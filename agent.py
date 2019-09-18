#!/usr/bin/python3
# In this program, the first step is exploring the positons that the anget can reach,
# then the agent start to search the path to gold position,
# if the agent can not reach the gold position and go back,
# then the agent start to collect resource, and re-search the path to gold and way back to initial position.

# algorithm:
# When searching for the path, the main algorithm used is greedy first search, the agent will calculate
# the manhattan distance from its postion to the destination, if the next position is closer to destination,
# then the agent is prefer to search this path first

# data structure:
# mainly use deque and list, when the next postion is closer to destination, appendleft, and
# search for this path first

import socket, sys
from collections import deque
from copy import deepcopy, copy


# this part is used to record the map, and display the map
class Map:
    def __init__(self):
        self.pos = [80, 80]
        self.facing = 'v'
        self.init_facing = 'v'
        self.game_map = [['?' for i in range(161)] for j in range(161)]
        self.game_map[80][80] = 'v'
        self.collection = {' ': [], 'a': [], 'o': [], 'T': [], 'k': []}
        self.num_of_moves = 0
        self.gold_positon = None

    def record_view(self, view):
        x = self.pos[0]
        y = self.pos[1]
        view = self.regular_view(view)
        ps = ([(x - 2, y - 2), (x - 2, y - 1), (x - 2, y), (x - 2, y + 1), (x - 2, y + 2)],
              [(x - 1, y - 2), (x - 1, y - 1), (x - 1, y), (x - 1, y + 1), (x - 1, y + 2)],
              [(x, y - 2), (x, y - 1), (x, y), (x, y + 1), (x, y + 2)],
              [(x + 1, y - 2), (x + 1, y - 1), (x + 1, y), (x + 1, y + 1), (x + 1, y + 2)],
              [(x + 2, y - 2), (x + 2, y - 1), (x + 2, y), (x + 2, y + 1), (x + 2, y + 2)])
        for i in range(5):
            for j in range(5):
                self.game_map[ps[i][j][0]][ps[i][j][1]] = view[i][j]
                if view[i][j] in self.collection:
                    self.collection[view[i][j]].append((ps[i][j][0], ps[i][j][1]))
                if view[i][j] in '$g':
                    self.gold_positon = list((ps[i][j][0], ps[i][j][1]))
        self.game_map[x][y] = self.facing

    # because the view get from server is according to the direction that the agent facing
    # so turn the view to correct direction
    def regular_view(self, view):
        if self.facing == 'v':  # 顺时针旋转180度
            v = list(map(list, zip(*view[::-1])))
            v = list(map(list, zip(*v[::-1])))
        if self.facing == '<':  # 逆时针旋转90度
            v = list(map(list, zip(*view)))[::-1]
        if self.facing == '>':  # 顺时针旋转90度
            v = list(map(list, zip(*view[::-1])))
        if self.facing == '^':
            return view
        return v

        # dispaly the current explored whole map
#     # def display_map(self):
        flag = True
        for i in range(161):
            if self.game_map[i].count('?') == 161:
                if not flag:
                    end_row = i
                    break
                continue
            else:
                if flag:
                    begin_row = i
                    flag = False
        right_rotation = list(map(list, zip(*self.game_map[::-1])))
        flag2 = True
        end_col = 161
        for i in range(161):
            if right_rotation[i].count('?') == 161:
                if not flag2:
                    end_col = i
                    break
                continue
            else:
                if flag2:
                    begin_col = i
                    flag2 = False
        for i in range(begin_row - 1, end_row + 1):
            print(''.join(self.game_map[i][begin_col - 1:end_col + 1]))


class Agent(Map):
    def __init__(self, port):
        super().__init__()
        self.pipe = Pipe(port)
        self.record_view(self.pipe.view)
        self.is_using_raft = False
        self.key = False
        self.axe = False
        self.get_gold = False
        self.stone = 0
        self.raft = 0
        self.doors = []
        self.treasure = None
        self.viable = {' ', 'k', 'o', 'O', 'a', '$', 'g'}
        self.arrivable = {}
        self.wait_for_collect = self.collection['k'] + self.collection['a'] + self.collection['o']
        self.water = []

    # this is the first step, the agent will collect all resources that it can get, and go to
    # all position it can go to without using stone or raft
    def begin_exploration(self):
        self.explored = []
        self.to_explore = deque()
        self.to_explore.append(self.pos)
        self.trees = []
        while self.to_explore:
            next_pos = self.to_explore.pop()
            suroundding = self.surrrounding(next_pos)
            for i in suroundding:
                if self.game_map[i[0]][i[1]] in self.viable and i not in self.explored:
                    if i not in self.to_explore:
                        self.to_explore.append(i)
                if self.game_map[i[0]][i[1]] == '-':
                    self.doors.append(i)
                if self.game_map[i[0]][i[1]] == 'T':
                    self.trees.append(i)
                if self.game_map[i[0]][i[1]] == '~':
                    if i not in self.water:
                        self.water.append(i)
            if next_pos in self.explored:
                continue
            self.explored.append(next_pos)
            path = self.path(self.pos, next_pos)
            if path:
                instructions = self.generate_instruction(path)
                self.send_instructions(path, instructions)

    # when the agent have explored the whole positions it can reach,
    # then it start try to get the gold and go back to initial position
    # firstly if the agent had got the gold when explore the map, then it go back to initial position directlly
    # then agent try to get the gold use only stone,
    # then use raft
    # if still can not get the gold, it start to collect resource
    # then go to fetch gold
    def start(self):
        if self.get_gold:
            path = self.path(self.pos, [80, 80])
            coms = self.generate_instruction(path)
            self.send_instructions(path, coms)
            # print(self.facing)
            self.turn_to_init_direction()
            # print(self.facing)
            return
        if self.gold_positon:
            #  only use stone
            gold_path = self.to_get_gold()
            if gold_path:
                gold_path.append([80, 80])
                for s in gold_path:
                    path = self.path(self.pos, s)
                    commands = self.generate_instruction(path)
                    self.send_instructions(path, commands)
                self.turn_to_init_direction()
                return
            else:
                # use raft try to get gold
                if self.raft:
                    copy_map = deepcopy(self.game_map)
                    gold_path = self.find_abs_path(self.pos, self.gold_positon, self.stone, self.raft, copy_map,
                                                   self.explored, self.water)
                    if gold_path:
                        map_for_back = deepcopy(gold_path[3])
                        inlet = self.find_inlet(self.gold_positon, map_for_back)
                        land = self.land(self.gold_positon, map_for_back)
                        way_back = self.find_abs_path(self.gold_positon, [80, 80], gold_path[0], gold_path[1],
                                                      map_for_back, land, inlet)
                        if way_back:
                            total_path = gold_path[6:] + way_back[6:]
                            for s in total_path:
                                path = self.path(self.pos, s)
                                coms = self.generate_instruction(path)
                                self.send_instructions(path, coms)
                            self.turn_to_init_direction()
                            return
                        else:
                            resource_can_collect = []
                            for i in range(len(self.game_map)):
                                for j in range(len(self.game_map)):
                                    if self.game_map[i][j] in 'okTa':
                                        resource_can_collect.append([i, j])
                            if len(resource_can_collect):
                                self.collect_resource(resource_can_collect[0])
                                inlet = self.find_inlet(self.pos, self.game_map)
                                for i in inlet:
                                    cur_land = self.land(self.pos, self.game_map)
                                    way_to_gold = self.find_abs_path(self.pos, self.gold_positon, self.stone,
                                                                     self.raft,
                                                                     self.game_map, cur_land, [i])
                                    cur_land = self.land(self.gold_positon, way_to_gold[3])
                                    inlet = self.find_inlet(self.gold_positon, way_to_gold[3])
                                    way_back = self.find_abs_path(self.gold_positon, [80, 80], way_to_gold[0],
                                                                  way_to_gold[1], way_to_gold[3], cur_land, inlet)
                                    if way_to_gold and way_back:
                                        for s in way_to_gold[6:] + way_back[6:]:
                                            path = self.path(self.pos, s)
                                            coms = self.generate_instruction(path)
                                            self.send_instructions(path, coms)
                                        self.turn_to_init_direction()
                                        return
                            else:
                                self.sailing()
                    else:
                        resource_can_collect = []
                        for i in range(len(self.game_map)):
                            for j in range(len(self.game_map)):
                                if self.game_map[i][j] in 'okTa':
                                    resource_can_collect.append([i, j])
                        if len(resource_can_collect):
                            self.collect_resource(resource_can_collect[0])
                        else:
                            self.sailing()
        else:
            self.sailing()
            resource_can_collect = []
            if not self.gold_positon:
                for i in range(len(self.game_map)):
                    for j in range(len(self.game_map)):
                        if self.game_map[i][j] in 'okTa':
                            resource_can_collect.append([i, j])
                if len(resource_can_collect):
                    self.collect_resource(resource_can_collect[0])
                    self.start()

    # used to send commands to the server, according to the path
    def send_instructions(self, path, instructions):
        index = 0
        for ins in instructions:
            if ins == 'f':
                if self.game_map[path[index + 1][0]][path[index + 1][1]] == 'k':
                    self.key = True
                    self.viable.add('-')
                    for i in self.doors:
                        self.to_explore.append(i)
                if self.game_map[path[index + 1][0]][path[index + 1][1]] == 'a':
                    self.axe = True
                    self.viable.add('T')
                    for t in self.trees:
                        self.to_explore.append(t)
                if self.game_map[path[index + 1][0]][path[index + 1][1]] == 'o':
                    self.stone += 1
                if self.game_map[path[index + 1][0]][path[index + 1][1]] in 'g$':
                    self.get_gold = True
                if self.game_map[path[index + 1][0]][path[index + 1][1]] == '~':
                    if self.stone:
                        self.stone -= 1
                    elif self.stone == 0 and self.raft > 0:
                        self.raft -= 1
                self.pos = path[index + 1]
                for item in self.surrrounding(self.pos):
                    if self.game_map[item[0]][item[1]] in self.viable and item not in self.explored:
                        self.to_explore.append(item)
                    if self.game_map[item[0]][item[1]] == 'T':
                        self.trees.append(item)
                self.explored.append(self.pos)
                self.pipe.send(ins)
                # self.display_map()
                self.record_view(self.pipe.view)
                index += 1
            elif ins == 'r':
                self.turning('r')
                self.pipe.send(ins)
                # self.display_map()
                self.record_view(self.pipe.view)
            elif ins == 'l':
                self.turning('l')
                self.pipe.send(ins)
                # self.display_map()
                self.record_view(self.pipe.view)
            elif ins == 'c':
                self.raft += 1
                self.pipe.send(ins)
                # self.display_map()
                self.record_view(self.pipe.view)
            elif ins == 'u':
                self.pipe.send(ins)
                # self.display_map()
                self.record_view(self.pipe.view)

    def land(self, pos, copy_map):
        explored = []
        nodes = [pos]
        while nodes:
            node = nodes.pop()
            if node not in explored:
                explored.append(node)
            for s in self.surrrounding(node):
                if copy_map[s[0]][s[1]] in self.viable:
                    if s not in explored and s not in nodes:
                        nodes.append(s)
        return explored

    def to_get_gold(self):
        stack = [i for i in self.water]
        distance_to_gold = self.distance(stack[-1], self.gold_positon)
        while stack:
            if self.stone:
                nub_of_stone = self.stone - 1
            else:
                return
            inlet = stack.pop()
            paths = deque([[nub_of_stone, inlet]])
            while paths:
                path = paths.popleft()
                if path[0] == 0:
                    for step in path[1:]:
                        for s in self.surrrounding(step):
                            if s == self.gold_positon:
                                return path[1:] + [s]
                            if s in self.explored or s in path:
                                continue
                            if self.game_map[s[0]][s[1]] == '~':
                                continue
                            elif self.game_map[s[0]][s[1]] in self.viable:
                                tmp = self.explore_space(s)
                                new_path = path + tmp[2]
                                new_path[0] += tmp[0]
                                if self.distance(new_path[-1], self.gold_positon) < distance_to_gold:
                                    paths.appendleft(new_path)
                                    distance_to_gold = self.distance(new_path[-1], self.gold_positon)
                                else:
                                    paths.append(new_path)
                else:
                    for step in path[1:]:
                        for s in self.surrrounding(step):
                            if s == self.gold_positon:
                                return path[1:] + [s]
                            if s in self.explored or s in path:
                                continue
                            if self.game_map[s[0]][s[1]] == '~':
                                new_path = path + [s]
                                new_path[0] -= 1
                                if self.distance(new_path[-1], self.gold_positon) < distance_to_gold:
                                    paths.appendleft(new_path)
                                    distance_to_gold = self.distance(new_path[-1], self.gold_positon)
                                else:
                                    paths.append(new_path)
                                if new_path[0] == 0:
                                    continue
                            elif self.game_map[s[0]][s[1]] in self.viable:
                                tmp = self.explore_space(s)
                                new_path = path + tmp[2]
                                new_path[0] += tmp[0]
                                if self.distance(new_path[-1], self.gold_positon) < distance_to_gold:
                                    paths.appendleft(new_path)
                                    distance_to_gold = self.distance(new_path[-1], self.gold_positon)
                                else:
                                    paths.append(new_path)
                    for s in self.water:
                        if s in self.explored or s in path:
                            continue
                        new_path = path + [s]
                        new_path[0] -= 1
                        if self.distance(new_path[-1], self.gold_positon) < distance_to_gold:
                            paths.appendleft(new_path)
                            distance_to_gold = self.distance(new_path[-1], self.gold_positon)
                        else:
                            paths.append(new_path)

    def explore_space(self, pos):
        path = [pos]
        l = deque([pos])
        num_stone = 0
        num_raft = 0
        if self.game_map[pos[0]][pos[1]] == 'o':
            num_stone += 1
        if self.game_map[pos[0]][pos[1]] == 'T':
            num_raft += 1
        while l:
            x = l.popleft()
            for s in self.surrrounding(x):
                if s not in path and self.game_map[s[0]][s[1]] in self.viable:
                    path.append(s)
                    if s not in l:
                        l.append(s)
                    if self.game_map[s[0]][s[1]] == 'o':
                        num_stone += 1
                    if self.game_map[s[0]][s[1]] == 'T':
                        num_raft += 1
        return num_stone, num_raft, path

    def turning(self, ins):
        d = {'^': ('>', '<'), '>': ('v', '^'), 'v': ('<', '>'), '<': ('^', 'v')}
        if ins == 'r':
            self.facing = d[self.facing][0]
        else:
            self.facing = d[self.facing][1]

    # this is used to search the path from pos to des
    # use manhatton distance as heuristic
    def path(self, pos, des):
        if pos == des:
            return
        path = [[pos]]
        while path:
            sub_path = path.pop()
            distance = self.distance(sub_path[-1], des)
            tmp = []
            for i in self.surrrounding(sub_path[-1]):
                if i in sub_path:
                    continue
                if i == des:
                    tmp.append(sub_path + [i])
                    return tmp[-1]
                if self.game_map[i[0]][i[1]] in self.viable:
                    if self.distance(i, des) == distance + 1:
                        path.append(sub_path + [i])
                    else:
                        tmp.append(sub_path + [i])
                        if i == des:
                            return tmp[-1]
                    if i == des:
                        return path[-1]
            for ele in tmp:
                path.append(ele)

    # calculate manhatton distace
    def distance(self, position, goal):
        return abs(position[0] - goal[0]) + abs(position[1] - goal[1])

    def surrrounding(self, pos):
        return [pos[0] - 1, pos[1]], [pos[0] + 1, pos[1]], [pos[0], pos[1] - 1], [pos[0], pos[1] + 1]

    def turn_to_init_direction(self):
        d = {'<': 'l', '>': 'r', '^': 'rr'}
        # print(self.facing)
        # print(self.init_facing)
        if self.facing == self.init_facing:
            return
        else:
            for ins in d[self.facing]:
                # print(ins)
                self.pipe.send(ins)

    # generate instructions according to the calculated path
    def generate_instruction(self, path):
        instruction = ''
        direction = self.facing
        for i in range(len(path) - 1):
            if self.north(path[i]) == path[i + 1]:
                if direction == '^':
                    instruction += 'f'
                elif direction == '>':
                    instruction += 'lf'
                elif direction == 'v':
                    instruction += 'rrf'
                elif direction == '<':
                    instruction += 'rf'
                direction = '^'
            elif self.sourth(path[i]) == path[i + 1]:
                if direction == '^':
                    instruction += 'rrf'
                elif direction == '>':
                    instruction += 'rf'
                elif direction == 'v':
                    instruction += 'f'
                elif direction == '<':
                    instruction += 'lf'
                direction = 'v'
            elif self.west(path[i]) == path[i + 1]:
                if direction == '^':
                    instruction += 'lf'
                elif direction == '>':
                    instruction += 'rrf'
                elif direction == 'v':
                    instruction += 'rf'
                elif direction == '<':
                    instruction += 'f'
                direction = '<'
            elif self.east(path[i]) == path[i + 1]:
                if direction == '^':
                    instruction += 'rf'
                elif direction == '>':
                    instruction += 'f'
                elif direction == 'v':
                    instruction += 'lf'
                elif direction == '<':
                    instruction += 'rrf'
                direction = '>'
            if self.game_map[path[i + 1][0]][path[i + 1][1]] == '-':
                instruction = instruction[:-1] + 'uf'
            elif self.game_map[path[i + 1][0]][path[i + 1][1]] == 'T':
                instruction = instruction[:-1] + 'cf'
        return instruction

    # this part is not used for explore the sea
    # whis program is not perfect, because when the agent dont know the gold posion
    # the agent need to explore more area, but i do not finish this part,
    # its too difficult for me now
    def sailing(self):
        inlet = self.find_inlet(self.pos, self.game_map)
        cur_inlet = inlet.pop()
        path = self.path(self.pos, cur_inlet)
        coms = self.generate_instruction(path)
        self.send_instructions(path, coms)
        explored = []
        to_explore = deque()
        to_explore.append(self.pos)
        while to_explore:
            node = to_explore.pop()
            for i in self.surrrounding(node):
                if self.game_map[i[0]][i[1]] in '~<>v^' and i not in explored:
                    if i not in to_explore:
                        to_explore.append(i)
            if node in explored:
                continue
            explored.append(node)
            path = self.sea_path(self.pos, node)
            if path:
                ins = self.generate_instruction(path)
                self.send_instructions(path, ins)

    def north(self, pos):
        return [pos[0] - 1, pos[1]]

    def sourth(self, pos):
        return [pos[0] + 1, pos[1]]

    def west(self, pos):
        return [pos[0], pos[1] - 1]

    def east(self, pos):
        return [pos[0], pos[1] + 1]

    def collect_resource(self, pos):
        My_map = deepcopy(self.game_map)
        for inlet in self.water:
            p = self.path_using_raft(inlet, pos, self.stone, self.raft, My_map)
            if p:
                for s in p[4:]:
                    sub_path = self.path(self.pos, s)
                    sub_com = self.generate_instruction(sub_path)
                    self.send_instructions(sub_path, sub_com)
                space = [pos]
                exploed = []
                path = [pos]
                while space:
                    next_pos = space.pop()
                    exploed.append(next_pos)
                    for s in self.surrrounding(next_pos):
                        if s not in exploed and self.game_map[s[0]][s[1]] in self.viable:
                            space.append(s)
                            if s not in path:
                                path.append(s)
                for s in path:
                    if s == self.pos:
                        continue
                    sub_path = self.path(self.pos, s)
                    sub_com = self.generate_instruction(sub_path)
                    self.send_instructions(sub_path, sub_com)

    # same path searching method , its just used for sea exploration
    def sea_path(self, pos, des):
        if pos == des:
            return
        nodes = deque([[pos]])
        distance = self.distance(pos, des)
        while nodes:
            node = nodes.popleft()
            for s in self.surrrounding(node[-1]):
                if s == des:
                    return node + [s]
                if s in node:
                    continue
                if self.game_map[s[0]][s[1]] == '~':
                    nodes.append(node + [s])
                    if self.distance(node[-1], des) < distance:
                        distance = self.distance(node[-1], des)
                        nodes.appendleft(node + [s])
                    else:
                        nodes.append(node + [s])

    # this part is used for searching path to an destination from initial position
    # given the number of stone, raft that the agent can use
    def find_abs_path(self, pos, des, rock, raft, copy_map, cur_land, inlet):
        distance = self.distance(pos, des)
        nodes = deque([[rock, raft, False, copy_map, cur_land, pos]])
        if des in cur_land:
            node = nodes.pop()
            return node + [des]
        for i in inlet:
            if rock > 0:
                new_map = deepcopy(copy_map)
                new_map[i[0]][i[1]] = 'O'
                new_node = [rock - 1, raft, False, new_map, cur_land, pos, i]
                if self.distance(i, des) < distance:
                    nodes.appendleft(new_node)
                else:
                    nodes.append(new_node)
            else:
                if raft > 0:
                    ext_land = deepcopy(cur_land)
                    new_map = deepcopy(copy_map)
                    new_node = [0, raft - 1, True, new_map, ext_land, pos, i]
                    if self.distance(i, des) < distance:
                        nodes.appendleft(new_node)
                    else:
                        nodes.append(new_node)
        while nodes:
            node = nodes.popleft()
            if node[0] < 0 or node[1] < 0:
                continue
            for s in self.surrrounding(node[-1]):
                if s == des:
                    return node + [s]
                if s in node[4]:
                    continue
                if node[3][s[0]][s[1]] == '*':
                    continue
                if s in node:
                    continue
                if node[2]:
                    if node[3][s[0]][s[1]] == '~':
                        new_node = deepcopy(node)
                        if self.distance(s, des) < distance:
                            distance = self.distance(s, des)
                            nodes.appendleft(new_node + [s])
                        else:
                            nodes.append(new_node + [s])
                    elif node[3][s[0]][s[1]] == 'o':
                        new_node = deepcopy(node)
                        new_node[3][s[0]][s[1]] = ' '
                        new_node[0] += 1
                        new_node[2] = False
                        if self.distance(s, des) < distance:
                            distance = self.distance(s, des)
                            nodes.appendleft(new_node + [s])
                        else:
                            nodes.append(new_node + [s])
                    elif node[3][s[0]][s[1]] == 'T':
                        new_node = deepcopy(node)
                        new_node[1] += 1
                        new_node[2] = False
                        node[3][s[0]][s[1]] = ' '
                        if self.distance(s, des) < distance:
                            distance = self.distance(s, des)
                            nodes.appendleft(new_node + [s])
                        else:
                            nodes.append(new_node + [s])
                    else:
                        new_node = deepcopy(node)
                        new_node[2] = False
                        if self.distance(s, des) < distance:
                            distance = self.distance(s, des)
                            nodes.appendleft(new_node + [s])
                        else:
                            nodes.append(new_node + [s])
                elif not node[2]:
                    if node[3][s[0]][s[1]] == '~':
                        if node[0] == 0 and node[1] == 0:
                            continue
                        if node[0] > 0:
                            new_node = deepcopy(node)
                            new_node[3][s[0]][s[1]] = 'O'
                            new_node[0] -= 1
                            if self.distance(s, des) < distance:
                                distance = self.distance(s, des)
                                nodes.appendleft(new_node + [s])
                            else:
                                nodes.append(new_node + [s])
                        else:
                            if node[1] > 0:
                                new_node = deepcopy(node)
                                new_node[2] = True
                                new_node[1] -= 1
                                if self.distance(s, des) < distance:
                                    distance = self.distance(s, des)
                                    nodes.appendleft(new_node + [s])
                                else:
                                    nodes.append(new_node + [s])
                    else:
                        if node[3][s[0]][s[1]] == 'o':
                            new_node = deepcopy(node)
                            new_node[0] += 1
                            new_node[3][s[0]][s[1]] = ' '
                            new_node.append(s)
                            nodes.appendleft(new_node)
                            inlet = self.find_inlet(new_node[-1], node[3])
                            for i in inlet:
                                cur_node = deepcopy(new_node)
                                cur_node[0] -= 1
                                cur_node[3][s[0]][s[1]] = ' '
                                cur_node.append(i)
                                nodes.append(cur_node)
                        elif node[3][s[0]][s[1]] == 'T':
                            new_node = deepcopy(node)
                            new_node[1] += 1
                            new_node[3][s[0]][s[1]] = ' '
                            new_node.append(s)
                            nodes.appendleft(new_node)
                        elif node[3][s[0]][s[1]] in self.viable:
                            new_node = deepcopy(node)
                            new_node.append(s)
                            nodes.appendleft(new_node)

    def find_inlet(self, pos, My_map):
        node = [pos]
        land = [pos]
        inlet = []
        while node:
            cur_node = node.pop()
            for s in self.surrrounding(cur_node):
                if My_map[s[0]][s[1]] in self.viable:
                    if s not in land and s not in node:
                        node.append(s)
                    if s not in land:
                        land.append(s)
                elif My_map[s[0]][s[1]] == '~':
                    if s not in inlet:
                        inlet.append(s)
        return inlet

    def path_using_raft(self, pos, des, num_stone, num_raft, My_map):
        distance = self.distance(pos, des)
        is_on_raft = False
        if My_map[pos[0]][pos[1]] == '~':
            if num_stone > 0:
                num_stone -= 1
            else:
                if num_raft > 0:
                    is_on_raft = True
                    num_raft -= 1
                else:
                    return
        paths = deque([[num_stone, num_raft, is_on_raft, My_map, pos]])
        if des not in self.explored:
            pass
        while paths:
            path = paths.popleft()
            if path[0] > 0:
                for s in self.surrrounding(path[-1]):
                    if s == des:
                        return path + [s]
                    if s not in self.explored and s not in path:
                        if path[3][s[0]][s[1]] == '~':
                            new_path = copy(path)
                            new_path[3][s[0]][s[1]] = 'O'
                            new_path[0] -= 1
                            if self.distance(s, des) < distance:
                                paths.appendleft(new_path + [s])
                            else:
                                paths.append(new_path + [s])
                        elif path[3][s[0]][s[1]] in self.viable:
                            if path[3][s[0]][s[1]] == 'o':
                                new_path = copy(path)
                                new_path[0] += 1
                                new_path[3][s[0]][s[1]] = ' '
                                if self.distance(s, des) < distance:
                                    distance = self.distance(s, des)
                                    paths.appendleft(new_path + [s])
                                else:
                                    paths.append(new_path + [s])
                            elif path[3][s[0]][s[1]] == 'T':
                                new_path = copy(path)
                                new_path[1] += 1
                                new_path[3][s[0]][s[1]] = ' '
                                if self.distance(s, des) < distance:
                                    distance = self.distance(s, des)
                                    paths.appendleft(new_path + [s])
                                else:
                                    paths.append(new_path + [s])
                            else:
                                new_path = copy(path)
                                if self.distance(s, des) < distance:
                                    distance = self.distance(s, des)
                                    paths.appendleft(new_path + [s])
                                else:
                                    paths.append(new_path + [s])
            elif path[0] == 0 and path[1] >= 0:
                for s in self.surrrounding(path[-1]):
                    if s == des:
                        return path + [s]
                    if s not in self.explored and s not in path:
                        if path[3][s[0]][s[1]] == '~' and not path[2]:
                            if path[1] == 0:
                                continue
                            else:
                                new_path = copy(path)
                                new_path[2] = True
                                new_path[1] -= 1
                            if self.distance(s, des) < distance:
                                distance = self.distance(s, des)
                                paths.appendleft(new_path + [s])
                            else:
                                paths.append(new_path + [s])
                        elif path[3][s[0]][s[1]] == '~' and path[2]:
                            new_path = copy(path)
                            if self.distance(s, des) < distance:
                                distance = self.distance(s, des)
                                paths.appendleft(new_path + [s])
                            else:
                                paths.append(new_path + [s])
                        elif path[3][s[0]][s[1]] in self.viable:
                            new_path = copy(path)
                            new_path[2] = False
                            if self.distance(s, des) < distance:
                                distance = self.distance(s, des)
                                paths.appendleft(new_path + [s])
                            else:
                                paths.append(new_path + [s])


# used for connect with the server
class Pipe:
    def __init__(self, port):
        self.port = port
        self.view = []
        self.connection()

    def connection(self):
        port = int(sys.argv[2])
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.sock.connect(('localhost', port))
        self.receiver()

    def receiver(self):
        d = b''
        while (True):
            d += self.sock.recv(1024)
            if len(d) == 24:
                nodelist = list(d.decode('utf-8'))
                tmpdata = nodelist[:12] + ['^'] + nodelist[12:]
                self.view = [tmpdata[5 * i:5 * i + 5] for i in range(5)]
                break

    def send(self, instruction):
        m = str.encode(instruction)
        self.sock.send(m)
        self.receiver()


if __name__ == '__main__':
    agent = Agent(31415)
    agent.begin_exploration()
    agent.start()
