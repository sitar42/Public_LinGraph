# **** ONE-directional lingraph which supports multiple resources in one node
# using MIP module in Python for constraint solver
from __future__ import absolute_import
from __future__ import division
from __future__ import print_function

from ortools.sat.python import cp_model

import time
import copy
# Node is a state node. value is the type of the node, label is a unique label
class Node:
    def __init__(self, value, label, count, copy=False):
        self.value = value
        self.label = label
        self.count = count
        self.copy = copy # copy flag: True if it is a copy node, otherwise False
        self.nextActions = [] # List of actions having this node as precondition [(A1, 2),(A2, 1),...] action and coefficient
        self.prevActions = [] # List of actions having this node as effect [(A1, 2),(A2, 1),...] action and coefficient

# count is the max possible action number
class Action:
    def __init__(self, value, label, count, copy=False):
        self.value = value
        self.label = label
        self.count = count
        self.copy = copy # True if the action is a Copy action, otherwise False
        self.effects = [] # List of effects nodes of the action, (N, coefficient)
        self.preconditions = [] # List of preconditions nodes of the action, (N, coefficient) 

# Given 2s1 + 1s2.. = 2s3 + 1s4 .. -> s1+s2 are prev_labels and rest labels are current_labels
# We also present s1 = 1 as writing numbers as string: '1'
class Constraint:
    def __init__(self, left_labels=[], right_labels=[]):
        self.left_labels = left_labels # [('s1', 1)] or [('a1', 2),('a2', 1),...]
        self.right_labels = right_labels # [('s1', 1)] or [('a1', 2),('a2', 1),...]
 #       self.prev_labels = prev_labels # only one label
 #       self.current_labels = current_labels # a list of labels
    # def add_current_labels(self, label):
    #     self.current_labels.append(label)

# Global variables
DEBUG_PRINT = False # True prints all debug print outs, False skips debug print outs
MAX_COUNT = 1000000 # Maximum number of an action count
LIMIT = 7 # max number of levels that the graph can reach
index_node_label = 0
index_action_label = 0
index_goal_label = 0
level_counter = 0 # stops extension of the graph when reaches LIMIT

actions = [] # holds given actions for planning
# Do we need left and right actions?
actions_left = [] # holds left actions (label, name, level)
actions_right = []
current_nodes_GL = [] # last level nodes for the left graph (from level1 to n)
current_nodes_GR = [] # last created level nodes for the right graph (from level n to 1)
constraints_GL = []
sibling_constraints_GL = []
constraints_GR = []
sibling_constraints_GR = []
# constraints = [] # holds all constraints ex: [C1, C2...] where C1 = (s1, [s2,s3,..]) or (s1, ['1']) or (s1, [s2])
initial_labels = [] # keeps labels for initial nodes, s1=1, s2=1 ..
goal_labels = [] # keeps labels for goal nodes, g1=1, g2=1 ..
variables_GL = [] # holds nodes and actions variables on the left graph
variables_GR = []
used_labels_GL = [] # holds only label of used nodes
used_variables_GL = [] # holds used nodes and count in the plan
used_labels_GR = [] # holds only label of used nodes
used_variables_GR = [] # holds used nodes and count in the plan

# **************** Auxiliary functions ****************
def reset_variables():
    global index_node_label
    global index_action_label
    global index_goal_label
    global level_counter
    global actions
    global actions_left
    global actions_right
    global current_nodes_GL
    global current_nodes_GR
    global constraints_GL
    global constraints_GR
    global initial_labels
    global goal_labels
    global variables_GL
    global variables_GR
    global sibling_constraints_GL
    global sibling_constraints_GR
    global used_labels_GL
    global used_variables_GL
    global used_labels_GR
    global used_variables_GR

    index_node_label = 0
    index_action_label = 0
    index_goal_label = 0
    level_counter = 0
    actions = []
    actions_left = []
    actions_right = []
    current_nodes_GL = []
    current_nodes_GR = []
    sibling_constraints_GL = []
    sibling_constraints_GR = []
    constraints_GL = []
    constraints_GR = []
    initial_labels = []
    goal_labels = []
    variables_GL = []
    variables_GR = []
    used_labels_GL = []
    used_variables_GL = []
    used_labels_GR = []
    used_variables_GR = [] 
    
def print_list(a_list):
    for item in a_list:
        print(item)

def print_nodes(node_list):
    for item in node_list:
        print('value:', item.value, '-label: ', item.label, '-count: ', item.count, '-Copy: ', item.copy)

def print_actions(action_list):
    for (item, coefficient) in action_list:
        print('Action value: ', item.value, ' - Action label: ', item.label, ' - coefficient: ', coefficient)

def print_constraints(constraints):
    for item in constraints:
        print('Constraint: ')
        for (left_label, count) in item.left_labels:
            print(count, left_label, ' + ')
        print(' ?=? ')
        for (right_label, count) in item.right_labels:
            print(count, right_label, ' + ')

def print_combinations(combinations):
    print('Combinations: ')
    for one_combination in combinations: # one_combination: [(N1, count), ..]
        print('One Combination:')
        for (node, count) in one_combination:
            print_nodes([node])
            print("Count: ", count)
                              
def print_combinations_dbg(combinations):
    if DEBUG_PRINT == True:
        print_combinations(combinations)

def print_variables(variables):
    for (variable, count) in variables:
        print("Variable: ", variable, " - count: ", count)

def  print_variables_dbg(variables):
    if DEBUG_PRINT == True:
        print_variables(variables)

def print_dbg(text):
    if DEBUG_PRINT == True:
        print(text)
 
def print_nodes_dbg(L):
    if DEBUG_PRINT == True:
        print_nodes(L)
   
def print_actions_dbg(L):
    if DEBUG_PRINT == True:
        print_actions(L)

def print_constraints_dbg(C):
    if DEBUG_PRINT == True:
        print_constraints(C)

def print_plan_actions(actions):
    for action_tuple in actions: # [(A1,count1),(A2,count2)]
        if action_tuple[0].copy == False: # if not a copy action
            print('Action value:', action_tuple[0].value, ' -- Action label: ', action_tuple[0].label, ' -- Action count: ', action_tuple[1])

def print_plan(plan): # plan is [[(A1,count1),(A2,count2)],[(A3,count3)],...]
    count = 0
    for actions in plan:
        count += 1
        print('Level-',count,' Actions:')
        print_plan_actions(actions)
        
# *****************************************************

# This function creates a unique node label
def create_node_label():
    global index_node_label
    index_node_label += 1
    return 's' + str(index_node_label)
    
# This function creates a unique action label
def create_action_label():
    global index_action_label
    index_action_label += 1
    return 'a' + str(index_action_label)

# This function creates a unique goal label
def create_goal_label():
    global index_goal_label
    index_goal_label += 1
    return 'g' + str(index_goal_label)

# Auxiliary function for creating nodes. (t,n) where t is the type and n is the count of the resource 
def aux_create_initial_nodes(state): # state[0] is t, state[1] is n
    global initial_labels
    new_label = create_node_label()
    initial_labels.append((new_label, state[1]))
    return Node(state[0], new_label, state[1])

# creates initial nodes from given list of resource types [a, b, ..]
def create_initial_nodes(initial_states):
    return list(map(aux_create_initial_nodes, initial_states))

# Auxiliary function for creating goal nodes 
def aux_create_goal_nodes(state):
    global goal_labels
    new_label = create_goal_label()
    # we do not assign anything to goals since we do not know yet
    goal_labels.append((new_label, state[1]))
    #constraints.append(new_constraint) # each resource (goal node count) is 1
    return Node(state[0], new_label, state[1])

# creates goal states from given list of goals [a, b, ..]
def create_goal_nodes(goal_states):
    return list(map(aux_create_goal_nodes, goal_states))

# extracts only the value part of each nodes
def extract_node_types(node_list):
    return list(map(lambda n: n.value, node_list))

# creates constraints for the given combination and solves together with the general constraints  
def solve_impaired_constraints(one_combination, graph_type):
    global variables_GL
    global variables_GR
    global initial_labels
    global goal_labels
    global constraints_GL
    global constraints_GR
    global sibling_constraints_GL
    global sibling_constraints_GR
    global current_nodes_GL
    global current_nodes_GR

    if graph_type == "left":
        # print_dbg("solve_impaired_constraints LEFT")
        variables = variables_GL
        labels = initial_labels
        constraints = constraints_GL
        sibling_constraints = sibling_constraints_GL
        current_nodes = current_nodes_GL
    else:
        # print_dbg("solve_impaired_constraints RIGHT")
        variables = variables_GR
        labels = goal_labels
        constraints = constraints_GR
        sibling_constraints = sibling_constraints_GR
        current_nodes = current_nodes_GR

    # Creates the model.
    model = cp_model.CpModel()
    
    # add initial variables, s1=2, s2=1..
    for (variable, count) in labels:
        # print('solve_constraints - Initial_labels - variable:', variable, ' - count:', count)
        expression = variable + ' = model.NewIntVar(' + str(count) + ', ' + str(count) + ', "' + variable + '")'
        exec(expression)
    # for variables adding rest of variables with their possible values, will be range(count+1) 
    for (variable, count) in variables:
        # print('solve_constraints - variables_GL - variable:', variable, ' - count:', count)
        expression = variable + ' = model.NewIntVar(0, ' + str(count) + ', "' + variable + '")'
        exec(expression)

    # Find non_zero_nodes, which are nodes in one_combination and their siblings
    non_zero_nodes = set()
    for (node, count) in one_combination:
        non_zero_nodes.add(node.label)
        expression = 'model.Add(' + node.label + ' >= ' + str(count) + ')'
        eval(expression)
        # add list of siblings of the node. prevAction is list of [(A1, coefficient)..]
        # (A, coefficientA) = node.prevActions[0] # there is only one prevAction for all nodes
        # for (N, coefficientN) in A.effects:
        #     non_zero_nodes.add(N.label) # effect is (N, coefficient)

    # print_dbg("solve_impaired_constraints: current nodes:")
    # print_nodes_dbg(current_nodes)
    # for node in current_nodes:
    #     # print('node in current_nodes:', node.label)
    #     if node.label in non_zero_nodes:
    #         print_dbg('node in non zero nodes:')
    #         print_dbg(node.label)
    #         problem.addConstraint(lambda x: x >= 1, [node.label])
    #     else: # node should be set to zero
    #         print_dbg('node in zero nodes:')
    #         print_dbg(node.label)
    #         problem.addConstraint(lambda x: x == 0, [node.label])

    # print_dbg("Sibling constraints in solve_impaired_constraints:")
    # print_constraints_dbg(sibling_constraints)
    for sibling_constraint in sibling_constraints:
        expression = '' # holds whole expression for adding constraints. eval('exp') evaluates the exp
        expression += 'model.Add('
        for node in sibling_constraint.left_labels: #[('s1', 2)]
            expression += str(node[1]) + '*' + node[0] + '+'
        expression = expression[:-1] # removes the last character '+'
        expression += '=='
        for action in sibling_constraint.right_labels: #[('s1', 2), ('s2', 1), ..]
            expression += str(action[1]) + '*' + action[0] + '+' # 2*s1 + 1*s2..
        expression = expression[:-1] # removes the last character '+'
        expression += ')'
        eval(expression) # evaluates the problem.addConstraint(..) string
    
    # print_dbg("Constraints in solve_impaired_constraints:")
    # print_constraints_dbg(constraints)
    for constraint in constraints:
        expression = '' # holds whole expression for adding constraints. eval('exp') evaluates the exp
        expression += 'model.Add('
        for node in constraint.left_labels: #[('s1', 2)]
            expression += str(node[1]) + '*' + node[0] + '+' # 2*s1
        expression = expression[:-1] # removes the last character '+'
        expression += '=='
        for action in constraint.right_labels: #[('s1', 2), ('s2', 1), ..]
            expression += str(action[1]) + '*' + action[0] + '+' # 2*s1 + 1*s2..
        expression = expression[:-1] # removes the last character '+'
        expression += ')'
        eval(expression) # evaluates the problem.addConstraint(..) string

    # Creates a solver and solves the model.
    solver = cp_model.CpSolver()
    status = solver.Solve(model)

    if status == cp_model.FEASIBLE or status == cp_model.OPTIMAL:
        return (solver, True)
        # #    print('x = %i' % solver.Value(x))
        # expression = 'solver.Value(x)'
        # print(eval(expression))
        # expression = 'solver.Value(y)'
        # print(eval(expression))
    else:
        return (solver, False)

# create constraints for google or-tools: CP-SAT solver and then solve them
# ?? we assume that goal_constraints and constraints are not empty
def solve_constraints(current_nodes_GL, current_nodes_GR, goal_constraints, conjunction, zero_labels):
    global variables_GL
    global variables_GR
    global initial_labels
    global goal_labels
    global constraints_GL
    global constraints_GR
    global sibling_constraints_GL
    global sibling_constraints_GR
    global used_labels_GL
    global used_variables_GL
    global used_labels_GR
    global used_variables_GR
    
    print("Beginning of solve_constraints - variables_GL: ", len(variables_GL), " - constraints_GL: ", len(constraints_GL), " - variables_GR: ", len(variables_GR), " - constraints_GR: ", len(constraints_GR), " - goal_constraints: ", len(goal_constraints), " - zero_constraints: ", len(zero_labels))
    print_variables_dbg(variables_GL)
    
    # Creates the model.
    model = cp_model.CpModel()
    
    # create initial variables, s1=2, s2=1..
    for (variable, count) in initial_labels:
        # print('solve_constraints - Initial_labels - variable:', variable, ' - count:', count)
        expression = variable + ' = model.NewIntVar(' + str(count) + ', ' + str(count) + ', "' + variable + '")'
        exec(expression)
        # create initial variables, s1=2, s2=1..
    for (variable, count) in goal_labels:
        # print('solve_constraints - goal_labels - variable:', variable, ' - count:', count)
        expression = variable + ' = model.NewIntVar(' + str(count) + ', ' + str(count) + ', "' + variable + '")'
        exec(expression)
    # for left variables adding rest of variables with their possible values, will be range(count+1) 
    for (variable, count) in variables_GL:
        # print('solve_constraints - variables_GL - variable:', variable, ' - count:', count)
        expression = variable + ' = model.NewIntVar(0, ' + str(count) + ', "' + variable + '")'
        exec(expression)
    # set possible values for right variables 
    for (variable, count) in variables_GR:
        # print('solve_constraints - variables_GR - variable:', variable, ' - count:', count)
        expression = variable + ' = model.NewIntVar(0, ' + str(count) + ', "' + variable + '")'
        exec(expression)
    # We assign zero to nodes that are in zero constraints list
    for variable in zero_labels:
        print_dbg('variable in zero_labels:')
        print_dbg(variable)
        expression = 'model.Add(' + variable + ' == 0)'
        eval(expression)

    print_dbg("Sibling constraints GL in solve_constraints:")
    print_constraints_dbg(sibling_constraints_GL)
    for sibling_constraint in sibling_constraints_GL:
        expression = '' # holds whole expression for adding constraints. eval('exp') evaluates the exp
        expression += 'model.Add('
        for node in sibling_constraint.left_labels: #[('s1', 2)]
            expression += str(node[1]) + '*' + node[0] + '+'
        expression = expression[:-1] # removes the last character '+'
        expression += '=='
        for action in sibling_constraint.right_labels: #[('s1', 2), ('s2', 1), ..]
            expression += str(action[1]) + '*' + action[0] + '+' # 2*s1 + 1*s2..
        expression = expression[:-1] # removes the last character '+'
        expression += ')'
        eval(expression) # evaluates the problem.addConstraint(..) string

    print_dbg("Sibling constraints GR in solve_constraints:")
    print_constraints_dbg(sibling_constraints_GR)
    for sibling_constraint in sibling_constraints_GR:
        expression = '' # holds whole expression for adding constraints. eval('exp') evaluates the exp
        expression += 'model.Add('
        for node in sibling_constraint.left_labels: #[('s1', 2)]
            expression += str(node[1]) + '*' + node[0] + '+'
        expression = expression[:-1] # removes the last character '+'
        expression += '=='
        for action in sibling_constraint.right_labels: #[('s1', 2), ('s2', 1), ..]
            expression += str(action[1]) + '*' + action[0] + '+' # 2*s1 + 1*s2..
        expression = expression[:-1] # removes the last character '+'
        expression += ')'
        eval(expression) # evaluates the problem.addConstraint(..) string

    for goal_constraint in goal_constraints:
        expression = '' # holds whole expression for adding constraints. eval('exp') evaluates the exp
        expression += 'model.Add('
        for node in goal_constraint.left_labels: #[('s1', 2)]
            expression += str(node[1]) + '*' + node[0] + '+' # 2*s1
        expression = expression[:-1] # removes the last character '+'
        expression += '=='
        for action in goal_constraint.right_labels: #[('s1', 2), ('s2', 1), ..]
            expression += str(action[1]) + '*' + action[0] + '+' # 2*s1 + 1*s2..
        expression = expression[:-1] # removes the last character '+'
        expression += ')'
        eval(expression) # evaluates the problem.addConstraint(..) string
 
    # add left constraints to the solver
    for constraint in constraints_GL:
        expression = '' # holds whole expression for adding constraints. eval('exp') evaluates the exp
        expression += 'model.Add('
        for node in constraint.left_labels: #[('s1', 2)]
            expression += str(node[1]) + '*' + node[0] + '+' # 2*s1
        expression = expression[:-1] # removes the last character '+'
        expression += '=='
        for action in constraint.right_labels: #[('s1', 2), ('s2', 1), ..]
            expression += str(action[1]) + '*' + action[0] + '+' # 2*s1 + 1*s2..
        expression = expression[:-1] # removes the last character '+'
        expression += ')'
        eval(expression) # evaluates the problem.addConstraint(..) string
        
       # add left constraints to the solver
    for constraint in constraints_GR:
        expression = '' # holds whole expression for adding constraints. eval('exp') evaluates the exp
        expression += 'model.Add('
        for node in constraint.left_labels: #[('s1', 2)]
            expression += str(node[1]) + '*' + node[0] + '+' # 2*s1
        expression = expression[:-1] # removes the last character '+'
        expression += '=='
        for action in constraint.right_labels: #[('s1', 2), ('s2', 1), ..]
            expression += str(action[1]) + '*' + action[0] + '+' # 2*s1 + 1*s2..
        expression = expression[:-1] # removes the last character '+'
        expression += ')'
        eval(expression) # evaluates the problem.addConstraint(..) string

    # Creates a solver and solves the model.
    solver = cp_model.CpSolver()
    status = solver.Solve(model)

    if status == cp_model.FEASIBLE or status == cp_model.OPTIMAL:
        # store solutions into global variables
        for (variable, count) in initial_labels:
            expression = 'solver.Value(' + variable + ')'
            node_used = eval(expression)
            if node_used > 0:
                used_labels_GL.append(variable)
                used_variables_GL.append((variable, node_used))
        for (variable, count) in goal_labels:
            expression = 'solver.Value(' + variable + ')'
            node_used = eval(expression)
            if node_used > 0:
                used_labels_GR.append(variable)
                used_variables_GR.append((variable, node_used))
        for (variable, count) in variables_GL:
            expression = 'solver.Value(' + variable + ')'
            node_used = eval(expression)
            if node_used > 0:
                used_labels_GL.append(variable)
                used_variables_GL.append((variable, node_used))
        for (variable, count) in variables_GR:
            expression = 'solver.Value(' + variable + ')'
            node_used = eval(expression)
            if node_used > 0:
                used_labels_GR.append(variable)
                used_variables_GR.append((variable, node_used))        
        return True
        # #    print('x = %i' % solver.Value(x))
        # expression = 'solver.Value(x)'
        # print(eval(expression))
        # expression = 'solver.Value(y)'
        # print(eval(expression))
    else:
        return False
    
    # after adding all constraints, we can find all solutions or one solution
    # solutions = problem.getSolutions()
#    return solver

# extract actions from left graph
def extract_left_plan(nodes, ret_actions):
    global used_labels_GL
    global used_variables_GL
    
    print_dbg('extract_left_plan - nodes:')
    print_nodes_dbg(nodes)
    #print_actions_dbg(ret_actions)
    if nodes == []:
        return ret_actions
    current_actions = []
    prev_nodes = []
    visited_action_nodes = set()
    dict_used = dict(used_variables_GL)
    for node in nodes:
        if node.label in used_labels_GL:
            print_dbg('extract_left_plan: if node.label in used_labels:')
            print_dbg(' - len(node.prevActions):')
            print_dbg(len(node.prevActions))
            # if node is not at the first level and not visited before
            if (node.label not in visited_action_nodes) and (len(node.prevActions) > 0):
                print_dbg('inside if (node.label not in visited_action_nodes. Printing node.prevActions')
                print_actions_dbg(node.prevActions)
                (prev_action, coefficientA) = node.prevActions[0]
                # print('prev_action: ', prev_action.label, ' - coefficientA: ', coefficientA)
                node_used = dict_used[node.label]
                current_actions.append((prev_action, node_used // coefficientA))# there is only 1 prevAction for each current_nodes_GL, [(A1, 2)]
                # current_actions.append((node.prevActions[0][0], node_used // node.prevActions[0][1]))# there is only 1 prevAction for each current_nodes_GL, [(A1, 2)]
                for node_tuple in prev_action.effects: # (N, coefficientN)
                    # print('effects tuple label: ', node_tuple[0].label)
                    visited_action_nodes.add(node_tuple[0].label)
                # visited_action_nodes += list(map(lambda x: x[0].label, node.prevActions[0][0].effects)) # there is only 1 prevAction for each current_nodes_GL, [(A1, 2)]. effect: (N, coefficient)
                for node_tuple in prev_action.preconditions: # (N, coefficientN)
                    # print('preconditions tuple label: ', node_tuple[0].label)
                    prev_nodes.append(node_tuple[0])
                # prev_nodes += list(map(lambda (N, coefficientN): N, node.prevActions[0][0].preconditions)) # there is only 1 prevAction for each current_nodes_GL, [(A1, 2)]. precondition: (N, coefficient)
                # # remove nodes in the list created by the same action
                # for n in node.prevActions[0].effects: # there is only 1 prevAction for each current_nodes_GL
                #     nodes.remove(n)
    if len(current_actions) > 0:
        print_dbg('current_actions: ')
        #print(current_actions)
        ret_actions = [current_actions] + ret_actions # adds list of current actions to all action list which is ex: [[A1,A2],[A3],..]
        # for (action, action_count) in current_actions: # extracts previous level nodes from actions
        #     prev_nodes += action.preconditions
    return extract_left_plan(prev_nodes, ret_actions)

# extract actions from right graph
#def extract_right_plan(nodes, ret_actions):

            
        
# for a in A:
#     print('a: ',a)
#     if a == 3:
#         b = A.pop()

# for key, value in solution.items():
#     print(key, value)
#     return True

# extracts a plan from solution list of nodes {"s1": "2", "s2":"0" ...} etc.
def extract_plan(current_nodes_GL, current_nodes_GR):
    left_actions = extract_left_plan(list(current_nodes_GL), [])
    #  right_actions = extract_right_plan(list(current_nodes_GR), [])
    #  print_plan(left_actions + right_actions)
    print_plan(left_actions)

# equalizes similar types of nodes at current_nodes_GL with current_nodes_GR
# and then creates new constraints from these equalities
# example: s5=g1, s6+s8=g3+g4..
def goal_check(current_nodes_GL, current_nodes_GR):
    visited_types = [] # accumulates visited node types
    zero_labels = [] # holds types that should be assigned to zero
    goal_constraints = []
    print_dbg('********** in GOAL_CHECK() *****')
    print_dbg('Current nodes GL:')
    print_nodes_dbg(current_nodes_GL)
    print_dbg('Current nodes GR:')
    print_nodes_dbg(current_nodes_GR)
    print_dbg('goal_constraints..')
    print_constraints_dbg(goal_constraints)
    # compare intersection of GL and GR, if it is empty there is no solution. Otherwise continue checking..
    conjunction = list(set(list(map(lambda gl_node: gl_node.value, current_nodes_GL))).intersection(list(map(lambda gr_node: gr_node.value, current_nodes_GR))))
    if conjunction == []:
        print_dbg('************* NO SOLUTION **************')
        return False
    else:
        for node_GL in current_nodes_GL:
            # if node_GL.value in visited_types:
            #     print_dbg('if node in visited_types')
            #     pass
            # else:
            if node_GL.value not in visited_types:
                print_dbg('goal_check: goal constraints before..')
                print_constraints_dbg(goal_constraints)
                left_constraints = list(map(lambda f_node: (f_node.label, 1), list(filter(lambda node: node.value == node_GL.value, current_nodes_GL))))
                right_constraints = list(map(lambda f_node2: (f_node2.label, 1), list(filter(lambda node2: node2.value == node_GL.value, current_nodes_GR))))
                # print_dbg('Left_constraints')
                # print_list(left_constraints)
                # print_dbg('Right_constraints')
                # print_list(right_constraints)
                if right_constraints == []:
                    print_dbg('node value is not in goal nodes')
                    zero_labels.append(node_GL.label)
                else:
                    goal_constraints.append(Constraint(left_constraints, right_constraints))
                visited_types.append(node_GL.value)
                print_dbg('goal constraints after..')
                print_constraints_dbg(goal_constraints)
                for node_GR in current_nodes_GR:
                    if node_GR.value not in conjunction:
                        # print_dbg('node_GR value is not in goal nodes. Zero constraint:')
                        # print_dbg(node_GL.label)
                        zero_labels.append(node_GR.label) # list of nodes that will be zero, (gi = 0)       
        # check constraints with a constraint solver
        isSolution = solve_constraints(current_nodes_GL, current_nodes_GR, goal_constraints, conjunction, zero_labels)
        print_dbg("End of solve_constraints..")
        if isSolution: # true if there is a solution
            print('************* FOUND A SOLUTION!')
            #TODO: Open below comment
            extract_plan(current_nodes_GL, current_nodes_GR)
            return True
        else:           
            print('************* NO SOLUTION!')
            return False

# returns True if the label is same with any node in the combination list
def is_node_in_list(label, combination):
    for node in combination:
        if label == node.label:
            return True
    return False # otherwise

# creates new actions and nodes using given precondition combinations for the action
# one_combination has (node, coefficient for the action) list as [(N1,n1), (N2,n2)]
def create_nodes_left(combinations, name, preconditions, effects):
    global MAX_COUNT
    global variables_GL
    global sibling_constraints_GL
    new_nodes = [] # holds new created recent nodes GL
    print_dbg('beginning function create_nodes_left..')
    print_dbg("create_nodes_left: combinations")
    print_combinations_dbg(combinations)
    for one_combination in combinations:
        # find action count
        action_count = MAX_COUNT
        new_action = Action(name, create_action_label(), action_count)
        for (node, coefficient) in one_combination:
            # print("create_nodes_left - label:",node.label,"value:",node.value,"node.count:",node.count,"coefficient:",coefficient)
            min_count = node.count // coefficient
            if (min_count < action_count):
                action_count = min_count
            node.nextActions.append((new_action, coefficient)) # adds action to nextActions list of the node
        new_action.count = action_count
        new_action.preconditions = new_action.preconditions + one_combination # adds precondition nodes of the action
        # new_action.preconditions.append(one_combination) # adds precondition nodes of the action
        # If s1,s2,s3 are sibling nodes, we create two constraints as s1=s2, s1=s3
        # for the first node s1
        (effect1,coefficient1) = effects[0] # first effect
        # print("effects[0]", effect1, "coefficient1:", coefficient1, "action_count:", action_count)
        first_effect_node = Node(effect1, create_node_label(), action_count * coefficient1) # creates the new effect node
        first_effect_node.prevActions.append((new_action, coefficient1)) # adds new action to previous action list of new node
        variables_GL.append((first_effect_node.label, first_effect_node.count)) # adds new label and count to variables list
        new_action.effects.append((first_effect_node, coefficient1)) # adds first effect node and coefficient of the action
        new_nodes.append(first_effect_node)
        for i in range(len(effects) - 1): # i from 0 to n-1, we add +1 to start from 1
            (effect,coefficient) = effects[i+1] # first effect
            # print("effects[i+1]", effect)
            effect_node = Node(effect, create_node_label(), action_count * coefficient) # creates the new effect node
            effect_node.prevActions.append((new_action, coefficient)) # adds new action to previous action list of new node
            variables_GL.append((effect_node.label, effect_node.count)) # adds new label to variables list
            new_action.effects.append((effect_node, coefficient)) # adds effect nodes of the action
            new_nodes.append(effect_node)
            sibling_constraints_GL.append(Constraint([(first_effect_node.label, coefficient)], [(effect_node.label, coefficient1)])) # if effects are s1:2 and s2:3, then sibling constraint is 3*s1=2*s2
    print_dbg('end of function create_nodes_left..')
    return new_nodes

# creates new actions and nodes using given effects combinations for the action.
# Since creating goes from right to left, process is in reverse order of 'from left to right'
# sibling constraint should be created for preconditions of an action(for create_nodes_left, it is for effects) 
def create_nodes_right(current_nodes_GR, combinations, name, preconditions, effects):
    temp_nodes = [] # holds new created recent nodes GR
    print_dbg('beginning function create_nodes_right..')
    global constraints
    global index_goal_label
    global variables
    for one_combination in combinations:
  #      combination_nodes = []
        new_action = Action(name, create_action_label())
        new_nodes = []
        #print('for one_combination:')
        for node in current_nodes_GR:
            #print('for node in current_nodes_GR')
            if is_node_in_list(node.label, one_combination):
                new_action.effects.append(node) # adds effect nodes of the action
  #              combination_nodes.append(node)
                node.prevActions.append(new_action) # adds action to prevActions list of the node               
        first_precondition_node = Node(preconditions[0], create_goal_label()) # creates the first precondition node g1
        first_precondition_node.nextActions.append(new_action) # adds new action to next action list of new node
        variables.append('g' + str(index_goal_label)) # adds new label to variables list
        new_action.preconditions.append(first_precondition_node) # adds first precondition node of the action
        temp_nodes.append(first_precondition_node)                
        for i in range(len(preconditions)):
            if i == 0: # if it is the first precondition do nothing
                pass
            else:
                precondition_node = Node(preconditions[i], create_goal_label()) # creates the new precondition node
                precondition_node.nextActions.append(new_action) # adds new action to next action list of new node
                variables.append('g' + str(index_goal_label)) # adds new label to variables list
                new_action.preconditions.append(precondition_node) # adds precondition nodes of the action
                temp_nodes.append(precondition_node)
                # If g1,g2,g3 are sibling nodes, we create two constraints as g1=g2, g1=g3    
                sibling_constraint = Constraint([first_precondition_node.label], [precondition_node.label])
                constraints.append(sibling_constraint)
    print_dbg('end of function create_nodes_right..')
    return temp_nodes

# returning new preconditions and count
def use_precondition(node, preconditions):
    new_preconditions = []
    count = 0
    for precondition in preconditions: # preconditions: [('type', count)..]
        if node.value == precondition[0]:
            if node.count >= precondition[1]:
                count = precondition[1]
            else:
                count = node.count
                new_preconditions.append((precondition[0], precondition[1] - count))
        else:
            new_preconditions.append(precondition)
    return (new_preconditions, count)

# finding all combinations for the given nodes that satisfy preconditions
# one combination is a list of [(node, count)..].  
def find_action_combinations(nodes, preconditions, effects, one_combination, combinations):
    if len(preconditions) > 0:
        if len(nodes) > 0:
            node = nodes.pop()
            temp_preconditions = preconditions
            (new_preconditions, count) = use_precondition(node, preconditions)
            # print_dbg("find_action_combinations - count: ")
            # print_dbg(count)
            if count == 0: # no match of preconditions with the given node
                # print_dbg("before find_action_combinations-2: ")
                new_combinations2 = find_action_combinations(nodes, preconditions, effects, one_combination, combinations)
                # print_dbg("find_action_combinations-2: ")
                # print_combinations_dbg(new_combinations2)
                return new_combinations2
            else:
                temp_nodes = list(nodes)
                temp_new_preconditions = list(new_preconditions)
                temp_one_combination = list(one_combination)
                one_combination.append((node, count))
                # print_dbg("before find_action_combinations-3: ")
                new_combinations3 = find_action_combinations(nodes, new_preconditions, effects, one_combination, combinations)
                # print_dbg("find_action_combinations-3: ")
                # print_combinations_dbg(new_combinations3)
                k = count - 1 # decreasing used node count 1 to find other combinations
                if k == 0:
                    # print_dbg("before find_action_combinations-4: ")
                    new_combinations4 = find_action_combinations(temp_nodes, temp_preconditions, effects, temp_one_combination, new_combinations3)
                    # print_dbg("find_action_combinations-4: ")
                    # print_combinations_dbg(new_combinations4)
                    return new_combinations4
                else:
                    new_node = copy.deepcopy(node)
                    new_node.count = k
                    temp_nodes.append(new_node)
                    # print_dbg("before find_action_combinations-5: ")
                    new_combinations5 = find_action_combinations(temp_nodes, temp_preconditions, effects, temp_one_combination, new_combinations3)
                    # print_dbg("find_action_combinations-5: ")
                    # print_combinations_dbg(new_combinations5)
                    return new_combinations5
                #    print('new_combinations2:')
                #    print_combinations(new_combinations2)
        else: # temp_nodes is empty
            #print('else combinations:')
            #print_combinations(combinations)
            return combinations
    else: # the list of preconditions is empty
        # If all nodes of a combination are copy nodes, then we should remove that combination
        # If all nodes in the combination are sibling and the combination is precondition of a symmetric action, then we should remove that combination
        copy_flag = True
        sibling_flag = True
        action_label = ""
        for (node, count) in one_combination:
            if node.copy == False: # at least one node is not a copy node
                copy_flag = False
            # check if all preconditions are siblings
            if node.prevActions == []: # if the n node is at the first level, no need to sibling check
                sibling_flag = False
                break
            else:
                (prevAction, coefficientA) = node.prevActions[0]
                if action_label == "":
                    #print("n.value", n.value)
                    #print("n.label", n.label)
                    #print("prevAction", n.prevActions)
                    #print("nextAction", n.nextActions)
                    action_label = prevAction.label
                if action_label != prevAction.label: # if at least one action is different, they are not siblings 
                    sibling_flag = False
                action_label = prevAction.label              
        # if at least one node in the combination is not copy node, then we can add this combination
        if (copy_flag == False):
            if (sibling_flag == False): # if preconditions are not sibling, we add the combination
                return ([one_combination] + combinations)
            else: # if preconditions are siblings, we check if it is not a symmetric action
                (node, count) = one_combination[0]
                (prevAction, coefficientA) = node.prevActions[0]
                if len(prevAction.preconditions) == len(effects): # a candidate for a symmetric action
                    new_effect_values = list(map(lambda effect_tuple: effect_tuple[0], effects))
                    for (prevAction_precondition, coefficient) in prevAction.preconditions:
                        if prevAction_precondition.value in new_effect_values:
                            new_effect_values.remove(prevAction_precondition.value)
                        else:
                            return ([one_combination] + combinations)
                    return combinations
                else: # not a symmetric action
                    return ([one_combination] + combinations)                
        else:
            return combinations


# ############### OLD version is below: for single number of nodes #################    
#     if len(preconditions) > 0:
#         if len(nodes) > 0:
#             node = nodes.pop()
#             #print('node: ', node.value)
#             if node.value in preconditions:
#             #    print('node in preconditions')
#                 temp_preconditions = list(preconditions)
#                 temp_one_combination = list(one_combination)
#                 temp_nodes = list(nodes)
#                 preconditions.remove(node.value)
#                 one_combination.append(node)
#             #    print('one_combination:' )
#             #    print_nodes(one_combination)
#                 new_combinations = find_action_combinations(nodes, preconditions, effects, one_combination, combinations)
#             #    print('new_combinations:')
#             #    print_combinations(new_combinations)
#                 last_combinations = find_action_combinations(temp_nodes, temp_preconditions, effects, temp_one_combination, new_combinations)
#             #    print('last_combinations:')
#             #    print_combinations(last_combinations)
#                 return last_combinations
#             else:
#                 new_combinations2 = find_action_combinations(nodes, preconditions, effects, one_combination, combinations)
#             #    print('new_combinations2:')
#             #    print_combinations(new_combinations2)
#                 return new_combinations2
#         else: # temp_nodes is empty
#             #print('else combinations:')
#             #print_combinations(combinations)
#             return combinations
#     else: # the list of preconditions is empty
#         # If all nodes of a combination are copy nodes, then we should remove that combination
#         # If all nodes in the combination are sibling and the combination is precondition of a symmetric action, then we should remove that combination
#         copy_flag = True
#         sibling_flag = True
#         action_label = ""
#         for n in one_combination:
#             if n.copy == False: # at least one node is not a copy node
#                 copy_flag = False
#             # check if all preconditions are siblings
#             if n.prevActions == []: # if the n node is at the first level, no need to sibling check
#                 sibling_flag = False
#                 break
#             else:
#                 if action_label == "":
#                     #print("n.value", n.value)
#                     #print("n.label", n.label)
#                     #print("prevAction", n.prevActions)
#                     #print("nextAction", n.nextActions)
#                     action_label = n.prevActions[0].label
#                 if action_label != n.prevActions[0].label: # if at least one action is different, they are not siblings 
#                     sibling_flag = False
#                 action_label = n.prevActions[0].label              
#         # if at least one node in the combination is not copy node, then we can add this combination
#         if (copy_flag == False):
#             if (sibling_flag == False): # if preconditions are not sibling, we add the combination
#                 return ([one_combination] + combinations)
#             else: # if preconditions are siblings, we check if it is not a symmetric action
#                 for prevAction_precondition in one_combination[0].prevActions[0].preconditions:
#                    if prevAction_precondition.value in effects:
#                        effects.remove(prevAction_precondition.value)
#                    else:
#                        return ([one_combination] + combinations)
#                 return combinations
#         else:
#             return combinations
# ################## Old Version end ##############
        
# This function checks if a combination satisfies or not for all created constraints.
# If can not satisfy, we delete that combination.
def delete_impaired_combinations(combinations, graph_type):
    new_combinations = []
    for one_combination in combinations:
        # check constraints with a constraint solver
        (solver, isSolution) = solve_impaired_constraints(one_combination, graph_type)
        if isSolution: # true if there is a solution
            print_dbg('************* A SOLUTION for impaired constraints!')
            new_combinations.append(one_combination)
        else:
            print_dbg('************* NO SOLUTION for impaired constraints!')
    return new_combinations
    
# expand graph from left.
def expand_from_left(actions):
    global current_nodes_GL
    global variables_GL
    global initial_labels
    global actions_left
    global level_counter
    print_dbg('>>>>>> Expanding from left >>>>>>')
    print_dbg('level_counter in expand_from_left: ')
    print_dbg(level_counter)
    new_current_nodes = []
    created_actions = []
    print('Number of current left level nodes: ')
    print(len(current_nodes_GL))
    print_dbg('Current Nodes: ')
    print_nodes_dbg(current_nodes_GL)

    # combination_count = 0
    combinations_all = []
    not_copy_list = []
    for name, preconditions, effects in actions:
        print_dbg('Action: ')
        print_dbg(name)
        temp_nodes = list(current_nodes_GL)
        # temp_nodes = list(filter(lambda x: x.value in preconditions, current_nodes_GL))
        temp_preconditions = list(preconditions)
        temp_effects = list(effects)
        non_zero_nodes = set() # keeps non zero node labels
        combinations = find_action_combinations(temp_nodes, temp_preconditions, temp_effects, [], []) # returned combinations without copy nodes and symmetric actions
        print_dbg('Returned Combinations from Left find action combinations:')
        print_combinations_dbg(combinations)
        # delete impaired combinations
        if level_counter > 1: # We don't need to check and delete first level nodes
            combinations = delete_impaired_combinations(combinations, "left")
        if len(combinations) > 0:
            print_dbg('Combinations from Left after delete_impaired_combinations:')
            print_combinations_dbg(combinations)
            combinations_all = combinations + combinations_all
            # combination_count = combination_count + len(combinations)
            new_nodes = create_nodes_left(combinations, name, preconditions, effects)
            print_dbg("expand_from_left - new_nodes:")
            print_nodes_dbg(new_nodes)
            new_current_nodes = new_current_nodes + new_nodes
    print_dbg("expand_from_left: All Action combinations are tried!")
    # if there is only one action applicable, then we don't copy preconditions of this action to the next level
    # if combination_count == 1:
    #     not_copy_list = list(map(lambda n: n.label, combinations_all[0]))
    # copy current nodes to next level and creates actions
    # creates copy nodes and actions
    for node in current_nodes_GL:
        # if node.label not in not_copy_list: # copy a node if not in the one combination list
        copy_action = Action('Copy', create_action_label(), node.count, True)
        copy_action.preconditions.append((node, 1)) # All copy actions have a coefficient 1 for copied nodes
        node.nextActions.append((copy_action, 1))

        if len(node.nextActions) > 1: # if a node has other actions, not only a copy action
            copy_node = Node(node.value, create_node_label(), node.count, True)
            # Also add copy node and count into the global variables_GL as (n1, count1)
            variables_GL.append((copy_node.label, copy_node.count))
        else: # if a node has only a copy action, then it's label is same with previous copied node
            copy_node = Node(node.value, node.label, node.count, True)
        copy_node.prevActions.append((copy_action, 1)) # adds new action to previous action list of new node
        copy_action.effects.append((copy_node, 1)) # All copy actions have a coefficient 1 for copied nodes
        new_current_nodes.append(copy_node)
    level_counter += 1
    print('Number of New level left nodes: ')
    print(len(new_current_nodes))
    print_dbg('New level nodes: ')
    print_nodes_dbg(new_current_nodes)
    current_nodes_GL = new_current_nodes
    return (current_nodes_GL, True)

# # expand graph from right
# def expand_from_right(current_nodes_GR, constraints, actions, LIMIT):
#     print_dbg('<<<<<<<<<<<< Expanding from right <<<<<<<<<<<<')
#     global level_counter
#     global variables
#     global index_goal_label
#     print_dbg('level_counter in expand_from_right: ')
#     print_dbg(level_counter)
#     new_current_nodes = []
#     print('Number of current right level goals: ')
#     print(len(current_nodes_GR))
#     print_dbg('Goals: ')
#     print_nodes_dbg(current_nodes_GR)
#     # if level_counter < LIMIT:
#     for name, preconditions, effects in actions:
#         print_dbg('Action: ')
#         print_dbg(name)
#         temp_nodes = list(filter(lambda x: x.value in effects, current_nodes_GR))
#         temp_effects = list(effects)
#         combinations = find_action_combinations(temp_nodes, temp_effects, [], [])
#         print_dbg('Combinations from right')
#         print_combinations(combinations)
#         new_nodes = create_nodes_right(current_nodes_GR, combinations, name, preconditions, effects)
#         new_current_nodes = new_current_nodes + new_nodes
#     # copy current nodes to next level and creates actions
#     # creates copy nodes and actions
#     for node in current_nodes_GR:
#         copy_action = Action('Copy', create_action_label(), True)
#         copy_action.effects.append(node)
#         node.prevActions.append(copy_action)
#         copy_node = Node(node.value, create_goal_label(), True)
#         copy_node.nextActions.append(copy_action) # adds new action to next action list of new node
#         variables.append('g' + str(index_goal_label)) # adds new label to variables list
#         copy_action.preconditions.append(copy_node)
#         new_current_nodes = new_current_nodes + [copy_node]
#     level_counter += 1
#     print('Number of New level right nodes: ')
#     print(len(new_current_nodes))
#     print_dbg('New level nodes: ')
#     print_nodes_dbg(new_current_nodes)
#     current_nodes_GR = new_current_nodes
#     return current_nodes_GR
#     # else:
#     #     print('******** LIMIT IS EXCEEDED! *************')
#     #     return current_nodes_GR

# returns list for a given action's dependencies
def aux_extract_dependency_left(action_tuple):
    if action_tuple[0].copy == True: # if copy action
        (N, coefficient) = action_tuple[0].effects[0] # we know there is only one copied node in effects
        if N.copy == True: # if N is a copy node, return node label, otherwise return action label
            return (N.label, 1)
        else:
            return (action_tuple[0].label, action_tuple[1])
    else:
        return (action_tuple[0].label, action_tuple[1])
        
# create left constraints for current and previous level nodes. 'nodes' is a list of previous nodes  
def create_constraints_left(prev_nodes):
    global constraints_GL
    global sibling_constraints_GL
    print_dbg('Creating constraints Left:')
    print_constraints_dbg(constraints_GL)
    print_dbg('prev_nodes')
    print_nodes_dbg(prev_nodes)
    for node in prev_nodes:
        # creates constraints for next actions of the previous nodes s1 = 2*s2 + 1*a2...
        # if a node has only a copy action, do not create a constraint for it. Its label is same with the copied previous label
        if len(node.nextActions) > 1:
            multiplier = 1
            first_right_labels = []
            for tupleA in node.nextActions: # tupleA: (A, coefficientA)
                (N, coefficientN) = tupleA[0].effects[0]
                first_right_labels.append((tupleA[1], coefficientN, N.label))
                # print("first_right_labels:", tupleA[1], coefficientN, N.label)
                multiplier = multiplier * coefficientN
            right_labels = []
            for (coefficientA, coefficientN, label) in first_right_labels:
                right_labels.append((label, (multiplier // coefficientN) * coefficientA))
                # print("right_labels:", label)
            constraints_GL.append(Constraint([(node.label, multiplier)], right_labels))
    print_dbg('After creating Constraints:')
    print_constraints_dbg(constraints_GL)

# create right constraints for goal and next level nodes from last goal. 'nodes' is a list of goal nodes  
def create_constraints_right(nodes):
    print_dbg('Creating constraints:')
    global constraints
    print_constraints_dbg(constraints)
    for node in nodes:
        constraints.append(Constraint([node.label], list(map(lambda action: action.preconditions[0].label, node.prevActions))))
    print_dbg('After creating Constraints:')
    print_constraints_dbg(constraints)

# expand graph first left to right + goal check, and then right to left + goal check, respectively until find a plan..
def expand_graph(actions):
    global current_nodes_GL
    global current_nodes_GR
    global LIMIT
    global level_counter
    if level_counter >= LIMIT:
        print_dbg('LIMIT reached1 !')
        return False
    if actions == []:
        print_dbg('Actions list is EMPTY!!')
        return False
    temp_nodes_GL = list(current_nodes_GL)
    (current_nodes_GL, is_expanded_GL) = expand_from_left(actions)
   # if (is_expanded_GL == False): # left graph could not be expanded, we try expanding right
   #      print('Left Graph can not be expanded anymore') # try right
   #      if level_counter >= LIMIT:
   #          print('LIMIT reached2 !')
   #          return False
   #      temp_nodes_GR = list(current_nodes_GR)
   #      (current_nodes_GR, is_expanded_GR) = expand_from_right(current_nodes_GR, actions, LIMIT)
   #      if (is_expanded_GR == False): # right graph could not be expanded, we need to finish expanding here
   #          print('Right Graph can not be expanded') # try right
   #          return False
   #      create_constraints_right(temp_nodes_GR, current_nodes_GR)
   #      if goal_check(current_nodes_GL, current_nodes_GR):
   #          print_dbg('FOUND A PLAN2!')
   #          return True
   #      else:
   #          return expand_graph(current_nodes_GL, current_nodes_GR, actions)
    print_dbg('temp_nodes_GL:')
    print_nodes_dbg(temp_nodes_GL)
    print_dbg('current_nodes_GL:')
    print_nodes_dbg(current_nodes_GL)
 #   print("Current Nodes GL: ")
 #   print_nodes(current_nodes_GL)
    create_constraints_left(temp_nodes_GL) # temp_nodes_GL holds previous level nodes
    if goal_check(current_nodes_GL, current_nodes_GR):
        print_dbg('FOUND A PLAN!')
        return True
    else:
        # if level_counter >= LIMIT:
        #     print('LIMIT reached3 !')
        #     return False
        #  temp_nodes_GR = list(current_nodes_GR)
        # (current_nodes_GR, is_expanded_GR) = expand_from_right(current_nodes_GR, actions, LIMIT)
        # if (is_expanded_GR == False): # right graph could not be expanded, we need to finish expanding here
        #     print('Right Graph can not be expanded2') # try right
        #     return False
        # create_constraints_right(temp_nodes_GR, current_nodes_GR)
        # if goal_check(current_nodes_GL, current_nodes_GR):
        #     print_dbg('FOUND A PLAN3!')
        #     return True
        # else:
        #   return expand_graph(current_nodes_GL, current_nodes_GR, actions)
        return expand_graph(actions)
        
 # checks if the GR list is matching with the GL list
def is_match(GR, GL):
    if (GR == []) and (GL == []):
         return True
    else:
        try:
            flag = False
            new_list = []
            node_r = GR.pop()
            for node_l in GL:
                if (node_r.value == node_l.value) and (node_r.count == node_l.count):
                    flag = True
                    GL.remove(node_l)
                    new_list = new_list + GL
                    break
                else:
                    new_list.append(node_l)
                    GL.remove(node_l)
            if flag == True:
                return is_match(GR, new_list)
            else: # no match with type or count
                return False
        except:
            print_dbg('Error!!!')
            return False   

# findPlan(initial_states, goal_states, actions)
# It returns a plan if exists, otherwise an empty list []
# Each node is in the form of (t, l, n) where t is type, l is a unique label and n is the number of resources
# initial_states: list of resources as [('a', 2), ('b', 1), ('c', 1)],
# goal_states: list of goals as [('c', 1), ('d', 1)],
# actions: list of action tuples as [('name', [preconditions], [effects]), (..), ..]
def find_plan(initial_states, goal_states, input_actions):
    global current_nodes_GL
    global current_nodes_GR
    global actions
    global level_counter
    actions = input_actions
    current_nodes_GL = create_initial_nodes(initial_states)
    print_dbg('Printing Initial Nodes:')
    print_nodes_dbg(current_nodes_GL)
    level_counter += 1
    current_nodes_GR = create_goal_nodes(goal_states)
    print_dbg('Printing Goal Nodes:')
    print_nodes_dbg(current_nodes_GR)
    temp_nodes_GL = list(current_nodes_GL)
    temp_nodes_GR = list(current_nodes_GR)
    if is_match(temp_nodes_GR, temp_nodes_GL):
        print_dbg('PROVED THE GOAL AT THE FIRST LEVEL!')
        return True
    else:
        print_dbg('***************** Extending graph! ---  CURRENT LEVEL: ')
        print_dbg(level_counter)
        return expand_graph(actions)

# proves goal G from initial states I using actions A. flag is expected result of prove.
def prove(I, G, A, flag):
    start_time = time.time()
    print_dbg('-------- Starting to prove a new GOAL! ---------')
    reset_variables()
    if (find_plan(I, G, A) == flag):
        if flag == True:
            print('I:', I, 'G:', G, 'proved!', "--- %s seconds" % (time.time() - start_time))
        else:
            print('I:', I, 'G:', G, 'proved! (no solution)', "--- %s seconds" % (time.time() - start_time))
    else:
         print('I:', I, 'G:', G, ' <<-- FAILED PROOF! -->> ', 'returned:', not flag, "--- %s seconds" % (time.time() - start_time))
    
def unit_test():
    # prove([('a', 1)],[('a', 1)],[],True)
    # prove([('a', 1)],[('a', 2)],[],False)
    # prove([('a', 2)],[('a', 1)],[],False)
    # prove([('a',1),('b',1)],[('b',1),('a',1)],[],True)
    # prove([('a',1)],[('c',1)],[('A->C',[('a',1)],[('c',1)])],True)
    # prove([('a',1),('b',1)],[('c',1),('b',1)],[('A->C',[('a',1)],[('c',1)])],True)
    # prove([('a',1),('b',1)],[('c',1),('d',1)],[('AB->CD',[('a',1),('b',1)],[('c',1),('d',1)])],True)
    # prove([('a',1),('b',1)],[('c',1),('d',1)],[('AB->C',[('a',1),('b',1)],[('c',1)])], False)
    # prove([('a',1)],[('b',1),('c',1)],[('A->B',[('a',1)],[('b',1)])],False)

    # # Multiple resources
    # prove([('a',5)],[('a',5)],[], True)
    # prove([('g',2)], [('b',1), ('c',1)],[('G->A2',[('g',1)],[('a',2)]), ('A2->B',[('a',2)],[('b',1)]), ('A->C',[('a',1)],[('c',1)])],False)
    # prove([('g',2)], [('b',1), ('c',1), ('d',1)],[('G->A2',[('g',1)],[('a',2)]), ('A2->B',[('a',2)],[('b',1)]), ('A->C',[('a',1)],[('c',1)]), ('A->D',[('a',1)],[('d',1)])],True)
    # prove([('a',4),('b',2)], [('c',2)],[('2AB->C',[('a',2),('b',1)],[('c',1)])],True)
    # prove([('b',1),('c',1),('a',1)], [('b',1),('c',2)], [('A->C',[('a',1)],[('c',1)])],True)

    # # Real World planning problems
    # # Assembly line planning:
    # prove([('C1',4),('M',2)], [('S1',2),('M',2)], [('C1M->S1M',[('C1',2),('M',1)],[('S1',1),('M',1)])],True)
    # prove([('C1',1),('C2',1),('M',1)], [('P',1),('M',1)], [('C1M->S1M',[('C1',1),('M',1)],[('S1',1),('M',1)]),('C2M->S2M',[('C2',1),('M',1)],[('S2',1),('M',1)]),('S1S2M->PM',[('S1',1),('S2',1),('M',1)],[('P',1),('M',1)])],True)
    # prove([('C1',2),('C2',2),('M',2)], [('P',2),('M',2)], [('C1M->S1M',[('C1',1),('M',1)],[('S1',1),('M',1)]),('C2M->S2M',[('C2',1),('M',1)],[('S2',1),('M',1)]),('S1S2M->PM',[('S1',1),('S2',1),('M',1)],[('P',1),('M',1)])],True)
    # prove([('C1',2),('S2',2),('M',2)], [('P',2),('M',2)], [('C1M->S1M',[('C1',1),('M',1)],[('S1',1),('M',1)]),('C2M->S2M',[('C2',1),('M',1)],[('S2',1),('M',1)]),('S1S2M->PM',[('S1',1),('S2',1),('M',1)],[('P',1),('M',1)])],True)

    # prove([('C1',36),('C2',36),('M',48)], [('P',36),('M',48)], [('C1M->S1M',[('C1',1),('M',1)],[('S1',1),('M',1)]),('C2M->S2M',[('C2',1),('M',1)],[('S2',1),('M',1)]),('S1S2M->PM',[('S1',1),('S2',1),('M',1)],[('P',1),('M',1)])],True)
     # prove([('C1',32),('C2',32),('M',48)], [('P',32),('M',48)], [('C1M->S1M',[('C1',1),('M',1)],[('S1',1),('M',1)]),('C2M->S2M',[('C2',1),('M',1)],[('S2',1),('M',1)]),('S1S2M->PM',[('S1',1),('S2',1),('M',1)],[('P',1),('M',1)])],True)
    # prove([('C1',8),('C2',8),('M',16)], [('P',8),('M',16)], [('C1M->S1M',[('C1',1),('M',1)],[('S1',1),('M',1)]),('C2M->S2M',[('C2',1),('M',1)],[('S2',1),('M',1)]),('S1S2M->PM',[('S1',1),('S2',1),('M',1)],[('P',1),('M',1)])],True)
    # prove([('C1',32),('C2',32),('M',64)], [('P',32),('M',64)], [('C1M->S1M',[('C1',1),('M',1)],[('S1',1),('M',1)]),('C2M->S2M',[('C2',1),('M',1)],[('S2',1),('M',1)]),('S1S2M->PM',[('S1',1),('S2',1),('M',1)],[('P',1),('M',1)])],True)
    prove([('C1',5),('C2',5),('M',8)], [('P',5),('M',8)], [('C1M->S1M',[('C1',1),('M',1)],[('S1',1),('M',1)]),('C2M->S2M',[('C2',1),('M',1)],[('S2',1),('M',1)]),('S1S2M->PM',[('S1',1),('S2',1),('M',1)],[('P',1),('M',1)])],True)
    

# Money exchange example
def money_exchange(number):
    if number == 1:
        I = ['5']
        G = ['2','1','1','1']
    elif number == 2:
        I = ['10']
        G = ['2','2','2','2','1','1']
    A = [('Change-10',['10'],['5','5']), ('Change-5',['5'],['2','2','1']), ('Change-2',['2'],['1','1'])]
    prove(I,G,A,True)
    
# There are 2 arms(L,R), 2 rooms(A,B) and 2 balls(b1,b2)  
def gripper():
    # Init = ['r_at_A','free_l','free_r','b1_at_A','b2_at_A']
    # Goal = ['b1_at_B', 'b2_at_B', 'r_at_B', 'free_l', 'free_r']
    # Rules = [('Move-A-B',['r_at_A'],['r_at_B']), ('Pick-b1-A-L',['b1_at_A','r_at_A','free_l'],['carry_b1_l', 'r_at_A']), ('Pick-b2-A-R',['b2_at_A','r_at_A','free_r'],['carry_b2_r','r_at_A']), ('Drop-b1-B-L',['carry_b1_l', 'r_at_B'],['b1_at_B','r_at_B','free_l']), ('Drop-b2-B-R',['carry_b2_r','r_at_B'],['b2_at_B','r_at_B','free_r'])]
    # prove(Init, Goal, Rules, True)

    Init = ['r_at_A','free_l','free_r','b1_at_A','b2_at_A']
    Goal = ['b1_at_B', 'b2_at_A', 'r_at_B', 'free_l', 'free_r']
    Rules = [('Move-A-B',['r_at_A'],['r_at_B']), ('Move-B-A',['r_at_B'],['r_at_A']), ('Pick-b1-A-L',['b1_at_A','r_at_A','free_l'],['carry_b1_l', 'r_at_A']), ('Pick-b2-A-R',['b2_at_A','r_at_A','free_r'],['carry_b2_r','r_at_A']), ('Drop-b1-B-L',['carry_b1_l', 'r_at_B'],['b1_at_B','r_at_B','free_l']), ('Drop-b2-B-R',['carry_b2_r','r_at_B'],['b2_at_B','r_at_B','free_r'])]
    prove(Init, Goal, Rules, True)

    
    # Init = ['r1','r2','r3']
    # Goal = ['k1', 'k2', 'k3']
    # Rules = [('Move-A-B',['r1'],['k1']), ('Move-B-A',['r2'],['k2']), ('Pick-b1-A-L',['r3'],['k3'])]
    # prove(Init, Goal, Rules, True)

def blocksworld(number):
    if number == 1:
        I = [('empty', 1), ('clear_a', 1), ('ontable_a', 1)]
        G = [('hold_a', 1)]
        A = [('FT(a)',[('empty',1), ('ontable_a',1), ('clear_a',1)],[('hold_a',1)]), ('ON(a,b)',[('hold_a',1),('clear_b',1)],[('empty',1),('on_a_b',1),('clear_a',1)])]
    # elif number == 2:
    #     I = ['empty', 'clear_a', 'ontable_a', 'clear_b', 'ontable_b']
    #     G = ['empty', 'clear_a', 'on_a_b', 'ontable_b']
    #     A = [('FT(a)',['empty', 'ontable_a', 'clear_a'],['hold_a']), ('OT(a)',['hold_a'],['empty','ontable_a','clear_a']), ('ON(a,b)',['hold_a','clear_b'],['empty','on_a_b','clear_a'])]
    # elif number == 3:
    #     I = ['hold_a', 'clear_b', 'ontable_b']
    #     G = ['empty', 'clear_b', 'on_b_a', 'ontable_a']
    #     #??
    # elif number == 5:
    #     I = ['empty', 'clear_a', 'on_a_b', 'on_b_c', 'ontable_c']
    #     G = ['hold_c', 'clear_b', 'on_b_a', 'ontable_a']
    #     A = [('U(a,b)',['empty','on_a_b','clear_a'],['hold_a','clear_b']), ('OT(a)',['hold_a'],['empty','ontable_a','clear_a']), ('U(b,c)',['empty','on_b_c','clear_b'],['hold_b','clear_c']), ('O(b,a)',['hold_b','clear_a'],['empty','on_b_a','clear_b']), ('FT(c)',['empty', 'ontable_c', 'clear_c'],['hold_c']), ('O(c,b)',['hold_c','clear_b'],['empty','on_c_b','clear_c'])]
    # elif number == 6:
    #     I = ['empty', 'clear_a', 'on_a_b', 'on_b_c', 'ontable_c']
    #     G = ['empty', 'clear_c', 'on_c_b', 'on_b_a', 'ontable_a']
    #     A = [('U(a,b)',['empty','on_a_b','clear_a'],['hold_a','clear_b']), ('OT(a)',['hold_a'],['empty','ontable_a','clear_a']), ('U(b,c)',['empty','on_b_c','clear_b'],['hold_b','clear_c']), ('O(b,a)',['hold_b','clear_a'],['empty','on_b_a','clear_b']), ('FT(c)',['empty', 'ontable_c', 'clear_c'],['hold_c']), ('O(c,b)',['hold_c','clear_b'],['empty','on_c_b','clear_c'])]
    elif number == 16: # plan has 1-Step (1 action)
        I = [('empty', 1), ('clear_a', 1), ('on_a_b', 1), ('on_b_c', 1), ('ontable_c', 1)]
        G = [('hold_a', 1), ('clear_b', 1), ('on_b_c', 1), ('ontable_c', 1)]
        A = [('U(a,b)',[('empty', 1),('on_a_b', 1),('clear_a', 1)],[('hold_a', 1),('clear_b', 1)]), ('OT(a)',[('hold_a', 1)],[('empty', 1),('ontable_a', 1),('clear_a', 1)]), ('U(b,c)',[('empty', 1),('on_b_c', 1),('clear_b', 1)],[('hold_b', 1),('clear_c', 1)]), ('O(b,a)',[('hold_b', 1),('clear_a', 1)],[('empty', 1),('on_b_a', 1),('clear_b', 1)]), ('FT(c)',[('empty', 1), ('ontable_c', 1), ('clear_c', 1)],[('hold_c', 1)]), ('O(c,b)',[('hold_c', 1),('clear_b', 1)],[('empty', 1),('on_c_b', 1),('clear_c', 1)])]
    elif number == 26: # plan has 2-Step (2 actions)
        I = [('empty', 1), ('clear_a', 1), ('on_a_b', 1), ('on_b_c', 1), ('ontable_c', 1)]
        G = [('empty', 1), ('clear_b', 1), ('on_b_c', 1), ('ontable_c', 1), ('ontable_a', 1), ('clear_a', 1)]
        A = [('U(a,b)',[('empty', 1),('on_a_b', 1),('clear_a', 1)],[('hold_a', 1),('clear_b', 1)]), ('OT(a)',[('hold_a', 1)],[('empty', 1),('ontable_a', 1),('clear_a', 1)]), ('U(b,c)',[('empty', 1),('on_b_c', 1),('clear_b', 1)],[('hold_b', 1),('clear_c', 1)]), ('O(b,a)',[('hold_b', 1),('clear_a', 1)],[('empty', 1),('on_b_a', 1),('clear_b', 1)]), ('FT(c)',[('empty', 1), ('ontable_c', 1), ('clear_c', 1)],[('hold_c', 1)]), ('O(c,b)',[('hold_c', 1),('clear_b', 1)],[('empty', 1),('on_c_b', 1),('clear_c', 1)])]
    elif number == 36: # plan has 3-Step (3 actions)
        I = [('empty', 1), ('clear_a', 1), ('on_a_b', 1), ('on_b_c', 1), ('ontable_c', 1)]
        G = [('hold_b', 1), ('ontable_c', 1), ('clear_c', 1), ('ontable_a', 1), ('clear_a', 1)]
        A = [('U(a,b)',[('empty', 1),('on_a_b', 1),('clear_a', 1)],[('hold_a', 1),('clear_b', 1)]), ('OT(a)',[('hold_a', 1)],[('empty', 1),('ontable_a', 1),('clear_a', 1)]), ('U(b,c)',[('empty', 1),('on_b_c', 1),('clear_b', 1)],[('hold_b', 1),('clear_c', 1)]), ('O(b,a)',[('hold_b', 1),('clear_a', 1)],[('empty', 1),('on_b_a', 1),('clear_b', 1)]), ('FT(c)',[('empty', 1), ('ontable_c', 1), ('clear_c', 1)],[('hold_c', 1)]), ('O(c,b)',[('hold_c', 1),('clear_b', 1)],[('empty', 1),('on_c_b', 1),('clear_c', 1)])]
    elif number == 46: # plan has 4-Step (4 actions)
        I = [('empty', 1), ('clear_a', 1), ('on_a_b', 1), ('on_b_c', 1), ('ontable_c', 1)]
        G = [('empty', 1), ('ontable_c', 1), ('clear_c', 1), ('ontable_a', 1), ('on_b_a', 1), ('clear_b', 1)]
        A = [('U(a,b)',[('empty', 1),('on_a_b', 1),('clear_a', 1)],[('hold_a', 1),('clear_b', 1)]), ('OT(a)',[('hold_a', 1)],[('empty', 1),('ontable_a', 1),('clear_a', 1)]), ('U(b,c)',[('empty', 1),('on_b_c', 1),('clear_b', 1)],[('hold_b', 1),('clear_c', 1)]), ('O(b,a)',[('hold_b', 1),('clear_a', 1)],[('empty', 1),('on_b_a', 1),('clear_b', 1)]), ('FT(c)',[('empty', 1), ('ontable_c', 1), ('clear_c', 1)],[('hold_c', 1)]), ('O(c,b)',[('hold_c', 1),('clear_b', 1)],[('empty', 1),('on_c_b', 1),('clear_c', 1)])]
    elif number == 56: # plan has 5-Step (5 actions)
        I = [('empty', 1), ('clear_a', 1), ('on_a_b', 1), ('on_b_c', 1), ('ontable_c', 1)]
        G = [('hold_c', 1), ('clear_b', 1), ('on_b_a', 1), ('ontable_a', 1)]
        A = [('U(a,b)',[('empty', 1),('on_a_b', 1),('clear_a', 1)],[('hold_a', 1),('clear_b', 1)]), ('OT(a)',[('hold_a', 1)],[('empty', 1),('ontable_a', 1),('clear_a', 1)]), ('U(b,c)',[('empty', 1),('on_b_c', 1),('clear_b', 1)],[('hold_b', 1),('clear_c', 1)]), ('O(b,a)',[('hold_b', 1),('clear_a', 1)],[('empty', 1),('on_b_a', 1),('clear_b', 1)]), ('FT(c)',[('empty', 1), ('ontable_c', 1), ('clear_c', 1)],[('hold_c', 1)]), ('O(c,b)',[('hold_c', 1),('clear_b', 1)],[('empty', 1),('on_c_b', 1),('clear_c', 1)])]
    elif number == 66: # plan has 6-Step (6 actions)
        I = [('empty', 1), ('clear_a', 1), ('on_a_b', 1), ('on_b_c', 1), ('ontable_c', 1)]
        G = [('empty', 1), ('clear_c', 1), ('on_c_b', 1), ('on_b_a', 1), ('ontable_a', 1)]
        A = [('U(a,b)',[('empty', 1),('on_a_b', 1),('clear_a', 1)],[('hold_a', 1),('clear_b', 1)]), ('OT(a)',[('hold_a', 1)],[('empty', 1),('ontable_a', 1),('clear_a', 1)]), ('U(b,c)',[('empty', 1),('on_b_c', 1),('clear_b', 1)],[('hold_b', 1),('clear_c', 1)]), ('O(b,a)',[('hold_b', 1),('clear_a', 1)],[('empty', 1),('on_b_a', 1),('clear_b', 1)]), ('FT(c)',[('empty', 1), ('ontable_c', 1), ('clear_c', 1)],[('hold_c', 1)]), ('O(c,b)',[('hold_c', 1),('clear_b', 1)],[('empty', 1),('on_c_b', 1),('clear_c', 1)])]
    prove(I,G,A,True)
