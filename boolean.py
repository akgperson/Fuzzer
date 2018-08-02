import time
import math
import argparse
import random
from collections import OrderedDict

class Op:
    def __init__(self, node, expr):
        self.expr = expr
        self.node = node

    def __repr__(self):
        return '({} {})'.format(self.node, self.expr)

    def __eq__(self, other):
        return isinstance(other, Op) and self.expr == other.expr and self.node == other.node

    def __hash__(self):
        return hash((self.expr, self.node))

class Bool_Op(Op):
    def __init__(self, node, expr):
        Op.__init__(self, node, expr)

class USort_Op(Op):
    def __init__(self, node, expr):
        Op.__init__(self, node, expr)

class Int_Op(Op):
    def __init__(self, node, expr):
        Op.__init__(self, node, expr)
    
class Real_Op(Op):
    def __init__(self, node, expr):
        Op.__init__(self, node, expr)
    
class BV_Op(Op):
    def __init__(self, node, expr):
        Op.__init__(self, node, expr)

class Arr_Op(Op):
    def __init__(self, node, expr):
        Op.__init__(self, node, expr)

class Var:
    def __init__(self, sort, n):
        self.sort = sort
        self.n = n

    def __repr__(self):
        return str(self.sort) + str(self.n)

class Var_Bool(Var):
    def __init__(self, n):
        Var.__init__(self, 'v', n)

    def __eq__(self, other):
        return isinstance(other, Var_Bool) and self.n == other.n

    def __hash__(self):
        return hash((self.sort, self.n))

class Var_Int(Var):
    def __init__(self, n):
        Var.__init__(self, 'i', n)

    def __eq__(self, other):
        return isinstance(other, Var_Int) and self.n == other.n

    def __hash__(self):
        return hash((self.sort, self.n))

class Var_Real(Var):
    def __init__(self, n):
        Var.__init__(self, 'r', n)

    def __eq__(self, other):
        return isinstance(other, Var_Real) and self.n == other.n

    def __hash__(self):
        return hash((self.sort, self.n))

class Var_UnIntSort(Var):
    def __init__(self, sort, n):
        Var.__init__(self, sort, n)

    def __repr__(self):
        return '{}-{}'.format(self.sort, self.n)

    def __eq__(self, other):
        return isinstance(other, Var_UnIntSort) and self.n == other.n and self.sort == other.sort

    def __hash__(self):
        return hash((self.sort, self.n))

class Var_BV(Var):
    def __init__(self, sort, n):
        Var.__init__(self, sort, n)

    def __repr__(self):
        return 'bv_{}-{}'.format(self.sort, self.n)

    def __eq__(self, other):
        return isinstance(other, Var_BV) and self.n == other.n and self.sort == other.sort

    def __hash__(self):
        return hash((self.sort, self.n))

class Var_Arr(Var):
    def __init__(self, sort_index, sort_element, n):
        Var.__init__(self, sort_index, n)
        self.sort_element = sort_element

    def __repr__(self):
        return 'arr-{}_{}-{}'.format(self.sort, self.sort_element, self.n)

    def __eq__(self, other):
        return isinstance(other, Var_Arr) and self.n == other.n and self.sort == other.sort and self.sort_element == other.sort_element

    def __hash__(self):
        return hash((self.sort, self.sort_element, self.n))

class Sort:
    def __init__(self, sort):
        self.sort = sort        

    def __repr__(self):
        return str(self.sort)

class Bool(Sort):
    def __init__(self):
        Sort.__init__(self, 'bool')

    def __eq__(self, other):
        return isinstance(other, Bool)

    def __hash__(self):
        return hash(self.sort)

class Int(Sort):
    def __init__(self):
        Sort.__init__(self, 'int')

    def __eq__(self, other):
        return isinstance(other, Int)

    def __hash__(self):
        return hash(self.sort)
        
class Real(Sort):
    def __init__(self):
        Sort.__init__(self, 'real')

    def __eq__(self, other):
        return isinstance(other, Real)

    def __hash__(self):
        return hash(self.sort)

class UnIntSort(Sort):
    def __init__(self, n):
        Sort.__init__(self, 'S')
        self.n = n

    def __repr__(self):
        return str(self.sort) + str(self.n)

    def __eq__(self, other):
        return isinstance(other, UnIntSort) and self.n == other.n

    def __hash__(self):
        return hash((self.sort, self.n))

class BV(Sort):
    def __init__(self, w):
        Sort.__init__(self, 'BV')
        self.w = w

    def __repr__(self):
        return str(self.sort) + str(self.w)

    def __eq__(self, other):
        return isinstance(other, BV) and self.w == other.w

    def __hash__(self):
        return hash((self.sort, self.w))

class Arr(Sort):
    def __init__(self, sort_index, sort_element):
        Sort.__init__(self, 'Arr')
        self.sort_index = sort_index
        self.sort_element = sort_element

    def __repr__(self):
        return '(_Array {} {})'.format(self.sort_index, self.sort_element)

    def __eq__(self, other):
        return isinstance(other, Arr) and self.sort_index == other.sort_index and self.sort_element == other.sort_element

    def __hash__(self):
        return hash((self.sort, self.sort_index, self.sort_element))

def random_real():
    y = 0
    if random.random() < 0.8:
        real = str(random.randint(1, 9))
    else:
        real = "0."
        y += 1
    i = random.randint(0, 10)
    for x in range(i):
        if random.random() < 0.05 and y == 0:
            real += "."
            y += 1
        else:
            real += str(random.randint(0, 9))
    if real[-1] == ".":
        real += "0"
    return real

def random_BV():
    prob = random.random()
    num = random.randint(0, 1000)
    if prob < 0.33:
        if random.random() < 0.5:
            bv = "#b" + str(bin(num)[2:])
            width = len(str(bin(num)[2:]))
        else:
            bv = "#b0" + str(bin(num)[2:])
            width = len(str(bin(num)[2:])) + 1
    elif prob < 0.66:
        bv = "#x" + str(hex(num)[2:])
        width = len(str(hex(num)[2:])) * 4
    else:
        width = len(str(bin(num)[2:]))
        bv = "(_ bv{} {})".format(num, width)
    return bv, width

def Ratio(lower_bound, upper_bound, ratio):
    n_variables = random.randint(lower_bound, upper_bound)
    n_clauses = math.ceil(ratio * n_variables)
    return n_variables, n_clauses

def find(s, ch):
    return [i for i, ltr in enumerate(s) if ltr == ch]

def replace_idx(s, index, replacement):
    return '{}{}{}'.format(s[:index], replacement, s[index+1:])

def set_options(option_fuzzing):
    if option_fuzzing == 1:
        tf = ['true', 'false']
        print('(set-option :incremental true)')
        print('(set-option :check-models true)')
        print('(set-option :check-unsat-cores true)')
        l = random.randint(0, len(boolean_solver_options))
        to_set = random.sample(boolean_solver_options, l)
        for i in to_set:
            print('(set-option :{} {})'.format(i, random.choice(tf)))
    if option_fuzzing == 0:
        print('(set-option :incremental true)')
        print('(set-option :check-models true)')
        print('(set-option :check-unsat-cores true)')

def set_logic(logic, option_fuzzing):
    a=0.33 #newSort
    b=0.66 #varUSort
    c=1 #bool_from_usort
    ni=0.33 #new_int 
    e=0.33 #int_from_int
    f=0.33 #bool_from_int
    g=0.33 #new_real
    h=0.33 #real_from_real
    m=0.33 #bool_from_real
    v=0.33 #real_and_int
    r=0.33 #new_BV
    t=0.33 #BV_from_BV
    u=0.33 #bool_from_BV
    gen_arr=0.33 #arrays of any sort
    add_reals = 0
    add_ints = 0

    logic_options = ['ALL', 'QF_ABV', 'QF_BV', 'QF_AUFBV', 'QF_NIA', 'QF_NRA', 'QF_UF', 'QF_UFNRA', 'QF_UFNIA', 'QF_UFBV', 'QF_AX', 'QF_ABV', 'QF_AUFBV']
    
    if logic == 'random':
        logic_choice = random.choice(logic_options)
    else:
        logic_choice = logic

    if logic_choice == 'ALL':
        print('(set-logic ALL)')
        set_options(option_fuzzing)
        add_reals = 1
        add_ints = 1

    elif logic_choice == 'QF_ABV':
        print('(set-logic QF_ABV)')
        set_options(option_fuzzing)
        a, b, c, ni, e, f, g, h, m, v, gen_arr = -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1 

    elif logic_choice == 'QF_BV':
        print('(set-logic QF_BV)')
        set_options(option_fuzzing)
        a, b, c, ni, e, f, g, h, m, v, gen_arr = -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1

    elif logic_choice == 'QF_AUFBV':
        print('(set-logic QF_AUFBV)')
        set_options(option_fuzzing)
        ni, e, f, g, h, m, v, gen_arr = -1, -1, -1, -1, -1, -1, -1, -1

    elif logic_choice == 'QF_NIA':
        print('(set-logic QF_NIA)')
        set_options(option_fuzzing)
        a, b, c, g, h, m, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_ints = 1

    elif logic_choice == 'QF_NRA':
        print('(set-logic QF_NRA)')
        set_options(option_fuzzing)
        a, b, c, ni, e, f, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
        add_reals = 1

    elif logic_choice == 'QF_UF':
        print('(set-logic QF_UF)')
        set_options(option_fuzzing)
        ni, e, f, g, h, m, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1

    elif logic_choice == 'QF_UFBV':
        print('(set-logic QF_UFBV)')
        set_options(option_fuzzing)
        ni, e, f, g, h, m, v, gen_arr = -1, -1, -1, -1, -1, -1, -1, -1

    elif logic_choice == 'QF_UFNRA':
        print('(set-logic QF_UFNRA)')
        set_options(option_fuzzing)
        ni, e, f, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, -1
        add_reals = 1

    elif logic_choice == 'QF_UFNIA':
        print('(set-logic QF_UFNIA)')
        set_options(option_fuzzing)
        g, h, m, v, r, t, u, gen_arr = -1, -1, -1, -1, -1, -1, -1, -1
        add_ints = 1

    elif logic_choice == 'QF_AX':
        print('(set-logic QF_AX)')
        set_options(option_fuzzing)
        add_reals = 1
        add_ints = 1

    elif logic_choice == 'QF_ABV':
        print('(set-logic QF_AX)')
        set_options(option_fuzzing)
        a, b, c, ni, e, f, g, h, m, v = -1, -1, -1, -1, -1, -1, -1, -1, -1, -1

    elif logic_choice == 'QF_AUFBV':
        print('(set-logic QF_AX)')
        set_options(option_fuzzing)
        ni, e, f, g, h, m, v = -1, -1, -1, -1, -1, -1, -1

    return a, b, c, ni, e, f, g, h, m, v, r, t, u, gen_arr, add_ints, add_reals

class Clauses():
    def __init__(self, b, nc):
        self.n_clauses = nc
        self.clauses = []
        self.unused_options = list(b)
        self.all_options = list(b)

    def new_cnfs(self):
        for i in range(self.n_clauses):
            cnf = "(or "
            for j in range(2):
                n_left = ((self.n_clauses-i)*3) + (3-j)
                if len(self.unused_options) == n_left:
                    addition = random.choice(self.unused_options)
                    cnf += (str(addition) + " ")
                    self.unused_options.remove(addition)
                else:
                    addition = random.choice(self.all_options)
                    cnf += (str(addition) + " ")
                    if addition in self.unused_options:
                        self.unused_options.remove(addition)
            n_left = ((self.n_clauses-i)*3) + (3-j)
            if len(self.unused_options) == n_left:
                addition = random.choice(self.unused_options)
                cnf += (str(addition) + ")")
            else:
                addition = random.choice(self.all_options)
                cnf += (str(addition) + ")")
            self.clauses.append(cnf)
            print('(assert ' + cnf + ')')

    def new_dist_cnfs(self):
        n_slots = (self.n_clauses * 3)
        string = ""
        for i in range(n_slots - 1):
            n_left = n_slots - i
            if len(self.unused_options) == n_left:
                addition = random.choice(self.unused_options)
                string += (str(addition) + "$")
                self.unused_options.remove(addition)
            else:
                addition = random.choice(self.all_options)
                string += (str(addition) + "$")
                if addition in self.unused_options:
                    self.unused_options.remove(addition)
        if len(self.unused_options) == 1:
            addition = random.choice(self.unused_options)
            string += str(addition)
        else:
            addition = random.choice(self.all_options)
            string += str(addition)

        place_holders = find(string, '$')
        w = n_slots - (self.n_clauses - 1)
        spaces = random.sample(place_holders, w)  
        for x in spaces:
            string = replace_idx(string, x, ' ')
        partitions = find(string, '$') 
        CNFs = []
        for x in partitions:
            c = string[:x]
            q = c.rfind('$')
            if q >= 0:
                c = c[q+1:] 
            CNFs.append(c)
        for items in CNFs:
            new_CNF = '(or {})'.format(items)
            self.clauses.append(new_CNF)
            print('(assert {})'.format(new_CNF))

    def cnf_choice(self):
        return random.choice(self.clauses)
    
    def node_from_cnf(self):
        n_operands = random.randint(1, 10)
        operands = ""
        operands = str(random.choice(self.clauses))
        for i in range(n_operands):
            operands += (" " + str(random.choice(self.clauses)))
        n_and = operands.count('and')
        n_or = operands.count('or')
        if n_and > n_or:
            new_cnf = Op('or', operands)
        elif n_and < n_or:
            new_cnf = Op('and', operands)
        else:
            if random.random() < 0.5:
                new_cnf = Op('or', operands)
            else:  
                new_cnf = Op('and', operands)
        self.clauses.append(new_cnf)
        return new_cnf

    def bin_node(self):
        op1 = '{} {}'.format(random.choice(self.clauses), random.choice(self.clauses))
        op2 = '{} {}'.format(random.choice(self.clauses), random.choice(self.clauses))
        new_cnf1 = Op('=>', op1)
        new_cnf2 = Op('or', op2)
        self.clauses.append(new_cnf1)
        self.clauses.append(new_cnf2)
        return new_cnf1, new_cnf2

class Nodes:
    def __init__(self, a_ints, a_reals):
        self.d = OrderedDict()
        self.d[Bool()] = []
        self.d[Int()] = []
        self.d[Real()] = []

        #dictionary of number of all nodes ever created
        self.dict = OrderedDict()
        self.dict[Bool()] = 0
        self.dict[Int()] = 0
        self.dict[Real()] = 0

        self.count = OrderedDict()

        self.initial_ints = a_ints
        self.initial_reals = a_reals

        self.new_keys = []
        self.indices = []

        self.n_vars = random.randint(1, 20)
        self.n_ints = random.randint(1, 20)
        self.n_reals = random.randint(1, 20)

        for i in range(self.n_vars):
            self.d[Bool()].append(Var_Bool(i)) 
            print('(declare-const {} Bool)'.format(Var_Bool(i)))
            self.dict[Bool()] += 1
            self.count[Var_Bool(i)] = 0
        if self.initial_ints == 1:
            for i in range(self.n_ints):
                if random.random() < 0.5:
                    self.d[Int()].append(Var_Int(i))
                    print('(declare-const {} Int)'.format(Var_Int(i)))
                    self.count[Var_Int(i)] = 0
                else:   
                    val = random.randint(0, 100)
                    self.d[Int()].append(val)
                    self.count[val] = 0
                self.dict[Int()] += 1
        if self.initial_reals == 1:
            for i in range(self.n_reals):
                if random.random() < 0.5:
                    self.d[Real()].append(Var_Real(i))
                    print('(declare-const {} Real)'.format(Var_Real(i)))
                    self.count[Var_Real(i)] = 0
                else:
                    new_real = random_real()
                    self.d[Real()].append(new_real)
                    self.count[new_real] = 0
                self.dict[Real()] += 1
    
    def push(self):
        print('(push 1)')

        self.new_keys.append(len(list(self.d)))

        self.indices.append([])
        for key in self.d:
            self.indices[-1].append(len(self.d[key]))

    def pop(self):
        print('(pop 1)')

        n_keys = self.new_keys[-1]
        self.new_keys.pop()
        added_keys = list(self.d)[n_keys:]
        for ones in added_keys:
            del self.d[ones]

        for key in self.d:
            j = self.indices[-1][list(self.d).index(key)]
            del self.d[key][j:]
        self.indices.pop()

    def newSort(self):
        n_unintsorts = 0
        for o in list(self.d):
            if type(o) is UnIntSort:
                n_unintsorts += 1
        if n_unintsorts < 5:
            current_sort = UnIntSort(n_unintsorts)
            print('(declare-sort {} 0)'.format(current_sort))
            self.d[current_sort] = []
            self.dict[current_sort] = 0
        else:
            pass
    
    def varUSort(self):
        options = []
        for o in list(self.d):
            if type(o) is UnIntSort:
                options.append(o)
        if len(options) > 0:
            current_sort = random.choice(options)
            n = len(self.d[current_sort])
            self.d[current_sort].append(Var_UnIntSort(current_sort, n))
            self.count[Var_UnIntSort(current_sort, n)] = 0
            print('(declare-const {} {})'.format(Var_UnIntSort(current_sort, n), current_sort))
            self.dict[current_sort] += 1

    def bool_from_usort(self):
        ops = []
        options = []
        for o in list(self.d):
            if type(o) is UnIntSort:
                ops.append(o)
        for things in ops:
            if len(self.d[things]) > 0:
                options.append(things)
        if len(options) > 0:
            current_sort = random.choice(options)
            n_items = random.randrange(1, 5)
            par = random.choice(self.d[current_sort])
            items = str(par)
            self.count[par] += 1
            for i in range(n_items):
                par = random.choice(self.d[current_sort])
                self.count[par] += 1
                items += (" " + str(par))
            if random.random() < 0.5:
                new_bool = Bool_Op('=', items)
            else:
                new_bool = Bool_Op('distinct', items) 
            self.d[Bool()].append(new_bool)         
            self.count[new_bool] = 0
            self.dict[Bool()] += 1   

    def new_bool(self):
        new_var = Var_Bool(self.n_vars)
        print('(declare-const {} Bool)'.format(new_var))
        self.n_vars += 1
        self.d[Bool()].append(new_var)
        self.count[new_var] = 0
        self.dict[Bool()] += 1   

    def new_int(self):
        if random.random() < 0.3:
            new_int = Var_Int(self.n_ints)
            print('(declare-const {} Int)'.format(new_int))
            self.n_ints += 1
            self.d[Int()].append(new_int)
            self.count[new_int] = 0
        else:
            new_int = random.randint(0, 1000)
            self.d[Int()].append(new_int)
            self.count[new_int] = 0
        self.dict[Int()] += 1

    def int_from_int(self):
        p = random.random()
        if p < 0.4:
            par = random.choice(self.d[Int()])
            new_int = Int_Op(random.choice(IntUnOp), par)
            self.d[Int()].append(new_int)
            self.count[new_int] = 0
            self.count[par] += 1
        elif p < 0.66:
            par1 = random.choice(self.d[Int()])
            operand = str(par1)
            par2 = random.choice(self.d[Int()])
            operand += (" " + str(par2))
            new_int = Int_Op(random.choice(IntBinOp), operand)
            self.d[Int()].append(new_int)
            self.count[par1] += 1     
            self.count[par2] += 1    
            self.count[new_int] = 0    
        else:
            par = random.choice(self.d[Int()])
            self.count[par] += 1
            operand = str(par)
            n = random.randrange(1, 5)
            for i in range(n):
                par = random.choice(self.d[Int()])
                self.count[par] += 1
                operand += (" " + str(par))
            new_int = Int_Op(random.choice(IntNOp), operand)
            self.d[Int()].append(new_int)
            self.count[new_int] = 0
        self.dict[Int()] += 1

    def bool_from_int(self):
        #can you choose multiple operands? chainable?
        par = random.choice(self.d[Int()])
        operand = str(par)
        self.count[par] += 1 
        par = random.choice(self.d[Int()])
        self.count[par] += 1 
        operand += (" " + str(par))
        new_bool = Bool_Op(random.choice(IRNBoolOp), operand)
        self.d[Bool()].append(new_bool)
        self.count[new_bool] = 0
        #want to add possibility of asserting this bool here?
        self.dict[Bool()] += 1

    def new_real(self):
        if random.random() < 0.5:
            self.d[Real()].append(Var_Real(self.n_reals))
            self.count[Var_Real(self.n_reals)] = 0
            print('(declare-const {} Real)'.format(Var_Real(self.n_reals)))
            self.n_reals += 1
        else:
            new_real = random_real()
            self.d[Real()].append(new_real)
            self.count[new_real] = 0
        self.dict[Real()] += 1

    def real_from_real(self):
        chance = random.random()
        if chance < 0.33: #unary
            par = random.choice(self.d[Real()])
            self.count[par] += 1
            self.d[Real()].append(Real_Op("-", par))
            self.count[Real_Op("-", par)] = 0
        elif chance < 0.67: #binary
            par = random.choice(self.d[Real()])
            self.count[par] += 1
            operands = str(par) 
            par = random.choice(self.d[Real()])
            self.count[par] += 1
            operands += (" " + str(par))
            self.d[Real()].append(Real_Op("/", operands))
            self.count[Real_Op("/", operands)] = 0
        else: #n-array
            par = random.choice(self.d[Real()])
            self.count[par] += 1
            operands = str(par)
            x = random.randrange(1, 5)
            for i in range(x):
                par = random.choice(self.d[Real()])
                self.count[par] += 1
                operands += (" " + str(par))
            new_real = Real_Op(random.choice(RealNOp), operands)
            self.d[Real()].append(new_real)
            self.count[new_real] = 0
        self.dict[Real()] += 1

    def bool_from_real(self):
        #n-array or binary?
        par = random.choice(self.d[Real()])
        self.count[par] += 1
        operands = str(par)
        n_operands = random.randrange(1, 5)
        for i in range(n_operands):
            par = random.choice(self.d[Real()])
            self.count[par] += 1
            operands += (" " + str(par))
        new_bool = Bool_Op(random.choice(IRNBoolOp), operands)
        self.d[Bool()].append(new_bool)
        self.count[new_bool] = 0
        #give possibility of asserting this new bool here?
        self.dict[Bool()] += 1
    
    def real_and_int(self):
        chance = random.randint(1, 3)
        if chance == 1:
            par = random.choice(self.d[Int()])
            self.count[par] += 1
            self.d[Real()].append(Real_Op("to_real", par))
            self.count[Real_Op("to_real", par)] = 0
            self.dict[Real()] += 1
        elif chance == 2:
            par = random.choice(self.d[Real()])
            self.count[par] += 1
            self.d[Int()].append(Int_Op("to_int", par))
            self.count[Int_Op("to_int", par)] = 0
            self.dict[Int()] += 1
        else:
            par = random.choice(self.d[Real()])
            self.count[par] += 1
            self.d[Bool()].append(Bool_Op("is_int", par))
            self.count[Bool_Op("is_int", par)] = 0
            self.dict[Bool()] += 1

    def new_BV(self):
        if random.random() < 0.25:
            width = random.randint(1, 30)
            bv_sort = BV(width)
            if bv_sort not in self.d.keys():
                self.d[bv_sort] = [] 
                self.dict[bv_sort] = 0
            const = Var_BV(width, len(self.d[bv_sort])) 
            print('(declare-const {} (_ BitVec {}))'.format(const, width))
            self.d[bv_sort].append(const) 
            self.count[const] = 0
            self.dict[bv_sort] += 1
        else:
            bv, width = random_BV()
            bv_sort = BV(width)
            if bv_sort not in self.d.keys():
                self.d[bv_sort] = []
                self.dict[bv_sort] = 0
            self.d[bv_sort].append(bv)
            self.count[bv] = 0
            self.dict[bv_sort] += 1

    def BV_from_BV(self):
        options = []
        for o in list(self.d):
            if type(o) is BV:
                options.append(o) 
        if len(options) > 0:
            s = random.choice(options)
            prob = random.random()

            if prob < 0.05: #concat
                s2 = random.choice(options)
                width = s.w + s2.w
                par1 = random.choice(self.d[s])
                par2 = random.choice(self.d[s2])
                self.count[par1] += 1
                self.count[par2] += 1
                operand = str(par1) + " " + str(par2) 
                new_BV = BV_Op("concat", operand)
                bv_sort = BV(width)
                if bv_sort not in self.d.keys():
                    self.d[bv_sort] = []
                    self.dict[bv_sort] = 0
                self.d[bv_sort].append(new_BV) 
                self.count[new_BV] = 0
                self.dict[bv_sort] += 1

            elif prob < 0.1: #repeat
                i = random.randint(1, 10)
                width = i * s.w
                operator = '(_ repeat {})'.format(i)
                par = random.choice(self.d[s])
                self.count[par] += 1
                new_BV = BV_Op(operator, par) 
                bv_sort = BV(width)
                if bv_sort not in self.d.keys():
                    self.d[bv_sort] = []
                    self.dict[bv_sort] = 0
                self.d[bv_sort].append(new_BV) 
                self.count[new_BV] = 0
                self.dict[bv_sort] += 1

            elif prob < 0.2: #unary, extract
                if random.random() < 0.5: #unary
                    par = random.choice(self.d[s])
                    self.count[par] += 1
                    new_BV = BV_Op(random.choice(Un_BV_BV), par)
                    self.d[s].append(new_BV)
                    self.count[new_BV] = 0
                    self.dict[s] += 1
                else: #extract
                    width = s.w
                    parameter1 = random.randrange(0, width)
                    parameter2 = random.randint(0, parameter1)
                    operator = "(_ extract {} {})".format(parameter1, parameter2)
                    new_width = parameter1 - parameter2 + 1 
                    par = random.choice(self.d[s])
                    self.count[par] += 1
                    new_BV = BV_Op(operator, par)    
                    bv_sort = BV(new_width)
                    if bv_sort not in self.d.keys():
                        self.d[bv_sort] = []
                        self.dict[bv_sort] = 0
                    self.d[bv_sort].append(new_BV) 
                    self.count[new_BV] = 0
                    self.dict[bv_sort] += 1

            elif prob < 0.3:
                i = random.randint(0, 10)
                if random.random() < 0.5:
                    if random.random() < 0.5:
                        operator = "(_ zero_extend {})".format(i)
                    else:
                        operator = "(_ sign_extend {})".format(i)
                    width = s.w + i
                    par = random.choice(self.d[s])
                    self.count[par] += 1
                    new_BV = BV_Op(operator, par)
                    bv_sort = BV(width)
                    if bv_sort not in self.d.keys():
                        self.d[bv_sort] = []
                        self.dict[bv_sort] = 0
                    self.d[bv_sort].append(new_BV) 
                    self.count[new_BV] = 0
                    self.dict[bv_sort] += 1
                else:
                    if random.random() < 0.5:
                        operator = "(_ rotate_left {})".format(i)
                    else:
                        operator = "(_ rotate_right {})".format(i)
                    par = random.choice(self.d[s])
                    self.count[par] += 1
                    new_BV = BV_Op(operator, par)
                    self.d[s].append(new_BV)
                    self.count[new_BV] = 0
                    self.dict[s] += 1

            elif prob < 0.4: #n-array
                a = random.randint(1, 3)
                par = random.choice(self.d[s])
                self.count[par] += 1
                operand = str(par)
                for i in range(a):
                    par = random.choice(self.d[s])
                    self.count[par] += 1
                    operand += (" " + str(par))
                new_BV = BV_Op(random.choice(N_BV_BV), operand)
                self.d[s].append(new_BV)
                self.count[new_BV] = 0
                self.dict[s] += 1

            else: #binary
                par1 = random.choice(self.d[s])
                par2 = random.choice(self.d[s])
                self.count[par1] += 1
                self.count[par2] += 1
                operand = str(par1) + " " + str(par2)
                operator = random.choice(Bin_BV_BV)
                new_BV = BV_Op(operator, operand)
                if operator == "bvcomp":
                    if BV(1) not in self.d.keys():
                        self.d[BV(1)] = []
                        self.dict[BV(1)] = 0
                    self.d[BV(1)].append(new_BV)
                    self.count[new_BV] = 0
                    self.dict[BV(1)] += 1
                else:
                    self.d[s].append(new_BV)
                    self.count[new_BV] = 0
                    self.dict[s] += 1

    def bool_from_BV(self):
        options = []
        for o in list(self.d):
            if type(o) is BV:
                options.append(o) 
        if len(options) > 0:
            s = random.choice(options)
            if random.random() < 0.33:
                par1 = random.choice(self.d[s])
                par2 = random.choice(self.d[s])
                self.count[par1] += 1
                self.count[par2] += 1
                operand = str(par1) + " " + str(par2)
                new_bool = Bool_Op(random.choice(Bin_BV_Bool), operand)
            else:
                par = random.choice(self.d[s])
                self.count[par] += 1
                operand = str(par)
                n = random.randint(1, 4)
                for i in range(n):
                    par = random.choice(self.d[s])
                    self.count[par] += 1
                    operand += (" " + str(par))
                new_bool = Bool_Op(random.choice(N_BV_Bool), operand)
            self.d[Bool()].append(new_bool)
            self.count[new_bool] = 0
            self.dict[Bool()] += 1

    def new_array(self, logic):
        if logic == 'ALL' or logic == 'QF_AX':
            ops = []
            for o in list(self.d):
                if type(o) is not Arr:
                    ops.append(o)
                if type(o) is Arr:
                    if len(self.d[o]) > 0:
                        ops.append(o)
            isort = random.choice(ops)
            esort = random.choice(ops)
            arrsort = Arr(isort, esort)
            if arrsort not in list(self.d):
                self.d[arrsort] = []
                self.dict[arrsort] = 0
            n = len(self.d[arrsort])
            new_arr = Var_Arr(isort, esort, n)
            print('(declare-const {} {})'.format(new_arr, arrsort))
            self.d[arrsort].append(new_arr)
            self.count[new_arr] = 0
            self.dict[arrsort] += 1   
        if logic == 'QF_ABV' or logic == 'QF_AUFBV':
            ops = []
            for o in list(self.d):
                if type(o) is not Arr:
                    ops.append(o)
                if type(o) is Arr:
                    if len(self.d[o]) > 0:
                        ops.append(o)
            i_ops = []
            for o in list(self.d):
                if type(o) is BV and len(self.d[o]) > 0:
                    i_ops.append(o)
            isort = random.choice(i_ops)
            esort = random.choice(ops)
            arrsort = Arr(isort, esort)
            if arrsort not in list(self.d):
                self.d[arrsort] = []
                self.dict[arrsort] = 0
            n = len(self.d[arrsort])
            new_arr = Var_Arr(isort, esort, n)
            print('(declare-const {} {})'.format(new_arr, arrsort))
            self.d[arrsort].append(new_arr)
            self.count[new_arr] = 0
            self.dict[arrsort] += 1   

    def array_from_array(self):
        ops = []
        options = []
        for o in list(self.d):
            if type(o) is Arr:
                ops.append(o)
        for things in ops:
            if len(self.d[things]) > 0 and len(self.d[things.sort_index]) > 0 and len(self.d[things.sort_element]) > 0:
                options.append(things)
        if len(options) > 0:
            current_sort = random.choice(options)
            isort = current_sort.sort_index
            esort = current_sort.sort_element
            par = random.choice(self.d[current_sort])
            self.count[par] += 1
            par2 = random.choice(self.d[isort])
            par3 = random.choice(self.d[esort])
            self.count[par2] += 1
            self.count[par3] += 1
            items = '{} {} {}'.format(par, par2, par3) 
            new_arr = Arr_Op('store', items)
            self.d[current_sort].append(new_arr)         
            self.count[new_arr] = 0
            self.dict[current_sort] += 1   

    def bool_from_array(self):
        if random.random() < 0.5:
            ops = []
            options = []
            for o in list(self.d):
                if type(o) is Arr:
                    ops.append(o)
            for things in ops:
                if len(self.d[things]) > 0 and len(self.d[things.sort_index]) > 0:
                    options.append(things)
            if len(options) > 0:
                current_sort = random.choice(options)
                isort = current_sort.sort_index
                par = random.choice(self.d[current_sort])
                par2 = random.choice(self.d[isort])
                self.count[par] += 1
                self.count[par2] += 1
                expression = '{} {}'.format(par, par2)
                new_bool = Bool_Op('select', expression)
                self.d[Bool()].append(new_bool)
                self.count[new_bool] = 0
                self.dict[Bool()] += 1
        else:
            ops = []
            options = []
            for o in list(self.d):
                if type(o) is Arr:
                    ops.append(o)
            for things in ops:
                if len(self.d[things]) > 0:
                    options.append(things)
            if len(options) > 0:
                current_sort = random.choice(options)
                par = random.choice(self.d[current_sort])
                self.count[par] += 1
                operand = str(par)
                n = random.randint(1, 4)
                for i in range(n):
                    par = random.choice(self.d[current_sort])
                    self.count[par] += 1
                    operand += (" " + str(par))
                if random.random() < 0.5:
                    new_bool = Bool_Op('=', operand)
                else:
                    new_bool = Bool_Op('distinct', operand)
                self.d[Bool()].append(new_bool)
                self.count[new_bool] = 0
                self.dict[Bool()] += 1

    def bool_from_bool(self):
        p = random.randint(1, 7)
        if p == 1:
            #pick Unary
            par = random.choice(self.d[Bool()])
            self.count[par] += 1
            new_bool = Bool_Op(random.choice(UnOp), par)
        elif p == 2:
            #pick Binary
            operand = ""
            par1 = random.choice(self.d[Bool()])
            par2 = random.choice(self.d[Bool()])
            self.count[par1] += 1
            self.count[par2] += 1
            operand = str(par1)
            operand += (" " + str(par2))
            new_bool = Bool_Op(random.choice(BiOp), operand)
        else:    
            n_operands = random.randint(1, 10)
            operands = ""
            par = random.choice(self.d[Bool()])
            self.count[par] += 1
            operands = str(par)
            for i in range(n_operands):
                par = random.choice(self.d[Bool()])
                self.count[par] += 1
                operands += (" " + str(par))
            new_bool = Bool_Op(random.choice(NarOp), operands)
        self.d[Bool()].append(new_bool)
        self.count[new_bool] = 0
        self.dict[Bool()] += 1
        return new_bool

    def bool_choice(self):
        return random.choice(self.d[Bool()])

    def num_bool(self):
        return min(len(self.d[Bool()]), 20)

    def bool_sample(self, nvar):
        bool_idx = random.sample(range(len(self.d[Bool()])), nvar)
        sample = []
        for x in bool_idx:
            sample.append(self.d[Bool()][x])
        return sample

    def boolean_stats(self):
        co_bool = 0
        co_int = 0
        co_real = 0
        co_unintsort = 0
        co_bv = 0
        co_arr = 0
        for key in self.dict:
            print('; number {} created: {}'.format(key, self.dict[key]))

            if type(key) is Bool: 
                co_bool += self.dict[key]
            if type(key) is Int:
                co_int += self.dict[key]
            if type(key) is Real: 
                co_real += self.dict[key]
            if type(key) is UnIntSort: 
                co_unintsort += self.dict[key]
            if type(key) is BV:
                co_bv += self.dict[key]
            if type(key) is Arr:
                co_arr += self.dict[key]

        count_bool = 0
        count_int = 0
        count_real = 0
        count_unintsort = 0
        count_bv = 0
        count_arr = 0

        thl_int = 0
        thl_real = 0
        thl_usort = 0
        thl_bv = 0
        thl_arr = 0
        c_thl_int = 0
        c_thl_real = 0
        c_thl_usort = 0
        c_thl_bv = 0
        c_thl_arr = 0

        for key in self.count:
            if type(key) is Var_Bool or type(key) is Bool_Op: 
                count_bool += self.count[key]
            if type(key) is Var_Int or type(key) is Int_Op or isinstance(key, int):
                count_int += self.count[key]
                if type(key) is Int_Op:
                    thl_int += 1
                    c_thl_int += self.count[key]
            if type(key) is Var_Real or type(key) is Real_Op or (isinstance(key, str) and isinstance(key[0], int)): 
                count_real += self.count[key]
                if type(key) is Real_Op:
                    thl_real += 1
                    c_thl_real += self.count[key]
            if type(key) is Var_UnIntSort or type(key) is USort_Op: 
                count_unintsort += self.count[key]
                if type(key) is USort_Op:
                    thl_usort += 1
                    c_thl_usort += self.count[key]
            if type(key) is Var_BV or type(key) is BV_Op or (isinstance(key, str) and (key[0] == '#' or key[0] == '(')):
                count_bv += self.count[key]
                if type(key) is BV_Op:
                    thl_bv += 1
                    c_thl_bv += self.count[key]
            if type(key) is Var_Arr or type(key) is Arr_Op:
                count_arr += self.count[key]
                if type(key) is Arr_Op:
                    thl_arr += 1
                    c_thl_arr += self.count[key]
        print('; variables and nodes of boolean sort were used {} times where {} were created'.format(count_bool, co_bool))
        print('; variables and nodes of integer sort were used {} times where {} were created'.format(count_int, co_int))
        print('; variables and nodes of real sort were used {} times where {} were created'.format(count_real, co_real))
        print('; variables and nodes of uninterpreted sort were used {} times where {} were created'.format(count_unintsort, co_unintsort))
        print('; variables and nodes of bit vector sort were used {} times where {} were created'.format(count_bv, co_bv))
        print('; variables and nodes of array sort were used {} times where {} were created'.format(count_arr, co_arr))
        print('; {} integer theory literals used {} times'.format(thl_int, c_thl_int))
        print('; {} real theory literals used {} times'.format(thl_real, c_thl_real))
        print('; {} usort theory literals used {} times'.format(thl_usort, c_thl_usort))
        print('; {} bit vector theory literals used {} times'.format(thl_bv, c_thl_bv))
        print('; {} array theory literals used {} times'.format(thl_arr, c_thl_arr))

        for key in self.count:
            print('; {} nodes created using {}'.format(self.count[key], key))


UnOp = ["not"]
BiOp = ["=>"]
NarOp = ["and", "or", "xor", "=", "distinct"]
IntUnOp = ["-", "abs"]
IntBinOp = ["div", "mod"]
IntNOp = ["-", "+", "*"]
IRNBoolOp = ["<=", "<", ">=", ">", "=", "distinct"]
RealNOp = ["-", "+", "*"]

Bin_BV_BV = ["bvand", "bvor", "bvadd", "bvmul", "bvudiv", "bvurem", "bvshl", "bvlshr", "bvnand", "bvnor", "bvsub", "bvsdiv", "bvsrem", "bvsmod", "bvashr", "bvcomp", "bvxnor"]
N_BV_BV = ["bvxor"]
Un_BV_BV = ["bvnot", "bvneg"]
Bin_BV_Bool = ["bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge"]
N_BV_Bool = ["=", "distinct"]

boolean_solver_options = ['arith-no-partial-fun', 'arith-rewrite-equalities', 'collect-pivot-stats', 'ut-all-bounded', 'dio-decomps', 'dio-repeat', 'dio-solver', 'fc-penalties', 'lemmas-on-replay-failure', 'miplib-trick', 'new-prop', 'nl-ext', 'nl-ext-ent-conf', 'nl-ext-factor', 'nl-ext-inc-prec', 'nl-ext-purify', 'nl-ext-rbound', 'nl-ext-rewrite', 'nl-ext-split-zero', 'nl-ext-tf-tplanes', 'nl-ext-tplanes', 'nl-ext-tplanes-interleave', 'pb-rewrites', 'restrict-pivots', 'revert-arith-models-on-unsat', 'rewrite-divk', 'se-solve-int', 'snorm-infer-eq', 'soi-qe', 'use-approx', 'use-fcsimplex', 'use-soi', 'arrays-eager-index', 'arrays-eager-lemmas', 'arrays-lazy-rintro1', 'arrays-model-based', 'arrays-optimize-linear', 'arrays-reduce-sharing', 'arrays-weak-equiv', 'parse-only', 'preprocess-only', 'print-success', 'stats', 'stats-every-query', 'stats-hide-zeros', 'bitblast-aig', 'bool-to-bv', 'bv-abstraction', 'bv-alg-extf', 'bv-algebraic-solver', 'bv-div-zero-const', 'bv-eager-explanations', 'bv-eq-solver', 'bv-extract-arith', 'bv-gauss-elim', 'bv-inequality-solver', 'bv-intro-pow2', 'bv-lazy-reduce-extf', 'bv-lazy-rewrite-extf', 'bv-propagate', 'bv-quick-xplain', 'bv-skolemize', 'bv-to-bool', 'cdt-bisimilar', 'dt-binary-split', 'dt-blast-splits', 'dt-cyclic', 'dt-force-assignment', 'dt-infer-as-lemmas', 'dt-ref-sk-intro', 'dt-rewrite-error-sel', 'dt-share-sel', 'dt-use-testers', 'sygus-eval-builtin', 'sygus-fair-max', 'sygus-opt1', 'sygus-sym-break', 'sygus-sym-break-agg', 'sygus-sym-break-dynamic', 'sygus-sym-break-lazy', 'sygus-sym-break-pbe', 'sygus-sym-break-rlv', 'decision-use-weight', 'eager-type-checking', 'print-expr-types', 'type-checking', 'idl-rewrite-equalities', 'continued-execution', 'early-exit', 'fallback-sequential', 'help', 'incremental-parallel', 'interactive', 'interactive-prompt', 'segv-spin', 'version', 'wait-to-join', 'filesystem-access', 'mmap', 'strict-parsing', 'aggressive-core-min', 'allow-empty-dependencies', 'fewer-preprocessing-holes', 'lfsc-letification', 'minisat-dump-dimacs', 'minisat-elimination', 'refine-conflicts', 'ag-miniscope-quant', 'cbqi', 'cbqi-all', 'cbqi-bv', 'cbqi-bv-concat-inv', 'cbqi-bv-interleave-value', 'cbqi-bv-linear', 'cbqi-bv-rm-extract', 'cbqi-bv-solve-nl', 'cbqi-full', 'cbqi-innermost', 'cbqi-lit-dep', 'cbqi-midpoint', 'cbqi-min-bounds', 'cbqi-model', 'cbqi-multi-inst', 'cbqi-nested-qe', 'cbqi-nopt', 'cbqi-prereg-inst', 'cbqi-recurse', 'cbqi-repeat-lit', 'cbqi-round-up-lia', 'cbqi-sat', 'cbqi-use-inf-int', 'cbqi-use-inf-real', 'cegqi', 'cegqi-si-abort', 'cegqi-si-partial', 'cegqi-si-reconstruct-const', 'cegqi-si-sol-min-core', 'cegqi-si-sol-min-inst', 'cond-rewrite-quant', 'cond-var-split-agg-quant', 'cond-var-split-quant', 'conjecture-filter-active-terms', 'conjecture-filter-canonical', 'conjecture-filter-model', 'conjecture-gen', 'conjecture-gen-uee-intro', 'conjecture-no-filter', 'dt-stc-ind', 'dt-var-exp-quant', 'e-matching', 'elim-ext-arith-quant', 'elim-taut-quant', 'finite-model-find']
boolean_solver_options += ['fmf-bound', 'fmf-bound-int', 'fmf-bound-lazy', 'fmf-empty-sorts', 'fmf-fmc-simple', 'fmf-fresh-dc', 'fmf-fun', 'fmf-fun-rlv', 'fmf-inst-engine', 'fmf-inst-gen', 'fmf-inst-gen-one-quant-per-round', 'fs-interleave', 'full-saturate-quant', 'full-saturate-quant-rd', 'global-negate', 'ho-matching', 'ho-matching-var-priority', 'ho-merge-term-db', 'increment-triggers', 'infer-arith-trigger-eq', 'infer-arith-trigger-eq-exp', 'inst-level-input-only', 'inst-no-entail', 'inst-no-model-true', 'inst-prop', 'inst-when-strict-interleave', 'inst-when-tc-first', 'int-wf-ind', 'ite-dtt-split-quant', 'local-t-ext', 'lte-partial-inst', 'lte-restrict-inst-closure', 'macros-quant', 'mbqi-interleave', 'mbqi-one-inst-per-round', 'mbqi-one-quant-per-round', 'min-synth-sol', 'miniscope-quant', 'miniscope-quant-fv', 'multi-trigger-cache', 'multi-trigger-linear', 'multi-trigger-priority', 'multi-trigger-when-single', 'partial-triggers', 'pre-skolem-quant', 'pre-skolem-quant-agg', 'pre-skolem-quant-nested', 'prenex-quant-user', 'pure-th-triggers', 'purify-dt-triggers', 'purify-triggers', 'qcf-all-conflict', 'qcf-eager-check-rd', 'qcf-eager-test', 'qcf-nested-conflict', 'qcf-skip-rd', 'qcf-tconstraint', 'qcf-vo-exp', 'quant-alpha-equiv', 'quant-anti-skolem', 'quant-cf', 'quant-epr', 'quant-epr-match', 'quant-fun-wd', 'quant-ind', 'quant-model-ee', 'quant-split', 'register-quant-body-terms', 'relational-triggers', 'relevant-triggers', 'rewrite-rules', 'rr-one-inst-per-round', 'strict-triggers', 'sygus-add-const-grammar', 'sygus-auto-unfold', 'sygus-bool-ite-return-const', 'sygus-crepair-abort', 'sygus-eval-opt', 'sygus-eval-unfold', 'sygus-eval-unfold-bool', 'sygus-ext-rew', 'sygus-grammar-norm', 'sygus-inference', 'sygus-inv-templ-when-sg', 'sygus-min-grammar', 'sygus-pbe', 'sygus-pbe-multi-fair', 'sygus-qe-preproc', 'sygus-ref-eval', 'sygus-repair-const', 'sygus-rr', 'sygus-rr-synth', 'sygus-rr-synth-accel', 'sygus-rr-synth-check', 'sygus-rr-synth-filter-cong', 'sygus-rr-synth-filter-match', 'sygus-rr-synth-filter-order', 'sygus-rr-verify', 'sygus-rr-verify-abort', 'sygus-sample-fp-uniform', 'sygus-sample-grammar', 'sygus-stream', 'sygus-templ-embed-grammar', 'sygus-unif', 'sygus-verify-subcall', 'track-inst-lemmas', 'var-elim-quant', 'var-ineq-elim-quant', 'sep-check-neg', 'sep-child-refine', 'sep-deq-c', 'sep-exp', 'sep-min-refine', 'sep-pre-skolem-emp', 'sets-ext', 'sets-infer-as-lemmas', 'sets-proxy-lemmas', 'sets-rel-eager', 'abstract-values', 'check-models', 'check-proofs', 'check-synth-sol', 'check-unsat-cores', 'cpu-time', 'dump-instantiations', 'dump-models', 'dump-proofs', 'dump-synth', 'dump-unsat-cores', 'dump-unsat-cores-full', 'ext-rew-prep', 'ext-rew-prep-agg', 'force-no-limit-cpu-while-dump', 'hard-limit', 'incremental', 'ite-simp', 'model-u-dt-enum', 'omit-dont-cares', 'on-repeat-ite-simp', 'produce-assertions', 'produce-assignments', 'produce-models', 'produce-unsat-assumptions', 'produce-unsat-cores', 'proof', 'repeat-simp']
boolean_solver_options += ['rewrite-apply-to-const', 'simp-ite-compress', 'simp-with-care', 'solve-real-as-int=N', 'sort-inference', 'static-learning', 'sygus-print-callbacks', 'symmetry-breaker-exp', 'synth-rr-prep', 'synth-rr-prep-ext-rew', 'unconstrained-simp', 'strings-abort-loop', 'strings-binary-csp', 'strings-check-entail-len', 'strings-eager', 'strings-eager-len', 'strings-eit', 'strings-exp', 'strings-fmf', 'strings-guess-model', 'strings-infer-as-lemmas', 'strings-infer-sym', 'strings-inm', 'strings-lazy-pp', 'strings-len-geqz', 'strings-len-norm', 'strings-lprop-csp', 'strings-min-prefix-explain', 'strings-print-ascii', 'strings-process-loop', 'strings-rexplain-lemmas', 'strings-sp-emp', 'strings-uf-reduct', 'assign-function-values', 'condense-function-values', 'symmetry-breaker', 'uf-ho', 'uf-ho-ext', 'uf-ss-clique-splits', 'uf-ss-eager-split', 'uf-ss-fair', 'uf-ss-fair-monotone', 'uf-ss-regions', 'uf-ss-totality', 'uf-ss-totality-sym-break', 'solve-real-as-int'] 

def bool_fuzz(logic, want_stats, option_fuzzing):
    n_push = 0
    n_pop = 0

    a, b, c, ni, e, f, g, h, m, v, r, t, u, gen_arr, add_ints, add_reals = set_logic(logic, option_fuzzing)
    nodes = Nodes(add_ints, add_reals)

    assertions = random.randrange(0, 100)
    while assertions > 0:

        if n_push > n_pop:
            if random.random() < 0.1:
                nodes.pop()
                n_pop += 1
            elif random.random() < 0.1:
                nodes.push()
                n_push += 1
        if n_push == n_pop:
            if random.random() < 0.1:
                nodes.push()
                n_push += 1

        if random.random() < 0.2:
            prob = random.random()
            if prob < a:
                nodes.newSort()
            elif prob < b:
                nodes.varUSort()
            elif prob < c:
                nodes.bool_from_usort()
    
        if random.random() < 0.33:
            nodes.new_bool()
        if random.random() < ni:
            nodes.new_int()
        if random.random() < e:
            nodes.int_from_int()
        if random.random() < f:
            nodes.bool_from_int()
        if random.random() < g:
            nodes.new_real()
        if random.random() < h:
            nodes.real_from_real()
        if random.random() < m:
            nodes.bool_from_real()
        if random.random() < v:
            nodes.real_and_int()
        if random.random() < r:
            nodes.new_BV()
        if random.random() < t:
            nodes.BV_from_BV()
        if random.random() < u:
            nodes.bool_from_BV()
        if random.random() < gen_arr:
            nodes.new_array(logic)
        if random.random() < gen_arr:
            nodes.array_from_array()
        if random.random() < gen_arr:
            nodes.bool_from_array()

        if random.random() < 0.5:
            new_node = nodes.bool_choice()    
        else:
            new_node = nodes.bool_from_bool()

        if random.random() < 0.4:
            print('(assert {})'.format(new_node))
            assertions -= 1
    
        if random.random() < 0.05:
            print('(check-sat)')

    if want_stats == 1:
        nodes.boolean_stats()

def cnf_fuzz(logic, vcratio, option_fuzzing):
    n_push = 0
    n_pop = 0

    a, b, c, ni, e, f, g, h, m, v, r, t, u, gen_arr, add_ints, add_reals = set_logic(logic, option_fuzzing)
    nodes = Nodes(add_ints, add_reals)

    for i in range(200):

        if n_push > n_pop:
            if random.random() < 0.1:
                nodes.pop()
                n_pop += 1
            elif random.random() < 0.1:
                nodes.push()
                n_push += 1
        if n_push == n_pop:
            if random.random() < 0.1:
                nodes.push()
                n_push += 1

        if random.random() < 0.2:
            prob = random.random()
            if prob < a:
                nodes.newSort()
            elif prob < b:
                nodes.varUSort()
            elif prob < c:
                nodes.bool_from_usort()
    
        if random.random() < 0.33:
            nodes.new_bool()
        if random.random() < ni:
            nodes.new_int()
        if random.random() < e:
            nodes.int_from_int()
        if random.random() < f:
            nodes.bool_from_int()
        if random.random() < g:
            nodes.new_real()
        if random.random() < h:
            nodes.real_from_real()
        if random.random() < m:
            nodes.bool_from_real()
        if random.random() < v:
            nodes.real_and_int()
        if random.random() < r:
            nodes.new_BV()
        if random.random() < t:
            nodes.BV_from_BV()
        if random.random() < u:
            nodes.bool_from_BV()
        if random.random() < 0.33:
            nodes.bool_from_bool()
        if random.random() < gen_arr:
            nodes.new_array(logic)
        if random.random() < gen_arr:
            nodes.array_from_array()
        if random.random() < gen_arr:
            nodes.bool_from_array()

    upp_b = nodes.num_bool()
    n_variables, n_clauses = Ratio(1, upp_b, vcratio)
    bank = nodes.bool_sample(n_variables)
    clauses = Clauses(bank, n_clauses)
    clauses.new_cnfs()

def ncnf_fuzz(logic, vcratio, option_fuzzing):
    n_push = 0
    n_pop = 0

    a, b, c, ni, e, f, g, h, m, v, r, t, u, gen_arr, add_ints, add_reals = set_logic(logic, option_fuzzing)
    nodes = Nodes(add_ints, add_reals)

    for i in range(200):

        if n_push > n_pop:
            if random.random() < 0.1:
                nodes.pop()
                n_pop += 1
            elif random.random() < 0.1:
                nodes.push()
                n_push += 1
        if n_push == n_pop:
            if random.random() < 0.1:
                nodes.push()
                n_push += 1

        if random.random() < 0.2:
            prob = random.random()
            if prob < a:
                nodes.newSort()
            elif prob < b:
                nodes.varUSort()
            elif prob < c:
                nodes.bool_from_usort()
    
        if random.random() < 0.33:
            nodes.new_bool()
        if random.random() < ni:
            nodes.new_int()
        if random.random() < e:
            nodes.int_from_int()
        if random.random() < f:
            nodes.bool_from_int()
        if random.random() < g:
            nodes.new_real()
        if random.random() < h:
            nodes.real_from_real()
        if random.random() < m:
            nodes.bool_from_real()
        if random.random() < v:
            nodes.real_and_int()
        if random.random() < r:
            nodes.new_BV()
        if random.random() < t:
            nodes.BV_from_BV()
        if random.random() < u:
            nodes.bool_from_BV()
        if random.random() < 0.33:
            nodes.bool_from_bool()
        if random.random() < gen_arr:
            nodes.new_array(logic)
        if random.random() < gen_arr:
            nodes.array_from_array()
        if random.random() < gen_arr:
            nodes.bool_from_array()

    upp_b = nodes.num_bool()
    n_variables, n_clauses = Ratio(1, upp_b, vcratio)
    bank = nodes.bool_sample(n_variables)
    clauses = Clauses(bank, n_clauses)
    clauses.new_dist_cnfs()

def CNFexp_fuzz(logic, vcratio, option_fuzzing):
    n_push = 0
    n_pop = 0

    a, b, c, ni, e, f, g, h, m, v, r, t, u, gen_arr, add_ints, add_reals = set_logic(logic, option_fuzzing)
    nodes = Nodes(add_ints, add_reals)

    for i in range(200):

        if n_push > n_pop:
            if random.random() < 0.1:
                nodes.pop()
                n_pop += 1
            elif random.random() < 0.1:
                nodes.push()
                n_push += 1
        if n_push == n_pop:
            if random.random() < 0.1:
                nodes.push()
                n_push += 1

        if random.random() < 0.2:
            prob = random.random()
            if prob < a:
                nodes.newSort()
            elif prob < b:
                nodes.varUSort()
            elif prob < c:
                nodes.bool_from_usort()
    
        if random.random() < 0.33:
            nodes.new_bool()
        if random.random() < ni:
            nodes.new_int()
        if random.random() < e:
            nodes.int_from_int()
        if random.random() < f:
            nodes.bool_from_int()
        if random.random() < g:
            nodes.new_real()
        if random.random() < h:
            nodes.real_from_real()
        if random.random() < m:
            nodes.bool_from_real()
        if random.random() < v:
            nodes.real_and_int()
        if random.random() < r:
            nodes.new_BV()
        if random.random() < t:
            nodes.BV_from_BV()
        if random.random() < u:
            nodes.bool_from_BV()
        if random.random() < 0.33:
            nodes.bool_from_bool()
        if random.random() < gen_arr:
            nodes.new_array(logic)
        if random.random() < gen_arr:
            nodes.array_from_array()
        if random.random() < gen_arr:
            nodes.bool_from_array()

    upp_b = nodes.num_bool()
    n_variables, n_clauses = Ratio(1, upp_b, vcratio)
    bank = nodes.bool_sample(n_variables)
    clauses = Clauses(bank, n_clauses)
    clauses.new_cnfs()

    assertions = random.randrange(0, 100)
    while assertions > 0:

        if random.random() < 0.5:
            new_node = clauses.cnf_choice()
        else:
            new_node = clauses.node_from_cnf()

        if random.random() < 0.6:
            print('(assert {})'.format(new_node))
            assertions -= 1

        if random.random() < 0.2:
            node1, node2 = clauses.bin_node()
            print('(assert {})'.format(node1))
            print('(assert {})'.format(node2))
            assertions -= 2

        if random.random() < 0.05:
            print('(check-sat)')

parser = argparse.ArgumentParser()
parser.add_argument('--strategy', dest='strategy', default='bool', type=str)
parser.add_argument('--logic', dest='logic', default='random', type=str)
parser.add_argument('--seed', dest='seed', default=None)
parser.add_argument('--stats', action='store_true')
parser.add_argument('--cnfratio', dest='ratio', default=5, type=int)
parser.add_argument('--disable', dest='disable', default='none', type=str)
args = parser.parse_args()

option_fuzzing = 1
if args.disable == 'option_fuzzing':
    option_fuzzing = 0

if args.seed != None:
    random.seed(args.seed)

want_stats = 0
if args.stats == True:
    want_stats = 1

if args.strategy == 'bool':
    bool_fuzz(args.logic, want_stats, option_fuzzing)
if args.strategy == 'cnf':
    cnf_fuzz(args.logic, args.ratio, option_fuzzing)
if args.strategy == 'ncnf':
    ncnf_fuzz(args.logic, args.ratio, option_fuzzing)
if args.strategy == 'CNFexp':
    CNFexp_fuzz(args.logic, args.ratio, option_fuzzing)

print("(check-sat)")
print("(exit)")
