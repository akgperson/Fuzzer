import math
import random
from collections import OrderedDict

print('(set-logic ALL)')
print('(set-option :incremental true)')

class Op:
    def __init__(self, node, expr):
        self.expr = expr
        self.node = node

    def __repr__(self):
        return '({} {})'.format(self.node, self.expr)

class Var:
    def __init__(self, sort, n):
        self.sort = sort
        self.n = n
    def __repr__(self):
        return str(self.sort) + str(self.n)

class Var_Bool(Var):
    def __init__(self, n):
        Var.__init__(self, 'v', n)

class Var_Int(Var):
    def __init__(self, n):
        Var.__init__(self, 'i', n)

class Var_Real(Var):
    def __init__(self, n):
        Var.__init__(self, 'r', n)

class Var_UnIntSort(Var):
    def __init__(self, sort, n):
        Var.__init__(self, sort, n)
    def __repr__(self):
        return '{}-{}'.format(self.sort, self.n)

class Var_BV(Var):
    def __init__(self, sort, n):
        Var.__init__(self, sort, n)
    def __repr__(self):
        return 'bv_{}-{}'.format(self.sort, self.n)

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

class Clauses():
    def __init__(self, b):
        self.clauses = []
        self.unused_options = list(b)
        self.all_options = list(b)

    def new_cnfs(self):
        for i in range(n_clauses):
            cnf = "(or "
            for j in range(2):
                n_left = ((n_clauses-i)*3) + (3-j)
                if len(self.unused_options) == n_left:
                    addition = random.choice(self.unused_options)
                    cnf += (str(addition) + " ")
                    self.unused_options.remove(addition)
                else:
                    addition = random.choice(self.all_options)
                    cnf += (str(addition) + " ")
                    if addition in self.unused_options:
                        self.unused_options.remove(addition)
            n_left = ((n_clauses-i)*3) + (3-j)
            if len(self.unused_options) == n_left:
                addition = random.choice(self.unused_options)
                cnf += (str(addition) + ")")
            else:
                addition = random.choice(self.all_options)
                cnf += (str(addition) + ")")
            self.clauses.append(cnf)
#            print('(assert ' + cnf + ')')

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

class Nodes:
    def __init__(self):
        self.d = OrderedDict()
        self.d[Bool()] = []
        self.d[Int()] = []
        self.d[Real()] = []

        self.new_keys = []
        self.indices = []

        self.n_vars = random.randint(1, 20)
        for i in range(self.n_vars):
            self.d[Bool()].append(Var_Bool(i)) 
            print('(declare-const {} Bool)'.format(Var_Bool(i)))
        self.n_ints = random.randint(1, 20)
        for i in range(self.n_ints):
            if random.random() < 0.5:
                self.d[Int()].append(Var_Int(i))
                print('(declare-const {} Int)'.format(Var_Int(i)))
            else:
                val = random.randint(0, 100)
                self.d[Int()].append(val)
        self.n_reals = random.randint(1, 20)
        for i in range(self.n_reals):
            if random.random() < 0.5:
                self.d[Real()].append(Var_Real(i))
                print('(declare-const {} Real)'.format(Var_Real(i)))
            else:
                new_real = random_real()
                self.d[Real()].append(new_real)
    
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
            print('(declare-const {} {})'.format(Var_UnIntSort(current_sort, n), current_sort))

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
            items = str(random.choice(self.d[current_sort]))
            for i in range(n_items):
                items += (" " + str(random.choice(self.d[current_sort])))
            if random.random() < 0.5:
                new_bool = '(= {})'.format(items)
            else:
                new_bool = '(distinct {})'.format(items)
            self.d[Bool()].append(new_bool)            

    def new_bool(self):
        new_var = Var_Bool(self.n_vars)
        print('(declare-const {} Bool)'.format(new_var))
        self.n_vars += 1
        self.d[Bool()].append(new_var)

    def new_int(self):
        if random.random() < 0.3:
            new_int = Var_Int(self.n_ints)
            print('(declare-const {} Int)'.format(new_int))
            self.n_ints += 1
            self.d[Int()].append(new_int)
        else:
            new_int = random.randint(0, 1000)
            self.d[Int()].append(new_int)

    def int_from_int(self):
        p = random.random()
        if p < 0.4:
            self.d[Int()].append(Op(random.choice(IntUnOp), random.choice(self.d[Int()])))
        elif p < 0.66:
            operand = str(random.choice(self.d[Int()])) 
            operand += (" " + str(random.choice(self.d[Int()])))
            self.d[Int()].append(Op(random.choice(IntBinOp), operand))    
        else:
            operand = str(random.choice(self.d[Int()]))
            n = random.randrange(1, 5)
            for i in range(n):
                operand += (" " + str(random.choice(self.d[Int()])))
            self.d[Int()].append(Op(random.choice(IntNOp), operand))

    def bool_from_int(self):
        #can you choose multiple operands? chainable?
        operand = str(random.choice(self.d[Int()])) 
        operand += (" " + str(random.choice(self.d[Int()])))
        new_bool = Op(random.choice(IRNBoolOp), operand)
        self.d[Bool()].append(new_bool)
        #want to add possibility of asserting this bool here?

    def new_real(self):
        if random.random() < 0.5:
            self.d[Real()].append(Var_Real(self.n_reals))
            print('(declare-const {} Real)'.format(Var_Real(self.n_reals)))
            self.n_reals += 1
        else:
            new_real = random_real()
            self.d[Real()].append(new_real)

    def real_from_real(self):
        chance = random.random()
        if chance < 0.33: #unary
            self.d[Real()].append(Op("-", random.choice(self.d[Real()])))
        elif chance < 0.67: #binary
            operands = str(random.choice(self.d[Real()])) 
            operands += (" " + str(random.choice(self.d[Real()])))
            self.d[Real()].append(Op("/", operands))
        else: #n-array
            operands = str(random.choice(self.d[Real()]))
            x = random.randrange(1, 5)
            for i in range(x):
                operands += (" " + str(random.choice(self.d[Real()])))
            self.d[Real()].append(Op(random.choice(RealNOp), operands))

    def bool_from_real(self):
        #n-array or binary?
        operands = str(random.choice(self.d[Real()]))
        n_operands = random.randrange(1, 5)
        for i in range(n_operands):
            operands += (" " + str(random.choice(self.d[Real()])))
        new_bool = Op(random.choice(IRNBoolOp), operands)
        self.d[Bool()].append(new_bool)
        #give possibility of asserting this new bool here?
    
    def real_and_int(self):
        chance = random.randint(1, 3)
        if chance == 1:
            self.d[Real()].append(Op("to_real", random.choice(self.d[Int()])))
        elif chance == 2:
            self.d[Int()].append(Op("to_int", random.choice(self.d[Real()])))
        else:
            self.d[Bool()].append(Op("is_int", random.choice(self.d[Real()])))

    def new_BV(self):
        if random.random() < 0.25:
            width = random.randint(1, 30)
            bv_sort = BV(width)
            if bv_sort not in self.d.keys():
                self.d[bv_sort] = [] 
            const = Var_BV(width, len(self.d[bv_sort])) 
            print('(declare-const {} (_ BitVec {}))'.format(const, width))
            self.d[bv_sort].append(const) 
        else:
            bv, width = random_BV()
            bv_sort = BV(width)
            if bv_sort not in self.d.keys():
                self.d[bv_sort] = []
            self.d[bv_sort].append(bv)

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
                operand = str(random.choice(self.d[s])) + " " + str(random.choice(self.d[s2])) 
                new_BV = Op("concat", operand)
                bv_sort = BV(width)
                if bv_sort not in self.d.keys():
                    self.d[bv_sort] = []
                self.d[bv_sort].append(new_BV) 

            elif prob < 0.1: #repeat
                i = random.randint(1, 10)
                width = i * s.w
                operator = '(_ repeat {})'.format(i)
                new_BV = Op(operator, random.choice(self.d[s])) 
                bv_sort = BV(width)
                if bv_sort not in self.d.keys():
                    self.d[bv_sort] = []
                self.d[bv_sort].append(new_BV) 

            elif prob < 0.2: #unary, extract
                if random.random() < 0.5: #unary
                    new_BV = Op(random.choice(Un_BV_BV), random.choice(self.d[s]))
                    self.d[s].append(new_BV)
                else: #extract
                    width = s.w
                    parameter1 = random.randrange(0, width)
                    parameter2 = random.randint(0, parameter1)
                    operator = "(_ extract {} {})".format(parameter1, parameter2)
                    new_width = parameter1 - parameter2 + 1 
                    new_BV = Op(operator, random.choice(self.d[s]))    
                    bv_sort = BV(new_width)
                    if bv_sort not in self.d.keys():
                        self.d[bv_sort] = []
                    self.d[bv_sort].append(new_BV) 

            elif prob < 0.3:
                i = random.randint(0, 10)
                if random.random() < 0.5:
                    if random.random() < 0.5:
                        operator = "(_ zero_extend {})".format(i)
                    else:
                        operator = "(_ sign_extend {})".format(i)
                    width = s.w + i
                    new_BV = Op(operator, random.choice(self.d[s]))
                    bv_sort = BV(width)
                    if bv_sort not in self.d.keys():
                        self.d[bv_sort] = []
                    self.d[bv_sort].append(new_BV) 
                else:
                    if random.random() < 0.5:
                        operator = "(_ rotate_left {})".format(i)
                    else:
                        operator = "(_ rotate_right {})".format(i)
                    new_BV = Op(operator, random.choice(self.d[s]))
                    self.d[s].append(new_BV)

            elif prob < 0.4: #n-array
                a = random.randint(1, 3)
                operand = str(random.choice(self.d[s]))
                for i in range(a):
                    operand += (" " + str(random.choice(self.d[s])))
                new_BV = Op(random.choice(N_BV_BV), operand)
                self.d[s].append(new_BV)

            else: #binary
                operand = str(random.choice(self.d[s])) + " " + str(random.choice(self.d[s]))
                operator = random.choice(Bin_BV_BV)
                new_BV = Op(operator, operand)
                if operator == "bvcomp":
                    if BV(1) not in self.d.keys():
                        self.d[BV(1)] = []
                    self.d[BV(1)].append(new_BV)
                else:
                    self.d[s].append(new_BV)

    def bool_from_BV(self):
        options = []
        for o in list(self.d):
            if type(o) is BV:
                options.append(o) 
        if len(options) > 0:
            s = random.choice(options)
            if random.random() < 0.33:
                operand = str(random.choice(self.d[s])) + " " + str(random.choice(self.d[s]))
                new_bool = Op(random.choice(Bin_BV_Bool), operand)
            else:
                operand = str(random.choice(self.d[s]))
                n = random.randint(1, 4)
                for i in range(n):
                    operand += (" " + str(random.choice(self.d[s])))
                new_bool = Op(random.choice(N_BV_Bool), operand)
            self.d[Bool()].append(new_bool)

    def bool_from_bool(self):
        p = random.randint(1, 7)
        if p == 1:
            #pick Unary
            new_bool = Op(random.choice(UnOp), random.choice(self.d[Bool()]))
        elif p == 2:
            #pick Binary
            operand = ""
            operand = str(random.choice(self.d[Bool()]))
            operand += (" " + str(random.choice(self.d[Bool()])))
            new_bool = Op(random.choice(BiOp), operand)
        else:    
            n_operands = random.randint(1, 10)
            operands = ""
            operands = str(random.choice(self.d[Bool()]))
            for i in range(n_operands):
                operands += (" " + str(random.choice(self.d[Bool()])))
            new_bool = Op(random.choice(NarOp), operands)
        self.d[Bool()].append(new_bool)
        return new_bool

    def bool_choice(self):
        return random.choice(self.d[Bool()])

    def num_bool(self):
        return min(len(self.d[Bool()]), 20)

    def bool_sample(self):
        bool_idx = random.sample(range(len(self.d[Bool()])), n_variables)
        sample = []
        for x in bool_idx:
            sample.append(self.d[Bool()][x])
        return sample

n_push = 0
n_pop = 0

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

nodes = Nodes()
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
        if prob < 0.33:
            nodes.newSort()
        elif prob < 0.66:
            nodes.varUSort()
        else:
            nodes.bool_from_usort()
    
    if random.random() < 0.33:
        nodes.new_bool()
    if random.random() < 0.33:
        nodes.new_int()
    if random.random() < 0.33:
        nodes.int_from_int()
    if random.random() < 0.33:
        nodes.bool_from_int()
    if random.random() < 0.33:
        nodes.new_real()
    if random.random() < 0.33:
        nodes.real_from_real()
    if random.random() < 0.33:
        nodes.bool_from_real()
    if random.random() < 0.33:
        nodes.real_and_int()
    if random.random() < 0.33:
        nodes.new_BV()
    if random.random() < 0.33:
        nodes.BV_from_BV()
    if random.random() < 0.33:
        nodes.bool_from_BV()
    if random.random() < 0.33:
        nodes.bool_from_bool()

upp_b = nodes.num_bool()
n_variables, n_clauses = Ratio(1, upp_b, 5)
bank = nodes.bool_sample()
clauses = Clauses(bank)
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

    if random.random() < 0.05:
        print('(check-sat)')

print("(check-sat)")
print("(exit)")
