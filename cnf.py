import math
import random
from collections import OrderedDict

print("(set-logic ALL)")
print('(set-option :incremental true)')

class Var:
    def __init__(self, n):
        self.n = n

    def __repr__(self):
        return 'v' + str(self.n)

class Op:
    def __init__(self, node, expr):
        self.expr = expr
        self.node = node

    def __repr__(self):
        return '({} {})'.format(self.node, self.expr)

class UnintSort:
    def __init__(self, n):
        self.n = n

    def __repr__(self):
        return 'S' + str(self.n)

#gives variables within a sort
class sVar:
    def __init__(self, sort, n):
        self.sort = sort
        self.n = n

    def __repr__(self):
        return '{}-{}'.format(self.sort, self.n)

class Ints:
    def __init__(self, n):
        self.n = n

    def __repr__(self):
        return 'i' + str(self.n)

class Reals:
    def __init__(self, n):
        self.n = n

    def __repr__(self):
        return 'r' + str(self.n)

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

n_unintsorts = 0

UnOp = ["not"]
BiOp = ["=>"]
NarOp = ["and", "or", "xor", "=", "distinct"]
IntUnOp = ["-", "abs"]
IntBinOp = ["div", "mod"]
IntNOp = ["-", "+", "*"]
IRNBoolOp = ["<=", "<", ">=", ">", "=", "distinct"]
RealNOp = ["-", "+", "*"]


n_vars = random.randint(1, 20)

#create a dictionary for all Sorts and add key Bool that will hold all boolean variables
d = OrderedDict()
d['Bool'] = []
d['Int'] = []
d['Real'] = []

for i in range(n_vars):
    d['Bool'].append(Var(i)) 
    print('(declare-const {} Bool)'.format(Var(i)))

n_ints = random.randint(1, 20)
for i in range(n_ints):
    if random.random() < 0.5:
        d['Int'].append(Ints(i))
        print('(declare-const {} Int)'.format(Ints(i)))
    else:
        val = random.randint(0, 100)
        d['Int'].append(val)

n_reals = random.randint(1, 20)
for i in range(n_reals):
    if random.random() < 0.5:
        d['Real'].append(Reals(i))
        print('(declare-const {} Real)'.format(Reals(i)))
    else:
        new_real = random_real()
        d['Real'].append(new_real)

new_keys = []

for i in range(200):

    if random.random() < 0.2:
        prob = random.random()
        #declare new Sort
        if prob < 0.33 and n_unintsorts < 4:
            current_sort = UnintSort(n_unintsorts)
            n_unintsorts += 1 
            print('(declare-sort {} 0)'.format(current_sort))
            d[current_sort] = []
        #add new variable to an existing sort
        elif prob < 0.66:
            options = list(d)
            options.remove('Bool')
            options.remove('Int')
            options.remove('Real')
            if len(options) > 0:
                current_sort = random.choice(options)
                n = len(d[current_sort])
                d[current_sort].append(sVar(current_sort, n))
                print('(declare-const {} {})'.format(sVar(current_sort, n), current_sort))
        #create a boolean expression using two variables in the same sort and add to Bool list
        else:
            options = []
            ops = list(d)
            ops.remove('Bool')
            ops.remove('Int')
            ops.remove('Real')
            for things in ops:
                if len(d[things]) > 0:
                    options.append(things)
            if len(options) > 0:
                current_sort = random.choice(options)
                n_items = random.randrange(1, 5)
                items = str(random.choice(d[current_sort]))
                for i in range(n_items):
                    items += (" " + str(random.choice(d[current_sort])))
                if random.random() < 0.5:
                    new_bool = '(= {})'.format(items)
                else:
                    new_bool = '(distinct {})'.format(items)
                d['Bool'].append(new_bool)            

    #create a new variable
    if random.random() < 0.5: #new bool
        new_var = Var(n_vars)
        print('(declare-const {} Bool)'.format(new_var))
        n_vars += 1
        d['Bool'].append(new_var)
    if random.random() < 0.5: #new int
        if random.random() < 0.3:
            new_int = Ints(n_ints)
            print('(declare-const {} Int)'.format(new_int))
            n_ints += 1
            d['Int'].append(new_int)
        else:
            new_int = random.randint(0, 1000)
            d['Int'].append(new_int)
    if random.random() < 0.5: #new int by exp
        p = random.random()
        if p < 0.4:
            d['Int'].append(Op(random.choice(IntUnOp), random.choice(d['Int'])))
        elif p < 0.66:
            operand = str(random.choice(d['Int'])) 
            operand += (" " + str(random.choice(d['Int'])))
            d['Int'].append(Op(random.choice(IntBinOp), operand))    
        else:
            operand = str(random.choice(d['Int']))
            n = random.randrange(1, 5)
            for i in range(n):
                operand += (" " + str(random.choice(d['Int'])))
            d['Int'].append(Op(random.choice(IntNOp), operand))
    if random.random() < 0.5: #new boolean
        #can you choose multiple operands? chainable?
        operand = str(random.choice(d['Int'])) 
        operand += (" " + str(random.choice(d['Int'])))
        new_bool = Op(random.choice(IRNBoolOp), operand)
        d['Bool'].append(new_bool)
        #want to add possibility of asserting this bool here?
    if random.random() < 0.5: #new real
        if random.random() < 0.5:
            d['Real'].append(Reals(n_reals))
            print('(declare-const {} Real)'.format(Reals(n_reals)))
            n_reals += 1
        else:
            new_real = random_real()
            d['Real'].append(new_real)
    if random.random() < 0.5: #new real from expression
        chance = random.random()
        if chance < 0.33: #unary
            d['Real'].append(Op("-", random.choice(d['Real'])))
        elif chance < 0.67: #binary
            operands = str(random.choice(d['Real'])) 
            operands += (" " + str(random.choice(d['Real'])))
            d['Real'].append(Op("/", operands))
        else: #n-array
            operands = str(random.choice(d['Real']))
            x = random.randrange(1, 5)
            for i in range(x):
                operands += (" " + str(random.choice(d['Real'])))
            d['Real'].append(Op(random.choice(RealNOp), operands))
    if random.random() < 0.5: #new bool from reals
        #n-array or binary?
        operands = str(random.choice(d['Real']))
        n_operands = random.randrange(1, 5)
        for i in range(n_operands):
            operands += (" " + str(random.choice(d['Real'])))
        new_bool = Op(random.choice(IRNBoolOp), operands)
        d['Bool'].append(new_bool)
        #give possibility of asserting this new bool here?
    if random.random() < 0.33: #real and int
        chance = random.randint(1, 3)
        if chance == 1:
            d['Real'].append(Op("to_real", random.choice(d['Int'])))
        elif chance == 2:
            d['Int'].append(Op("to_int", random.choice(d['Real'])))
        else:
            d['Bool'].append(Op("is_int", random.choice(d['Real'])))

    if random.random() < 0.1:
        p = random.randint(1, 7)
        if p == 1:
            #pick Unary
            new_node = Op(random.choice(UnOp), random.choice(d['Bool']))
        elif p == 2:
            #pick Binary
            operand = ""
            operand = str(random.choice(d['Bool']))
            operand += (" " + str(random.choice(d['Bool'])))
            new_node = Op(random.choice(BiOp), operand)
        else:    
            #choose number operands
            n_operands = random.randint(1, 10)
            #choose operands and put into string
            operands = ""
            operands = str(random.choice(d['Bool']))
            for i in range(n_operands):
                operands += (" " + str(random.choice(d['Bool'])))
            new_node = Op(random.choice(NarOp), operands)

        if str(new_node) not in d['Bool']:
            d['Bool'].append(new_node)


var_ratio = 5
cnfs = []
unused_booleans = []
all_booleans = []
n_variables = random.randint(1, 20)
n_3cnf = math.ceil(var_ratio * n_variables)

choices = d['Bool']
for i in range(n_variables):
    choice = random.choice(choices)
    unused_booleans.append(choice)
    all_booleans.append(choice)
    choices.remove(choice)

for i in range(n_3cnf):
    length_cnf = 3
    cnf = "(or "
    for j in range(length_cnf - 1):
        n_left = ((n_3cnf-i)*3) + (3-j)
        if len(unused_booleans) == n_left:
            addition = random.choice(unused_booleans)
            cnf += (str(addition) + " ")
            unused_booleans.remove(addition)
        else:
            addition = random.choice(all_booleans)
            cnf += (str(addition) + " ")
            if addition in unused_booleans:
                unused_booleans.remove(addition)
    if len(unused_booleans) == n_left:
        addition = random.choice(unused_booleans)
        cnf += (str(addition) + ")")
        unused_booleans.remove(addition)
    else:
        addition = random.choice(all_booleans)
        cnf += (str(addition) + ")")
        if addition in unused_booleans:
            unused_booleans.remove(addition)
    print('(assert ' + cnf + ')')

print("(check-sat)")
print("(exit)")
