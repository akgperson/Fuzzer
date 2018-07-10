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

class Sort:
    def __init__(self, sort, n):
        self.sort = sort        
        self.n = n
    def __repr__(self):
        return str(self.sort) + str(self.n)

class Bool(Sort):
    def __init__(self, n):
        Sort.__init__(self, 'v', n)

class Int(Sort):
    def __init__(self, n):
        Sort.__init__(self, 'i', n)

class Real(Sort):
    def __init__(self, n):
        Sort.__init__(self, 'r', n)

class newUSort(Sort):
    def __init__(self, n):
        Sort.__init__(self, 'S', n)

class UnIntSort(Sort):
    def __init__(self, sort, n):
        Sort.__init__(self, sort, n)
    def __repr__(self):
        return '{}-{}'.format(self.sort, self.n)

class BVSort(Sort):
    def __init__(self, width, n):
        Sort.__init__(self, width, n)
    def __repr__(self):
        return'bv{}-{}'.format(self.sort, self.n)

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

class Nodes:
    def __init__(self):
        self.d = OrderedDict()
        self.d['Bools'] = []
        self.d['Ints'] = []
        self.d['Reals'] = []

        self.new_keys = []
        self.indices = []

        self.n_vars = random.randint(1, 20)
        for i in range(self.n_vars):
            self.d['Bools'].append(Bool(i)) 
            print('(declare-const {} Bool)'.format(Bool(i)))
        self.n_ints = random.randint(1, 20)
        for i in range(self.n_ints):
            if random.random() < 0.5:
                self.d['Ints'].append(Int(i))
                print('(declare-const {} Int)'.format(Int(i)))
            else:
                val = random.randint(0, 100)
                self.d['Ints'].append(val)
        self.n_reals = random.randint(1, 20)
        for i in range(self.n_reals):
            if random.random() < 0.5:
                self.d['Reals'].append(Real(i))
                print('(declare-const {} Real)'.format(Real(i)))
            else:
                new_real = random_real()
                self.d['Reals'].append(new_real)
    
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
        global n_unintsorts
        current_sort = newUSort(n_unintsorts)
        n_unintsorts += 1
        print('(declare-sort {} 0)'.format(current_sort))
        self.d[current_sort] = []
    
    def varUSort(self):
        options = list(self.d)
        options.remove('Bools')
        options.remove('Ints')
        options.remove('Reals')
        if len(options) > 0:
            current_sort = random.choice(options)
            n = len(self.d[current_sort])
            self.d[current_sort].append(UnIntSort(current_sort, n))
            print('(declare-const {} {})'.format(UnIntSort(current_sort, n), current_sort))

    def bool_from_usort(self):
        options = []
        ops = list(self.d)
        ops.remove('Bools')
        ops.remove('Ints')
        ops.remove('Reals')
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
            self.d['Bools'].append(new_bool)            

    def new_bool(self):
        new_var = Bool(self.n_vars)
        print('(declare-const {} Bool)'.format(new_var))
        self.n_vars += 1
        self.d['Bools'].append(new_var)

    def new_int(self):
        if random.random() < 0.3:
            new_int = Int(self.n_ints)
            print('(declare-const {} Int)'.format(new_int))
            self.n_ints += 1
            self.d['Ints'].append(new_int)
        else:
            new_int = random.randint(0, 1000)
            self.d['Ints'].append(new_int)

    def int_from_int(self):
        p = random.random()
        if p < 0.4:
            self.d['Ints'].append(Op(random.choice(IntUnOp), random.choice(self.d['Ints'])))
        elif p < 0.66:
            operand = str(random.choice(self.d['Ints'])) 
            operand += (" " + str(random.choice(self.d['Ints'])))
            self.d['Ints'].append(Op(random.choice(IntBinOp), operand))    
        else:
            operand = str(random.choice(self.d['Ints']))
            n = random.randrange(1, 5)
            for i in range(n):
                operand += (" " + str(random.choice(self.d['Ints'])))
            self.d['Ints'].append(Op(random.choice(IntNOp), operand))

    def bool_from_int(self):
        #can you choose multiple operands? chainable?
        operand = str(random.choice(self.d['Ints'])) 
        operand += (" " + str(random.choice(self.d['Ints'])))
        new_bool = Op(random.choice(IRNBoolOp), operand)
        self.d['Bools'].append(new_bool)
        #want to add possibility of asserting this bool here?

    def new_real(self):
        if random.random() < 0.5:
            self.d['Reals'].append(Real(self.n_reals))
            print('(declare-const {} Real)'.format(Real(self.n_reals)))
            self.n_reals += 1
        else:
            new_real = random_real()
            self.d['Reals'].append(new_real)

    def real_from_real(self):
        chance = random.random()
        if chance < 0.33: #unary
            self.d['Reals'].append(Op("-", random.choice(self.d['Reals'])))
        elif chance < 0.67: #binary
            operands = str(random.choice(self.d['Reals'])) 
            operands += (" " + str(random.choice(self.d['Reals'])))
            self.d['Reals'].append(Op("/", operands))
        else: #n-array
            operands = str(random.choice(self.d['Reals']))
            x = random.randrange(1, 5)
            for i in range(x):
                operands += (" " + str(random.choice(self.d['Reals'])))
            self.d['Reals'].append(Op(random.choice(RealNOp), operands))

    def bool_from_real(self):
        #n-array or binary?
        operands = str(random.choice(self.d['Reals']))
        n_operands = random.randrange(1, 5)
        for i in range(n_operands):
            operands += (" " + str(random.choice(self.d['Reals'])))
        new_bool = Op(random.choice(IRNBoolOp), operands)
        self.d['Bools'].append(new_bool)
        #give possibility of asserting this new bool here?
    
    def real_and_int(self):
        chance = random.randint(1, 3)
        if chance == 1:
            self.d['Reals'].append(Op("to_real", random.choice(self.d['Ints'])))
        elif chance == 2:
            self.d['Ints'].append(Op("to_int", random.choice(self.d['Reals'])))
        else:
            self.d['Bools'].append(Op("is_int", random.choice(self.d['Reals'])))
    
    def bool_from_bool(self):
        p = random.randint(1, 7)
        if p == 1:
            #pick Unary
            new_bool = Op(random.choice(UnOp), random.choice(self.d['Bools']))
        elif p == 2:
            #pick Binary
            operand = ""
            operand = str(random.choice(self.d['Bools']))
            operand += (" " + str(random.choice(self.d['Bools'])))
            new_bool = Op(random.choice(BiOp), operand)
        else:    
            n_operands = random.randint(1, 10)
            operands = ""
            operands = str(random.choice(self.d['Bools']))
            for i in range(n_operands):
                operands += (" " + str(random.choice(self.d['Bools'])))
            new_bool = Op(random.choice(NarOp), operands)
        self.d['Bools'].append(new_bool)
        return new_bool

    def bool_choice(self):
        return random.choice(self.d['Bools'])

n_push = 0
n_pop = 0
n_unintsorts = 0

UnOp = ["not"]
BiOp = ["=>"]
NarOp = ["and", "or", "xor", "=", "distinct"]
IntUnOp = ["-", "abs"]
IntBinOp = ["div", "mod"]
IntNOp = ["-", "+", "*"]
IRNBoolOp = ["<=", "<", ">=", ">", "=", "distinct"]
RealNOp = ["-", "+", "*"]

nodes = Nodes()
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
        if prob < 0.33 and n_unintsorts < 4:
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

    if random.random() < 0.5:
        new_node = nodes.bool_choice()    
    else:
        new_node = nodes.bool_from_bool()

    if random.random() < 0.4:
        print('(assert {})'.format(new_node))
        assertions -= 1

    if random.random() < 0.05:
        print('(check-sat)')

print("(check-sat)")
print("(exit)")
