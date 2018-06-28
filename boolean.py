import random
from collections import OrderedDict

print("(set-logic ALL)")
print('(set-option :incremental true)')

class Var:
    def __init__(self, n):
        self.n = n

    def __repr__(self):
        return 'v' + str(self.n)

class UnaryOp:
    def __init__(self, node, expr):
        self.expr = expr
        self.node = node

    def __repr__(self):
        return '({} {})'.format(self.node, self.expr)

class BinOp:
    def __init__(self, node, expr):
        self.expr = expr
        self.node = node

    def __repr__(self):
        return '({} {})'.format(self.node, self.expr)

class NOp:
    def __init__(self, node, operands):
        self.node = node
        self.operands = operands

    def __repr__(self):
        return '({} {})'.format(self.node, self.operands)

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

#def createUnintSort():
#    prob = random.random()
#declare new Sort
#    if prob < 0.33 and n_unintsorts < 4:
#        new_UnintSort = UnintSort(n_unintsorts)
#        n_unintsorts += 1 
#        print('(declare-sort {} 0)'.format(new_UnintSort))
#        d[str(new_UnintSort)] = []
#
#add new variable to an existing sort
#    elif prob < 0.66:
#        current_sort = random.choice(list(d))
#        n = len(d[current_sort])
#        d[current_sort].append(sVar(current_sort, n))
#        print('(declare-const {} {})'.format(sVar(current_sort, n), current_sort))
#
#create a boolean expression using two variables in the same sort and add to Bool list
#    else:
#        current_sort = random.choice(list(d))
#        n_items = random.randrange(2, 5)
#        items = str(random.choice(d[str(current_sort)]))
#        for i in range(n_items-1):
#            items += (" " + str(random.choice(d[str(current_sort)])))
#        if random.random() < 0.5:
#            new_bool = '(= {})'.format(items)
#        else:
#            new_bool = '(distinct {})'.format(items)
#        d['Bool'].append(new_bool)            

indices = []
n_unintsorts = 0

UnOp = ["not"]
BiOp = ["=>"]
NarOp = ["and", "or", "xor", "=", "distinct"]

n_vars = random.randrange(1, 20)

#create a dictionary for all Sorts and add key Bool that will hold all boolean variables
d = OrderedDict()
d['Bool'] = []

for i in range(n_vars):
    d['Bool'].append(Var(i)) 
    print('(declare-const {} Bool)'.format(Var(i)))

n_push = 0
n_pop = 0

assertions = random.randrange(0, 100)
while assertions > 0:

    if n_push > n_pop:
        if random.random() < 0.1:
            print('(pop 1)')
            n_pop += 1

            if len(list(d.keys())) > n_keys:
                new_keys = list(d.keys())[n_keys:]
                for ones in new_keys:
                    del d[ones]

            for key in d:
                j = indices[list(d.keys()).index(key)]
                del d[key][j:]

        elif random.random() < 0.1:
            print('(push 1)')
            n_push += 1

            for key in d:
                indices.append(len(d[key]))
            n_keys = len(list(d.keys()))

    if n_push == n_pop:
        if random.random() < 0.1:
            print('(push 1)')
            n_push += 1
            
            for key in d:
                indices.append(len(d[key]))
            n_keys = len(list(d.keys()))

    if random.random() < 0.9:
#        createUnintSort()
        prob = random.random()
#declare new Sort
        if prob < 0.33 and n_unintsorts < 4:
            current_sort = UnintSort(n_unintsorts)
            n_unintsorts += 1 
            print('(declare-sort {} 0)'.format(current_sort))
            d[current_sort] = []
            d[current_sort].append(sVar(current_sort, 0))
            print('(declare-const {} {})'.format(sVar(current_sort, 0), current_sort))

#add new variable to an existing sort
        elif prob < 0.66 and len(d.keys()) > 1:
            options = list(d)
            options.remove('Bool')
            current_sort = random.choice(options)
            n = len(d[current_sort])
            d[current_sort].append(sVar(current_sort, n))
            print('(declare-const {} {})'.format(sVar(current_sort, n), current_sort))

#create a boolean expression using two variables in the same sort and add to Bool list
        elif len(d.keys()) > 1:
            options = list(d)
            options.remove('Bool')
            current_sort = random.choice(options)
            n_items = random.randrange(2, 5)
            items = str(random.choice(d[current_sort]))
            for i in range(n_items-1):
                items += (" " + str(random.choice(d[current_sort])))
            if random.random() < 0.5:
                new_bool = '(= {})'.format(items)
            else:
                new_bool = '(distinct {})'.format(items)
            d['Bool'].append(new_bool)            

    #decide: var or op
    if random.random() < 0.2:
        #choose var
        if random.random() < 0.5:
            #create new var and add it to Bool list
            new_var = Var(n_vars)
            print('(declare-const {} Bool)'.format(new_var))
            new_node = new_var
            n_vars += 1
            d['Bool'].append(new_var)
        else:
            #choose a var from Bool list
            new_node = random.choice(d['Bool'])
    else:
        p = random.randrange(1, 7)
        if p == 1:
            #pick from UnaryOp
            new_node = UnaryOp(random.choice(UnOp), random.choice(d['Bool']))
        elif p == 2:
            #pick from BinOp
            operand = ""
            operand = str(random.choice(d['Bool']))
            operand += (" " + str(random.choice(d['Bool'])))

            new_node = BinOp(random.choice(BiOp), operand)
                
        else:    
            #choose number operands
            n_operands = random.randrange(2, 10)

            #choose operands and put into string
            operands = ""
            operands = str(random.choice(d['Bool']))

            for i in range(n_operands-1):
                operands += (" " + str(random.choice(d['Bool'])))

            new_node = NOp(random.choice(NarOp), operands)

        if str(new_node) not in d['Bool']:
            d['Bool'].append(new_node)

    if random.random() < 0.4:
        print('(assert {})'.format(new_node))
        assertions -= 1

    if random.random() < 0.05:
        print('(check-sat)')

print("(check-sat)")
print("(exit)")
