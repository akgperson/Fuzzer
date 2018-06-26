import random

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

# decide on number of assertions (0-100)
assertions = random.randrange(0, 100)

leaf = []
scopes = []
UnOp = ["not"]
BiOp = ["=>"]
NarOp = ["and", "or", "xor", "=", "distinct"]

# create variables
n_vars = random.randrange(1, 20)

for i in range(n_vars):
    leaf.append(Var(i))
    print('(declare-const {} Bool)'.format(Var(i)))

n_push = 0
n_pop = 0

while assertions > 0:

    if n_push > n_pop:
        if random.random() < 0.1:
            print('(pop 1)')
            n_pop += 1
            idx = scopes.pop()
            del leaf[idx:]
        elif random.random() < 0.1:
            print('(push 1)')
            n_push += 1
            scopes.append(len(leaf))
    if n_push == n_pop:
        if random.random() < 0.1:
            print('(push 1)')
            n_push += 1
            scopes.append(len(leaf))

    #decide: var or op
    if random.random() < 0.2:
        #choose var
        if random.random() < 0.5:
            #create new var and add it to leaf list
            new_var = Var(n_vars)
            print('(declare-const {} Bool)'.format(new_var))
            new_node = new_var
            n_vars += 1
            leaf.append(new_var)
        else:
            #choose a var from leaf list
            new_node = random.choice(leaf)
    else:
        p = random.randrange(1, 7)
        if p == 1:
            #pick from UnaryOp
#            if random.random() < 0.5:
            new_node = UnaryOp(random.choice(UnOp), random.choice(leaf))
#            else:
#                new_var = Var(n_vars)
#                n_vars += 1
#                print('(declare-const {} Bool)'.format(new_var))
#                new_node = UnaryOp(random.choice(UnOp), new_var)
        elif p == 2:
            #pick from BinOp
            operand = ""
            
#            if random.random() < 0.5:
            operand = str(random.choice(leaf))
#            else:
#                new_var = Var(n_vars)
#                print('(declare-const {} Bool)'.format(new_var))
#                n_vars += 1
#                leaf.append(new_var)
#                operand = str(new_var)
            
#            if random.random() < 0.5:
            operand += (" " + str(random.choice(leaf)))
#            else:
#                new_var = Var(n_vars)
#                print('(declare-const {} Bool)'.format(new_var))
#                n_vars += 1
#                leaf.append(new_var)
#                operand += (" " + str(new_var))

            new_node = BinOp(random.choice(BiOp), operand)
                
        else:    
            #choose number operands
            n_operands = random.randrange(2, 10)

            #choose operands and put into string
            operands = ""

#            if random.random() < 0.5:
            operands = str(random.choice(leaf))
#            else:
#                new_var = Var(n_vars)
#                print('(declare-const {} Bool)'.format(new_var))
#                n_vars += 1
#                leaf.append(new_var)
#                operands = str(new_var)

            for i in range(n_operands-1):
#                if random.random() < 0.5:
                operands += (" " + str(random.choice(leaf)))
#                else:
#                    new_var = Var(n_vars)
#                    print('(declare-const {} Bool)'.format(new_var))
#                    n_vars += 1
#                    leaf.append(new_var)
#                    operands += (" " + str(new_var))

            new_node = NOp(random.choice(NarOp), operands)

        if str(new_node) not in leaf:
            leaf.append(new_node)

    if random.random() < 0.1:
        print('(assert {})'.format(new_node))
        assertions -= 1

    if random.random() < 0.05:
        print('(check-sat)')

print("(check-sat)")
print("(exit)")
