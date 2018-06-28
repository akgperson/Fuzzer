import random

class New:
    def __init__(self, n):
        self.n = n
    def __repr__(self):
        return 'key' + str(self.n)

class Var:
    def __init__(self, n):
        self.n = n
    def __repr__(self):
        return 'v' + str(self.n)

d = dict()
d['Bool'] = []
#for k,v in d.items(): 
#    print(k, v)
d['Bool'].append(Var(4))
#for k,v in d.items(): 
#    print(k, v)

#val = random.choice(d['Bool'])
#print(val)

#print(len(d['Bool']))

new_key = New(3)
d[str(new_key)] = ['first']
d[str(new_key)].append(Var(1))
#for k,v in d.items(): 
#    print(k, v)
#ran = random.choice(list(d))
#print(ran)

print(str(random.choice(d[str(new_key)])))

#d['Bool'].append(item)
#print(d['Bool'])

