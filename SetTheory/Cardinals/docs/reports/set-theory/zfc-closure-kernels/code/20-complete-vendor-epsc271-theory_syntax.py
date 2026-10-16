"""Pure symbolic constructors used by the retained EPSC emitter.

These definitions match ProveIt's theory_backend_experiment.py; logical
formula position1 is a falsity placeholder, not a variable label.
The runtime codec in this deliverable makes that placeholder genuine Bottom.
"""

def Imp(a,b):return('imp',a,b)
def Rel(a,b):return('rel',a,b)
def Eq(a,b):return('eq',a,b)
def All(a,b):return('all',a,b)
def Not(a):return Imp(a,1)
def And(a,b):return Not(Imp(a,Not(b)))
def Ex(a,b):return Not(All(a,Not(b)))
def Or(a,b):return Imp(Not(a),b)
def Iff(a,b):return And(Imp(a,b),Imp(b,a))
