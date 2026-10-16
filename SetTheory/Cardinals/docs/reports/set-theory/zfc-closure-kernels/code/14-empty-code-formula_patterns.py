"""Standalone symbolic patterns used in the rejected reduced-logic experiment.

Constructor conventions follow the pinned ProveIt/upstream generator. This
small specification is independently written and does not import a compiler.
Integers and string parameters in formula positions denote numerical codes.
"""
def Imp(a,b):return ('imp',a,b)
def Rel(a,b):return ('rel',a,b)
def All(a,b):return ('all',a,b)
def Not(a):return Imp(a,1)
def And(a,b):return Not(Imp(a,Not(b)))
def Or(a,b):return Imp(Not(a),b)
def Ex(a,b):return Not(All(a,Not(b)))

def psc(kernel='subset',support_first=False,a=0,b=1,c='c'):
    """Fixed slots by default; a,b may instead be emitter parameters."""
    bounded=All(a,Ex(c,All(b,Imp(c,All(a,Imp(Rel(a,b),Rel(a,c)))))))
    seed=All(c,Imp(Rel(c,a),Rel(c,b))) if kernel=='subset' else All(c,Not(Rel(c,a)))
    closed=All(a,Imp(Or(seed,Rel(a,c)),All(b,Imp(c,Rel(b,c)))))
    support=All(b,Imp(Rel(b,c),Ex(a,c)))
    body=Ex(c,And(support,closed) if support_first else And(closed,support))
    return Imp(bounded,All(b,body) if kernel=='subset' else body)

def retained_logic():
    # This list is checked against the frozen upstream symbolic spec when
    # compiler experiments are reproduced. The Boolean regression needs no repo.
    a,b,c,u='a','b','c','u'
    return [
        Imp(Imp(Imp(c,u),a),Imp(Imp(a,c),Imp(b,c))),
        Imp(Ex(a,All(a,b)),b),
        Imp(All(a,All(b,c)),All(b,All(a,c))),
        Imp(All(a,Imp(b,c)),Imp(All(a,b),All(a,c))),
        Imp(b,All(a,Ex(a,b))),
        Imp(Rel(a,b),All(c,Rel(a,b))),
    ]
