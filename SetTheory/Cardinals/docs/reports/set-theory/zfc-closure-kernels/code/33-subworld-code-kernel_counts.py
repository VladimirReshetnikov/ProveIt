"""Exact syntax counts for the proposed bounded-parameter subworld kernel.

This is a source-size measurement, not a TM-state estimate or proof checker.
Grammar: Bottom, Member, Equal, Imp, All, and one opaque matrix hole Phi.
Exists, And, Iff expand classically through Bottom/Imp/All.
All reported trees include duplicated subexpressions (no DAG sharing).
"""
from collections import Counter
import json

F = ('bottom',)
P = ('phi',)

def mem(x,y): return ('member',x,y)
def eq(x,y): return ('equal',x,y)
def imp(a,b): return ('imp',a,b)
def all_(x,a): return ('all',x,a)
def neg(a): return imp(a,F)
def ex(x,a): return neg(all_(x,neg(a)))
def and_(a,b): return neg(imp(a,neg(b)))
def iff(a,b): return and_(imp(a,b),imp(b,a))

# The five variable labels are a,b,z,x,y. W is a genuine constant.
N = ex('z',mem('z','W'))
EXT = imp(all_('z',iff(mem('z','a'),mem('z','b'))),eq('a','b'))
SS = imp(mem('x','W'),ex('y',and_(mem('y','W'),all_('z',
     iff(mem('z','y'),and_(mem('z','x'),P))))))
RED = imp(and_(mem('a','W'),mem('b','W')),
          imp(ex('z',P),ex('z',and_(mem('z','W'),P))))
JOIN_RAW = and_(N,and_(SS,RED))
JOIN_EXT = and_(and_(N,EXT),and_(SS,RED))

# Equivalent strengthened separation: move the source guard inside the
# already inhabited output existential. This absorbs N at no stencil cost.
# Curry only the reverse direction of exact intersection, avoiding a
# duplicated expanded And.
A = mem('z','y')
B = mem('z','x')
exact_intersection = and_(imp(A,and_(B,P)),imp(B,imp(P,A)))
SS_PLUS = ex('y',and_(mem('y','W'),imp(mem('x','W'),
                                     all_('z',exact_intersection))))
# Free z in the antecedent is rebound in the consequent: no syntax-level
# substitution of the matrix is hidden by this formulation.
RED_CURRY = imp(mem('a','W'),imp(mem('b','W'),imp(P,
                               ex('z',and_(mem('z','W'),P)))))
COMPACT_RAW = and_(SS_PLUS,RED_CURRY)
COMPACT_EXT = and_(EXT,COMPACT_RAW)

# Published 254-lineage C/G/V bundle, abstracting its relative falsity to F
# only for a like-for-like syntax count. This is not a semantics bridge.
C = ex('b',and_(
    all_('a',imp(mem('a','b'),and_(
        ex('c',and_(all_('b',imp(all_('c',imp(mem('c','b'),mem('c','a'))),
                                   mem('b','c'))),mem('c','b'))),
        all_('c',imp(mem('c','a'),mem('c','b')))))),mem('c','b')))
G = ex('c',and_(
    all_('a',imp(mem('a','b'),all_('b',imp(P,ex('b',and_(P,mem('b','c'))))))),
    all_('b',imp(mem('b','c'),ex('a',P)))))
VM = imp(mem('a','b'),all_('c',mem('a','b')))
VE = imp(eq('a','b'),all_('c',eq('a','b')))
ORIGINAL = and_(and_(C,G),and_(VM,VE))

def quantify(xs,a):
    for x in reversed(xs): a=all_(x,a)
    return a

def counts(a):
    c=Counter()
    def go(t):
        c[t[0]]+=1
        if t[0]=='imp': go(t[1]); go(t[2])
        elif t[0]=='all': c['labels']+=1; go(t[2])
        elif t[0] in ('member','equal'): c['labels']+=2
    go(a)
    c['formula_nodes']=sum(v for k,v in c.items() if k!='labels')
    c['stack_tokens']=c['formula_nodes']+c['labels']
    c['constructors_excluding_matrix_holes']=c['formula_nodes']-c['phi']
    return dict(sorted(c.items()))

if __name__=='__main__':
    out={name:counts(t) for name,t in [('N',N),('EXT',EXT),('SS2',SS),('RED2',RED),
       ('joined_raw_open',JOIN_RAW),('joined_extensional_open',JOIN_EXT),
       ('joined_raw_universal_closure',quantify(['a','b','x'],JOIN_RAW)),
       ('joined_extensional_universal_closure',quantify(['a','b','x'],JOIN_EXT)),
       ('original_C',C),('original_G',G),('original_CG_V',ORIGINAL),
       ('joined_raw_plus_V',and_(JOIN_RAW,and_(VM,VE))),
       ('joined_extensional_plus_V',and_(JOIN_EXT,and_(VM,VE))),
       ('compact_SS_plus',SS_PLUS),('compact_RED2',RED_CURRY),
       ('compact_raw_open',COMPACT_RAW),('compact_extensional_open',COMPACT_EXT),
       ('compact_raw_plus_V',and_(COMPACT_RAW,and_(VM,VE))),
       ('compact_extensional_plus_V',and_(COMPACT_EXT,and_(VM,VE))),
       ('compact_raw_universal_closure',quantify(['a','b','x','z'],COMPACT_RAW)),
       ('compact_extensional_universal_closure',quantify(['a','b','x','z'],COMPACT_EXT))]}
    print(json.dumps(out,indent=2,sort_keys=True))
