"""PA196 formula words and pinned shallow source association.

Definitions follow PA196/Logic/Basic.lean and the supplied Program.lean.
The MIT and MIT-0 notices are retained alongside this module.
"""
from pathlib import Path
import re
import gate_variants as g
I,M,U,E,N,And = g.I,g.M,g.U,g.E,g.N,g.And
emit=g.emit
def Ex(a,b):return N(U(a,N(b)))

def heads(flags,flip):
    d,h,a='DHA'
    eq=lambda x,y:E(x,y,flip)
    result=[I(Ex(d,U(d,h)),h),
            I(U(d,U(a,h)),U(a,U(d,h))),
            I(M(h,d),I(eq(h,a),M(a,d))),
            I(eq(h,d),I(M(a,h),M(a,d))),
            Ex(d,eq(h,d)),
            I(U(d,a),I(U(d,I(a,h)),U(d,h)))]
    for bit,j in enumerate((2,3,5)):
        if flags>>bit&1:
            _,x,(_,y,z)=result[j]
            result[j]=I(y,I(x,z))
    return result

def gate(swap,flip):return g.gate(False,False,swap,flip)
def isnode(t):return isinstance(t,tuple)and len(t)==2
def raw_nodes():
    nodes={}
    text=(Path(__file__).resolve().parent/'inputs/Program.lean').read_text()
    for name,line in re.findall(r'^def (\w+) : Tree := \.node (.*)$',text,re.M):
        tokens=re.findall(r'\(\.leaf \(\.(\w+)(?: (\d+))?\)\)|\b((?:node|x)\d+)\b',line)
        children=[child if child else ('leaf',op,int(arg)if arg else None)
                  for op,arg,child in tokens]
        assert len(children)==2
        nodes[name]=tuple(children)
    return nodes
raw=raw_nodes()
def shallow(t):
    if isinstance(t,str)and t.startswith('x'):
        a,b=raw[t];return(shallow(a),shallow(b))
    return t
initial=shallow('x67')
def flat(t):
    return flat(t[0])+flat(t[1]) if isnode(t) else [t]
w=flat(initial)
assert len(w)==201
prefix=w[:18]
suffix=w[-3:]
assert sum((emit(h)for h in heads(0,False)),[])==w[18:121]
assert emit(gate(False,False))==w[121:-3]
