"""Translate canonical certificates from the old arity table to affine scopes.

The former object/formula grammar is Eq/Q/D, and numerical terms are 0/S/I.
Within each equation insert one nearest dummy numerical slot. Bound numerical
slots belonging to an intervening successor/iterator stay in place. This is
an untrusted producer; only the standalone checker makes verdicts.
"""
from copy import deepcopy

def term(a,depth=0):
    if not isinstance(a,list):
        return a+2 if isinstance(a,(int,float)) and a>=2*depth+1 else a
    if len(a)==0:return []
    if len(a)==1:return [term(a[0],depth+1)]
    if len(a)==3:return [term(x,depth+2) for x in a]
    if len(a)==2:return 0  # inherited numerical zero alias, not an operator
    return deepcopy(a)    # preserve malformed shapes for boundary testing

def formula(a):
    if not isinstance(a,list):return a
    if len(a)==1:return [formula(a[0])]
    if len(a)==2:return [term(a[0]),term(a[1])]
    if len(a)==3:return [deepcopy(a[0]),deepcopy(a[1]),formula(a[2])]
    return deepcopy(a)

def translate(packet):
    if not isinstance(packet,list) or not packet:return deepcopy(packet)
    out=[]
    for item in packet[:-1]:
        if not isinstance(item,list) or len(item)!=4:
            out.append(deepcopy(item));continue
        m,s,u,t=item
        if m:
            out.append([formula(m),term(s),term(u),formula(t)])
        elif t:
            out.append([deepcopy(m),deepcopy(s),deepcopy(u),term(t)])
        else:
            out.append([deepcopy(m),term(s),deepcopy(u),deepcopy(t)])
    out.append(formula(packet[-1]))
    return out
