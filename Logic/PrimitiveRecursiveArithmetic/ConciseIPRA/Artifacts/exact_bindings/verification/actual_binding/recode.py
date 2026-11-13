"""Typed, untrusted recoding of decoded canonical native proof trees.

The input is a derivation tree reconstructed by the unchanged source scanner.
Each proof-packet field is recoded in its mathematical role. This deliberately
does not translate arbitrary accepted raw certificates or unused payloads.
"""
from copy import copy

def term(a, slots=()):
    if type(a) is int:
        if a <= 1:
            return a
        if a % 2 == 0:
            raise ValueError(('noncanonical even term code', a))
        j = (a - 3)//2
        if j < len(slots):
            if not slots[j]:
                raise ValueError(('dummy reference in canonical proof', a, slots))
            index = sum(slots[:j])
        else:
            index = j - slots.count(False)
        return 3 + 2*index
    if type(a) is not list:
        raise ValueError(('not a term tree',a))
    if len(a) == 1:
        return [term(a[0], (False,False)+slots)]
    if len(a) == 3:
        return [term(a[0], (False,)+slots),
                term(a[1], (False,)+slots),
                term(a[2], (True,)+slots)]
    raise ValueError(('bad canonical term arity', a))

def formula(a, slots=()):
    if a == 0 or a == []:
        return a
    if type(a) is not list:
        raise ValueError(('not a formula tree', a))
    if len(a) == 2:
        return [term(x,slots) for x in a]
    if len(a) == 1:
        return [formula(a[0],(True,True)+slots)]
    if len(a) == 3 and a[0] == a[1] == a[2]:
        return [formula(a[0],(True,)+slots)]*3
    raise ValueError(('bad canonical formula arity', a))

def recode_tree(node):
    out = copy(node)
    out.goal = formula(node.goal)
    m,s,u,t = node.packet
    if node.terminal == 'hypothesis':
        out.packet = [0,0,1,1]
    elif node.terminal == 'computation':
        out.packet = [0,term(s),term(u),term(t)]
    elif node.match:
        out.packet = [formula(m),term(s),term(u),formula(t)]
    elif m:
        out.packet = [formula(m),0,0,1]
    else:
        out.packet = [0,0,2 if node.progress else [],term(t)]
    if node.major is not None:
        out.major = recode_tree(node.major)
    if node.continuation is not None:
        out.continuation = recode_tree(node.continuation)
    return out
