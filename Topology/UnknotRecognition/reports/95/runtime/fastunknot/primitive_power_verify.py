"""Independent arithmetic replay of a source-reconstructed rank-two terminal.

No producer, gcd selection, orbit/Whitehead search or normalization is called.
The caller must first reconstruct a classical knot presentation and replay its
entire move prefix. These helpers alone make no assertion about arbitrary
presented groups. Coherent letter signs imply free and cyclic reduction.
"""
from math import gcd


def _header(terminal, alive, slots, length, check):
    check()
    if type(terminal) is not dict or set(terminal) != {
            'kind','relation','generators','primitive_vector','exponent','width'}:
        return None
    labels,vector = terminal['generators'],terminal['primitive_vector']
    slot,d,width = terminal['relation'],terminal['exponent'],terminal['width']
    if (terminal['kind'] != 'rank_two_primitive_power' or len(alive) != 2
            or type(labels) is not list or len(labels) != 2
            or any(type(g) is not int or g <= 0 for g in labels)
            or labels != sorted(alive) or type(vector) is not list or len(vector) != 2
            or any(type(x) is not int for x in vector)
            or type(slot) is not int or not 0 <= slot < slots
            or type(d) is not int or d < 1 or type(width) is not int):
        return None
    u,v = vector
    size = length(slot)
    # Bound every claimed integer by the reconstructed word before gcd and
    # products; forged large metadata cannot inflate the replay profile.
    if (not size or max(abs(u),abs(v),d) > size or not 0 <= width < size
            or gcd(abs(u),abs(v)) != 1 or width != abs(u)+abs(v)-1):
        return None
    return slot,labels,u,v,d,width


def verify_literal_terminal(words, alive, terminal, budget):
    data = _header(terminal,alive,len(words),lambda i: len(words[i]),budget.tick)
    if data is None:return False
    slot,labels,u,v,d,width = data
    signed = (labels[0],-labels[0],labels[1],-labels[1])
    weights = (v,-v,-u,u)
    counts = [0]*4
    height = low = high = 0
    for letter in words[slot]:
        budget.tick()
        if letter not in signed:return False
        i = signed.index(letter)
        counts[i] += 1
        height += weights[i]
        low,high = min(low,height),max(high,height)
    a,A,b,B = counts
    budget.tick()
    return (bool(a+A+b+B) and not (a and A or b and B)
            and a-A == d*u and b-B == d*v and high-low == width)


def verify_compressed_terminal(arena, roots, alive, terminal):
    data = _header(terminal,alive,len(roots),lambda i: arena.lengths[roots[i]],arena.tick)
    if data is None:return False
    slot,labels,u,v,d,width = data
    signed = (labels[0],-labels[0],labels[1],-labels[1])
    weights = (v,-v,-u,u)
    # A postorder stack independent of the producer's reachable-node traversal.
    # Replay only the selected relator; all slots were retained by the caller.
    memo = {0:((0,0,0,0),0,0,0)}
    pending = [(roots[slot],False)]
    while pending:
        arena.tick()
        node,ready = pending.pop()
        if node in memo:continue
        rule = arena.rules[node]
        if rule[0] == 't':
            if rule[1] not in signed:return False
            index = signed.index(rule[1]);counts = [0]*4;counts[index] = 1
            h = weights[index]
            memo[node] = tuple(counts),h,min(0,h),max(0,h)
        elif not ready:
            pending.extend(((node,True),(rule[2],False),(rule[1],False)))
        else:
            left,a,lo,hi = memo[rule[1]]
            right,b,low,high = memo[rule[2]]
            memo[node] = tuple(x+y for x,y in zip(left,right)),a+b,min(lo,a+low),max(hi,a+high)
    (a,A,b,B),_,low,high = memo[roots[slot]]
    arena.tick()
    return (bool(a+A+b+B) and not (a and A or b and B)
            and a-A == d*u and b-B == d*v and high-low == width)
