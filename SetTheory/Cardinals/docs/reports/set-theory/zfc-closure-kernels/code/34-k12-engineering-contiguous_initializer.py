"""Counted binary blank-tape initializer using a contiguous unary counter.

This is a new local compiler component, not a ZFC consistency-machine claim.
The input/output convention is that of ProveIt's compact_initializer.py,
whose source21 construction is separately attributed in the accompanying notes.
All declared counts include the initializer's complete binary state table.
"""
from __future__ import annotations
from math import isqrt

PHYSICAL_ORDER = (2, 4, 3, 7, 6, 8, 0, 1, 5)


def choose_parameters(minimum_gap, *, shared_cleanup=False):
    if type(minimum_gap) is not int or minimum_gap < 1:
        raise ValueError("minimum_gap must be a positive integer")
    offset = 5 if shared_cleanup else 3
    radicand = 4*max(0,minimum_gap-offset)
    root = isqrt(radicand)
    if root*root < radicand: root += 1
    # For c=n+m, max_n n(c+1-n) = floor((c+1)^2/4).
    # This is the exact minimum possible variable state cost in this family.
    c = max(2,root-1)
    candidates = []
    for n in range(1,c):
        m = c-n
        gap = n * (m + 1) + offset
        if gap < minimum_gap: continue
        cost = n + m + (32 if shared_cleanup else 33)
        time = (57 if shared_cleanup else 35) + 8*n + (m+1)*n*(n+2)
        candidates.append((cost, time, gap, n, m))
    _, _, _, n, m = min(candidates)
    return n, m


def make_initializer(initial, n, m, target="return", *, shared_cleanup=False):
    initial = tuple(initial)
    if len(initial) != 9 or any(type(x) is not int or x < 0 for x in initial):
        raise ValueError("exactly nine natural initial registers required")
    if type(n) is not int or type(m) is not int or n < 1 or m < 1:
        raise ValueError("positive n and m required")
    if target.startswith("i:"):
        raise ValueError("target must not collide with initializer labels")
    registers = [b for j in PHYSICAL_ORDER for b in [0] + [1]*(initial[j]+1)]
    # Viewed left-to-right after writing: marker, 0, 1^n, 00,
    # optionally (sentinel 1, 0), header, register file.
    wire = list(reversed(registers)) + [1]
    if shared_cleanup:
        wire += [0, 1]
    wire += [0, 0] + [1]*n + [0, 1]
    table = {}
    def put(q,b,w,d,t):
        if (q,b) in table:
            raise ValueError("duplicate transition")
        table[q,b] = w,d,t
    def both(q,w,d,t):
        for b in (0,1): put(q,b,w,d,t)
    for j,w in enumerate(wire):
        last = j+1 == len(wire)
        both(f"i:{j}",w,"R" if last else "L",
             "i:right" if last else f"i:{j+1}")
    put("i:right",0,0,"R","i:right")
    put("i:right",1,1,"R","i:ones")
    put("i:ones",1,1,"R","i:ones")
    put("i:ones",0,0,"R","i:test")
    put("i:test",0,0,"L","i:back")
    put("i:test",1,1,"L","e:14" if shared_cleanup else "i:finish_zero")
    both("i:back",0,"L","i:erase")
    both("i:erase",0,"L","i:return_ones")
    put("i:return_ones",1,1,"L","i:return_ones")
    put("i:return_ones",0,0,"L","i:return_zeros")
    put("i:return_zeros",0,0,"L","i:return_zeros")
    put("i:return_zeros",1,0,"L","i:stride0")
    for j in range(m):
        last = j+1 == m
        both(f"i:stride{j}",1 if last else 0,"R" if last else "L",
             "i:right" if last else f"i:stride{j+1}")
    if not shared_cleanup:
        both("i:finish_zero",0,"L","i:finish_header")
        both("i:finish_header",1,"L","i:finish_left")
        put("i:finish_left",0,0,"L","i:finish_left")
        put("i:finish_left",1,1,"R",target)
    S = sum(initial)
    gap = n*(m+1)+(5 if shared_cleanup else 3)
    contract = dict(kind="contiguous-unary", counter_count=n, stride=m, gap=gap,
                    shared_cleanup=shared_cleanup,
                    initializer_states=S+n+m+(32 if shared_cleanup else 33),
                    blank_steps=S+(57 if shared_cleanup else 35)+8*n+(m+1)*n*(n+2),
                    initial_registers=list(initial), physical_order=list(PHYSICAL_ORDER),
                    scratch_marks_on_exit=0, spare_register_blocks=0,
                    absolute_exit_head=-(18+S+gap))
    assert len(table) == 2*contract["initializer_states"]
    return table, contract


def check_literal_boot(table, start, target, contract):
    """All finite support is compared; exterior blanks are therefore included."""
    q,head,ones = start,0,set()
    for steps in range(contract["blank_steps"]+1):
        if q == target: break
        w,d,q = table[q,int(head in ones)]
        if w: ones.add(head)
        else: ones.discard(head)
        head += 1 if d == "R" else -1
    else: raise AssertionError("initializer exceeded exact step count")
    bits = [1]+[0]*contract["gap"]+[1]
    bits += [b for j in PHYSICAL_ORDER
             for b in [0]+[1]*(contract["initial_registers"][j]+1)]
    expected = {head-1+i for i,b in enumerate(bits) if b}
    assert steps == contract["blank_steps"]
    assert head == contract["absolute_exit_head"]
    assert ones == expected
    return dict(steps=steps,head=head,state=target,one_positions=sorted(ones),
                exact_finite_support=True,all_other_integer_cells_zero=True)
