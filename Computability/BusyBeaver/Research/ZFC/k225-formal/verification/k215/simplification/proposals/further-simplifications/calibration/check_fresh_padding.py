#!/usr/bin/env python3
"""Owned, independent finite sanity checks. No downloaded programs are executed.
Not a Lean proof, not an unbounded theorem check, not a runtime measurement.
Definitions transcribed from pinned Code254/TarskiCalculus/KSeedModel222.
"""
from functools import lru_cache
from itertools import product
from math import isqrt
from pathlib import Path
import json

if not __debug__:
    raise SystemExit("Assertions are required; do not run this checker with -O or -OO.")

B = ("bot",)
def rel(i, j): return ("rel", i, j)
def eq(i, j): return ("eq", i, j)
def imp(a, b): return ("imp", a, b)
def all_(i, a): return ("all", i, a)
def neg(a): return imp(a, B)
def pair(a, b): return (a+b)*(a+b+1)//2+b
def unpair(n):
    s = (isqrt(8*n+1)-1)//2
    b = n-s*(s+1)//2
    return s-b, b
def enc(f):
    t = f[0]
    if t == "bot": return 1
    if t == "rel": return 4*pair(f[1], f[2])+1
    if t == "eq": return 4*pair(f[1], f[2])+3
    if t == "imp": return 4*pair(enc(f[1]), enc(f[2]))
    return 4*pair(f[1], enc(f[2]))+2
def dec(c):
    if c == 0: return imp(rel(0, 0), rel(0, 0))
    a, b = unpair(c//4)
    return (lambda: imp(dec(a), dec(b)), lambda: rel(a,b),
            lambda: all_(a, dec(b)), lambda: eq(a,b))[c%4]()
def occurs(f):
    t = f[0]
    if t == "bot": return set()
    if t in ("rel", "eq"): return {f[1], f[2]}
    if t == "imp": return occurs(f[1]) | occurs(f[2])
    return {f[1]} | occurs(f[2])
def free(f):
    if f[0] == "all": return free(f[2]) - {f[1]}
    if f[0] == "imp": return free(f[1]) | free(f[2])
    return occurs(f)
def nodes(f):
    if f[0] == "imp": return 1+nodes(f[1])+nodes(f[2])
    if f[0] == "all": return 1+nodes(f[2])
    return 1
def upd(e,i,d):
    z=dict(e); z[i]=d
    return tuple(sorted(z.items()))
def val(e,i): return dict(e).get(i,0)
def evaluator(n, mem):
    @lru_cache(None)
    def sat(f,e):
        t=f[0]
        if t=="bot": return False
        if t=="rel": return mem[val(e,f[1])][val(e,f[2])]
        if t=="eq": return val(e,f[1])==val(e,f[2])
        if t=="imp": return not sat(f[1],e) or sat(f[2],e)
        return all(sat(f[2],upd(e,f[1],d)) for d in range(n))
    return sat
def req(b,k,m):
    return all_(b, imp(m,neg(all_(b,imp(m,neg(rel(b,k)))))))
def clos(a,b,k,m):
    return all_(b, imp(rel(b,k),neg(all_(a,imp(m,neg(all_(a,
        imp(all_(k,imp(rel(k,a),rel(k,b))),req(b,k,m)))))))))
def bundle(a,b,k,m):
    return neg(imp(imp(rel(a,b),all_(k,rel(a,b))),
                   all_(k,imp(clos(a,b,k,m),neg(req(b,k,m))))))
def seed(n,mem,R,A):
    def answered(C,x):
        return not any(R[x]) or any(R[x][z] and mem[z][C] for z in range(n))
    def subset(x,y): return all(not mem[w][x] or mem[w][y] for w in range(n))
    return any(answered(C,A) and all(not mem[y][C] or any(
        R[x][y] and all(not subset(xp,y) or answered(C,xp) for xp in range(n))
        for x in range(n)) for y in range(n)) for C in range(n))
def relation(sat,e,a,b,m,n):
    return [[sat(m,upd(upd(e,a,x),b,y)) for y in range(n)] for x in range(n)]

atoms=[B]+[c(i,j) for c in (rel,eq) for i in range(2) for j in range(2)]
forms=atoms+[imp(a,b) for a in atoms for b in atoms]+[all_(i,a) for i in range(2) for a in atoms]
for f in forms:
    assert all(i<enc(f) for i in occurs(f))
    assert enc(f) not in free(f)
    pad=all_(enc(f),f)
    assert enc(pad)>1
    assert nodes(pad)==nodes(f)+1
    assert nodes(neg(neg(f)))==nodes(f)+4

checks={"formula_occurrence_bounds":len(forms),"padding_semantics":0,
        "named_bundle_ordinary_iff":0,"junk_code_implication_semantics":0}
for bits in product((False,True),repeat=4):
    mem=(bits[:2],bits[2:])
    sat=evaluator(2,mem)
    for ev in product(range(2),repeat=2):
        e=tuple(enumerate(ev))
        for f in forms:
            assert sat(all_(enc(f),f),e)==sat(f,e)
            checks["padding_semantics"]+=1
            assert sat(bundle(0,1,2,f),e)==seed(2,mem,relation(sat,e,0,1,f,2),val(e,0))
            checks["named_bundle_ordinary_iff"]+=1
        for x,y in product(range(8),repeat=2):
            assert sat(dec(4*pair(x,y)),e)==(not sat(dec(x),e) or sat(dec(y),e))
            checks["junk_code_implication_semantics"]+=1

# Honest negative controls for the two syntactic aliases.
assert dec(0)!=imp(dec(0),dec(0))
assert dec(enc(B))!=B
assert evaluator(1,((True,),))(dec(1),()) is True
assert evaluator(1,((True,),))(B,()) is False

# The ordinary-role guard is real: an irreflexive degenerate-role counterexample.
# R(y) means 3 in y, so only 0 is an output. Any container containing 0 also
# contains the non-output 1, preventing SeedProp; the degenerate bundle is true.
mem=tuple(tuple((x,y) in {(3,0),(0,2),(1,2)} for y in range(4)) for x in range(4))
sat=evaluator(4,mem); e=((0,0),(1,3)); m=rel(1,0)
assert sat(bundle(0,0,2,m),e)
assert not seed(4,mem,relation(sat,e,0,0,m,4),0)

out={"status":"finite_sanity_checks_passed_not_kernel_certification",
     "source_pin":"beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc",
     "checks":checks,
     "all_2_element_membership_relations":16,
     "includes_reflexive_models":True,
     "empty_domain_note":"No Nat-valued environment into an empty domain exists; no consistency inference made.",
     "negative_controls":["raw code zero is not a syntax-homomorphic implication",
       "encoded Bottom decodes to Rel00; semantic equivalence fails in a reflexive singleton",
       "a=b counterexample: named bundle true while SeedProp false in an irreflexive four-element model"],
     "padding_node_change":"fresh universal adds 1 node; double negation adds 4 nodes",
     "proof_assistants_run":False}
Path(__file__).with_name("finite_checks.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out,indent=2))
