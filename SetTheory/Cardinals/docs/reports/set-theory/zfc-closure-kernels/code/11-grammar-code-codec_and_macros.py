#!/usr/bin/env python3
"""Exact, independently written regressions for the modified four-row search.

This is a mathematical prototype, not a verified compiler or a TM simulator.
Natural expressions are shared DAGs. Equality tests either use an identity or
an elementary certified distinction; undecidable-by-this-normalizer cases
raise, never use fingerprints. The implementation is independent of upstream
proof/validation programs.
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from math import isqrt
from pathlib import Path
import hashlib
import json
import random


def pair(a: int, b: int) -> int:
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n: int) -> tuple[int, int]:
    s = (isqrt(8*n + 1) - 1) // 2
    b = n - s*(s + 1)//2
    return s-b, b


TOP = ("top",)


def encode(f: tuple) -> int:
    op = f[0]
    if op == "top": return 0
    if op == "rel": return 3*pair(f[1], f[2]) + 1
    if op == "all": return 3*pair(f[1], encode(f[2])) + 2
    if op == "imp": return 3*pair(encode(f[1]), encode(f[2]))
    raise ValueError(op)


@lru_cache(None)
def decode(n: int) -> tuple:
    if not isinstance(n, int) or n < 0: raise ValueError("natural required")
    if n == 0: return TOP
    q, tag = divmod(n, 3)
    a, b = unpair(q)
    if tag == 0: return ("imp", decode(a), decode(b))
    if tag == 1: return ("rel", a, b)
    return ("all", a, decode(b))


def normalize(f: tuple) -> tuple:
    if f[0] in ("top", "rel"): return f
    if f[0] == "all": return ("all", f[1], normalize(f[2]))
    a, b = normalize(f[1]), normalize(f[2])
    return TOP if a == b == TOP else ("imp", a, b)


def labels(f: tuple) -> set[int]:
    if f[0] == "top": return set()
    if f[0] == "rel": return {f[1], f[2]}
    if f[0] == "all": return {f[1]} | labels(f[2])
    return labels(f[1]) | labels(f[2])


class Nat:
    __slots__ = ("uid", "kind", "args", "lower", "mod3")
    registry: dict[tuple, "Nat"] = {}

    def __new__(cls, kind, args, lower, mod3):
        key = (kind, args)
        if key in cls.registry: return cls.registry[key]
        self = super().__new__(cls)
        self.uid = len(cls.registry)
        self.kind, self.args = kind, args
        self.lower, self.mod3 = min(lower, 2), mod3
        cls.registry[key] = self
        return self

    def __repr__(self):
        if self.kind in ("num", "symbol"): return repr(self.args[0])
        return f"{self.kind}#{self.uid}"


def num(n: int) -> Nat:
    if not isinstance(n, int) or n < 0: raise ValueError("natural required")
    return Nat("num", (n,), n, n % 3)


ZERO, ONE = num(0), num(1)


def symbol(name: str, lower=0, mod3=None) -> Nat:
    return Nat("symbol", (name, lower, mod3), lower, mod3)


def plus(a: Nat, b: Nat) -> Nat:
    if a is ZERO: return b
    if b is ZERO: return a
    if a.kind == b.kind == "num": return num(a.args[0] + b.args[0])
    if b.uid < a.uid: a, b = b, a
    residue = None if a.mod3 is None or b.mod3 is None else (a.mod3+b.mod3) % 3
    return Nat("add", (a, b), a.lower+b.lower, residue)


def P(a: Nat, b: Nat) -> Nat:
    if a.kind == b.kind == "num":
        value = pair(a.args[0], b.args[0])
        if value.bit_length() <= 256: return num(value)
    return Nat("pair", (a, b), pair(a.lower, b.lower), None)


def unP(n: Nat) -> tuple[Nat, Nat]:
    if n.kind == "pair": return n.args
    if n.kind == "num":
        a, b = unpair(n.args[0]); return num(a), num(b)
    raise ValueError(f"unpair lacks certified inverse: {n!r}")


def code(tag: int, a: Nat, b: Nat) -> Nat:
    q = P(a, b)
    if q.kind == "num":
        value = 3*q.args[0]+tag
        if value.bit_length() <= 256: return num(value)
    return Nat("code", (tag, a, b), 3*q.lower+tag, tag)


def eq(a: Nat, b: Nat) -> bool:
    if a is b: return True
    if a.kind == b.kind == "num": return a.args[0] == b.args[0]
    if a.mod3 is not None and b.mod3 is not None and a.mod3 != b.mod3: return False
    if a.kind == "num" and a.args[0] < b.lower: return False
    if b.kind == "num" and b.args[0] < a.lower: return False
    raise ValueError(f"comparison has no certificate: {a!r} =? {b!r}")


def imp(a,b): return code(0,a,b)
def rel(a,b): return code(1,a,b)
def all_(a,b): return code(2,a,b)
def neg(a): return imp(a,ONE)
def conj(a,b): return neg(imp(a,neg(b)))
def ex(a,b): return neg(all_(a,neg(b)))


ACTIVE_PROFILE=(True,False)


def rows(a,h,b,c,u):
    """GEN; rho8 or its bijective reparameterization; rho2; rho4; B row.

    ACTIVE_PROFILE selects (dual_B, permuted_L) for sequential regressions.
    The optimized L' is literally L(b,u,a,c).
    """
    dual,permuted=ACTIVE_PROFILE
    L=(imp(imp(imp(a,c),b),imp(imp(b,a),imp(u,a))) if permuted else
       imp(imp(imp(c,u),a),imp(imp(a,c),imp(b,c))))
    B=imp(b,all_(a,ex(a,b))) if dual else imp(ex(a,all_(a,b)),b)
    return [all_(a,h),L,
        imp(all_(a,imp(b,c)),imp(all_(a,b),all_(a,c))),
        imp(all_(a,all_(b,c)),all_(b,all_(a,c))),
        B]


def bundle(a,b,c):
    power = ex(c,conj(all_(b,imp(all_(c,imp(rel(c,b),rel(c,a))),rel(b,c))),rel(c,b)))
    trans = all_(c,imp(rel(c,a),rel(c,b)))
    C = ex(b,conj(all_(a,imp(rel(a,b),conj(power,trans))),rel(c,b)))
    w = ex(b,conj(c,rel(b,c)))
    G = ex(c,conj(all_(a,imp(rel(a,b),all_(b,imp(c,w)))),
                  all_(b,imp(rel(b,c),ex(a,c)))))
    V = imp(rel(a,b),all_(c,rel(a,b)))
    return conj(V,conj(C,G))


@dataclass(frozen=True)
class State:
    top: Nat
    stack: Nat
    counter: Nat = ZERO
    cache: Nat = ZERO


def MP(x=ZERO): return ("mp",x)
DROP = ("drop",ZERO)
NIP = ("nip",ZERO)
def AX(c,x=ZERO,y=ZERO,u=ZERO): return ("ax",x,c,y,u)


def command(s: State, cmd: tuple) -> State | None:
    op, x = cmd[:2]
    t,S,d,h = s.top,s.stack,plus(s.counter,x),s.cache
    if op == "mp":
        if eq(imp(t,d),h): t,S=d,P(ZERO,S)
        else: t=ZERO
        h=ZERO
    elif op == "drop": t,S=h,P(t,S)
    elif op == "nip":
        if eq(h,ONE): return None
        h,S=unP(S)
    elif op == "ax":
        c,y,u=cmd[2:]; a=d; b=plus(h,y)
        for r in [t]+rows(a,h,b,c,u): S=P(r,S)
        t=ZERO if eq(c,a) or eq(c,b) else bundle(a,b,c)
        d=h=ZERO
    else: raise ValueError(op)
    return State(t,S,d,h)


def run(s,commands):
    for cmd in commands:
        s=command(s,cmd)
        if s is None:return None
    return s


DISCARD=[MP(ONE),AX(ONE)]+[NIP]*6


def leaf_bundle(a,b,c,u=ZERO):
    return DISCARD+[AX(c,a,b,u)]+[NIP]*6


def leaf_row(a,b,c,u,j):
    assert 1<=j<=4
    return DISCARD+[AX(c,a,b,u)]+[NIP]*j+[DROP]+[NIP]*(7-j)


def gen_block(block,i):
    return block+[DROP,NIP,AX(i,i)]+[NIP]*5+[DROP,NIP,NIP]


def mp_block(block_A,block_imp,B):
    return block_A+[DROP]+block_imp+[NIP,DROP,NIP,MP(B),AX(B)]+[NIP]*6+[DROP,NIP,NIP]


def codec_checks():
    count=0
    for n in range(10000):
        f=decode(n)
        assert encode(f)==n and normalize(f)==f
        assert all(v<n for v in labels(f))
        count+=1
    rng=random.Random(252)
    def random_formula(depth):
        if depth==0 or rng.random()<0.30:
            return TOP if rng.random()<0.20 else ("rel",rng.randrange(8),rng.randrange(8))
        if rng.random()<0.4:return ("all",rng.randrange(8),random_formula(depth-1))
        return ("imp",random_formula(depth-1),random_formula(depth-1))
    for _ in range(1000):
        f=random_formula(5)
        assert decode(encode(f))==normalize(f)
        count+=1
    return {"exact_roundtrip_and_freshness_codes":10000,
            "exact_random_finite_formula_normalization_cases":1000,
            "total":count}


def macro_checks(dual=True,permuted=False):
    global ACTIVE_PROFILE
    ACTIVE_PROFILE=(dual,permuted)
    counts={"discard":0,"row_extraction":0,"bundle_extraction":0,"gen":0,
            "mp_context":0,"start":0,"halt_suffix":0}
    rng=random.Random(250)
    retained_stacks=[ZERO,num(42),symbol("uninspected-stack")]
    retained_tops=[ZERO,ONE,num(7),symbol("arbitrary-top")]
    for S in retained_stacks:
        for T in retained_tops:
            start=State(T,S)
            assert run(start,DISCARD)==State(ZERO,S)
            counts["discard"]+=1
            for _ in range(15):
                a,b,c,u=[num(rng.randrange(6)) for _ in range(4)]
                for j in range(1,5):
                    expected=rows(a,ZERO,b,c,u)[-j]
                    assert run(start,leaf_row(a,b,c,u,j))==State(expected,S)
                    counts["row_extraction"]+=1
                expected=ZERO if eq(c,a) or eq(c,b) else bundle(a,b,c)
                assert run(start,leaf_bundle(a,b,c,u))==State(expected,S)
                counts["bundle_extraction"]+=1
                for j in (1,4):
                    block=leaf_row(a,b,c,u,j)
                    H=rows(a,ZERO,b,c,u)[-j]
                    i=num(rng.randrange(6))
                    assert run(start,gen_block(block,i))==State(all_(i,H),S)
                    counts["gen"]+=1
            # Execute exactly the two MP-node contexts around abstract sub-builders.
            # Sub-builders' only assumed contract is (T,S,0,0)->(formula,S,0,0).
            for A in (ONE,num(7),imp(num(7),num(7))):
                for B in (ONE,num(7),all_(ONE,ZERO)):
                    left=run(State(A,S),[DROP])
                    right=State(imp(A,B),left.stack)
                    out=run(right,[NIP,DROP,NIP,MP(B),AX(B)]+[NIP]*6+[DROP,NIP,NIP])
                    assert out is None if A is ONE or B is ONE else out==State(B,S)
                    counts["mp_context"]+=1
            for d,h in [(ZERO,ZERO),(num(4),num(9)),(symbol("d"),symbol("h"))]:
                out=run(State(T,S,d,h),[AX(ZERO,ONE,ONE,ZERO)])
                assert out is not None and out.counter is ZERO and out.cache is ZERO
                counts["start"]+=1
            assert run(State(ONE,S),[DROP,NIP,NIP]) is None
            counts["halt_suffix"]+=1
    return counts | {"total":sum(counts.values()),
                     "quantifier_row":"dual" if dual else "original",
                     "L_row":"permuted" if permuted else "original",
                     "integer_expression_DAG_nodes":len(Nat.registry),
                     "probabilistic_equality":False,"uncertified_comparison_policy":"raise"}


def relative_model_checks():
    """The full dual calculus has a Boolean model separating it from old rho6.

    Universal operators are identity, F is true; raw Rel(0,1) is false.
    Every outer relative conjunction and every relative existential is true.
    This demonstrates derivability inequivalence, not refutation inequivalence.
    """
    def imply(a,b):return not a or b
    def exists(a):return imply(imply(a,True),True)
    cases=0
    for a in (False,True):
      for b in (False,True):
       for c in (False,True):
        for u in (False,True):
         assert imply(imply(imply(c,u),a),imply(imply(a,c),imply(b,c)))
         assert imply(b,exists(b))
         assert imply(imply(b,c),imply(b,c))
         assert imply(c,c)
         cases+=1
    assert not imply(True,False)
    assert not imply(exists(False),False)
    # A different two-world model separates refutations after a single added
    # F-stable axiom T=Q(F->A)->F. This is not the actual C/G theory.
    # w sees w,g; g sees only g. Values are pairs (at w, at g).
    F=(False,True)
    A=(False,False)
    def arr(p,q):return tuple(imply(x,y) for x,y in zip(p,q))
    def box(p):return (all(p),p[1])
    def neg(p):return arr(p,F)
    def diamond(p):return neg(box(neg(p)))
    values=[(bool(k&1),bool(k&2)) for k in range(4)]
    for p in values:
        assert all(arr(p,box(diamond(p))))
        for q in values:
            assert all(arr(box(arr(p,q)),arr(box(p),box(q))))
    assert all(arr(F,box(F))) and all(arr(A,box(A)))
    T=arr(box(arr(F,A)),F)
    assert T==(True,True) and F[0] is False
    return {"Boolean_assignments_checked":cases,
            "old_dual_derivability_equivalent":False,
            "two_world_dual_B_cases":4,"two_world_K_cases":16,
            "arbitrary_theory_refutation_conservativity_counterexample":True,
            "actual_C_G_refutation_equivalence_decided":False}


def main():
    profiles={f"{L}_L_{B}_B":macro_checks(dual=(B=="dual"),permuted=(L=="permuted"))
              for L in ("original","permuted") for B in ("dual","original")}
    result={"scope":"Independent exact regressions, not formal proofs or TM validation",
            "codec":codec_checks(),"macros":{"profiles":profiles,
              "total":sum(p["total"] for p in profiles.values()),
              "probabilistic_equality":False,"uncertified_comparison_policy":"raise"},
            "relative_falsity_separating_model":relative_model_checks()}
    result["script_sha256"]=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    output=Path(__file__).with_name("codec-and-macro-results.json")
    output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))


if __name__=="__main__":main()
