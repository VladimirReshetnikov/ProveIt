#!/usr/bin/env python3
"""Check the six-valued obstruction to replacing rho8 by K and S.

The theorem is about the *logical* code calculus: K, S, the other seven
published rows, atomic fresh-variable vacuity, MP, GEN and irreflexivity.
CP and GIC are not hypotheses of this obstruction. This is not a model of
ordinary first-order semantics and makes no claim about a binary table.
Only Python's standard library is required. Explicit exceptions remain
active under python -O. The accompanying proof is in report.pdf and
formalism/ks_obstruction.tex. Supply --output for a fresh external receipt.
"""
from itertools import product
from pathlib import Path
import json
import argparse
import hashlib

H=tuple(product(range(3),range(2)))
BOT=(0,0)
TOP=(2,1)
E=(0,1)
FIXED=(BOT,E,TOP)
DOMAIN=(0,1)
counts={}

def meet(a,b): return min(a[0],b[0]),min(a[1],b[1])
def le(a,b): return a[0]<=b[0] and a[1]<=b[1]
def imp(a,b): return (2 if a[0]<=b[0] else b[0],
                     1 if a[1]<=b[1] else b[1])
def neg(a): return imp(a,BOT)
def modal(a): return ((1+a[1]) if a[0]==2 else 0,a[1])
def inf(values):
    result=TOP
    for x in values: result=meet(result,x)
    return result
def universal(values): return modal(inf(values))
def exists(values): return neg(universal(neg(v) for v in values))
def check(name,condition):
    if not condition: raise ValueError('failed obligation: '+name)
    counts[name]=counts.get(name,0)+1

def algebra_checks():
    check('Q_top',modal(TOP)==TOP)
    check('Q_bottom',modal(BOT)==BOT)
    for a,b in product(H,repeat=2):
        check('Q_meet',modal(meet(a,b))==meet(modal(a),modal(b)))
        check('modus_ponens',not(a==TOP and imp(a,b)==TOP) or b==TOP)
        check('K',imp(a,imp(b,a))==TOP)
        check('normal_distribution',le(modal(imp(a,b)),imp(modal(a),modal(b))))
    for a,b,c in product(H,repeat=3):
        check('S',imp(imp(a,imp(b,c)),imp(imp(a,b),imp(a,c)))==TOP)
        check('Heyting_residuation',le(meet(a,b),c)==le(a,imp(b,c)))
    for a in H:
        actual=neg(modal(neg(modal(a))))
        check('rho6_scalar',le(actual,a))
        check('rho6_closed_formula',actual==(2 if a[0]==2 else 0,a[1]))
        check('fixed_points',(modal(a)==a)==(a in FIXED))
    for v in product(H,repeat=2):
        quantified=universal(v)
        existential_universal=exists((quantified,quantified))
        for current in v:
            check('rho6_domain_two',imp(existential_universal,current)==TOP)
    for b0,b1,c0,c1 in product(H,repeat=4):
        bv=(b0,b1);cv=(c0,c1)
        row=imp(universal(imp(b,c) for b,c in zip(bv,cv)),
                imp(universal(bv),universal(cv)))
        check('rho2_domain_two',row==TOP)
        left=universal((universal((b0,b1)),universal((c0,c1))))
        right=universal((universal((b0,c0)),universal((b1,c1))))
        check('rho4_domain_two',left==right)

def equality_and_membership_checks():
    for r01,r10 in product(FIXED,repeat=2):
        relation={(0,0):BOT,(1,1):BOT,(0,1):r01,(1,0):r10}
        for env in product(DOMAIN,repeat=3):
            def eq(a,b): return TOP if env[a]==env[b] else BOT
            def rel(a,b): return relation[env[a],env[b]]
            for a,b,c in product(range(3),repeat=3):
                check('rho7_euclid',imp(eq(c,a),imp(eq(c,b),eq(a,b)))==TOP)
                check('rho5_left_congruence',imp(eq(c,a),imp(rel(c,b),rel(a,b)))==TOP)
                check('rho3_right_congruence',imp(eq(a,b),imp(rel(c,a),rel(c,b)))==TOP)
                if c!=a and c!=b:
                    check('atomic_membership_vacuity',imp(rel(a,b),modal(rel(a,b)))==TOP)
                    check('atomic_equality_vacuity',imp(eq(a,b),modal(eq(a,b)))==TOP)
            for a,b in product(range(3),repeat=2):
                # Rebinding a also changes b when the two *labels* coincide.
                values=[]
                for x in DOMAIN:
                    s=list(env);s[a]=x
                    values.append(TOP if s[a]==s[b] else BOT)
                check('rho1_equality_existence',exists(values)==TOP)
            for a in range(3):
                check('IR',universal((neg(relation[x,x]) for x in DOMAIN))==TOP)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    algebra_checks()
    equality_and_membership_checks()
    # In the relation with off-diagonal value E, let a!=b and c fresh.
    # A=R(a,b), P=forall c not A, F=R(0,0).
    A=E
    P=universal((neg(A),neg(A)))
    dne=imp(neg(neg(P)),P)
    peirce=imp(imp(imp(P,BOT),P),P)
    check('P_witness',P==(1,0))
    check('DNE_counterexample',dne==(1,1) and dne!=TOP)
    check('Peirce_counterexample',peirce==(1,1) and peirce!=TOP)
    check('fresh_vacuity_counterexample',imp(neg(A),P)==(1,1))
    a,b,c,u=BOT,neg(A),P,BOT
    definable_L=imp(imp(imp(c,u),a),imp(imp(a,c),imp(b,c)))
    check('definable_L_counterexample',definable_L==(1,1))
    failures=[]
    for a,b,c,u in product(H,repeat=4):
        L=imp(imp(imp(c,u),a),imp(imp(a,c),imp(b,c)))
        if L!=TOP: failures.append({'a':a,'b':b,'c':c,'u':u,'L':L})
    check('full_L_not_valid',bool(failures))
    report={
      'status':'All declared finite obligations passed.',
      'claim':'Logical-basis obstruction only; CP and GIC excluded.',
      'algebra':'C3 x C2, componentwise Heyting implication',
      'elements':H,'bottom':BOT,'top':TOP,'atomic_value':E,
      'modal_table':[[x,modal(x)] for x in H],
      'fixed_points':FIXED,
      'obligations':counts,'total_cases':sum(counts.values()),
      'witness':{'A':A,'P':P,'DNE':dne,'Peirce':peirce},
      'invalid_L_instances':len(failures),'first_invalid_L':failures[0],
      'definable_L_witness':{'a':BOT,'b':neg(A),'c':P,'u':BOT,'value':definable_L},
      'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'kernel_checked':False,'ordinary_first_order_model':False,
      'machine_state_bound_claimed':False}
    out=args.output
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report,indent=2,sort_keys=True))

if __name__=='__main__':main()
