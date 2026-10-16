#!/usr/bin/env python3
"""Exhaustive algebraic obstruction to replacing rho8 by K and S alone.

The scope is the genuine-bottom named Tarski logical calculus with no
nonlogical theory. It is not a model of CP/GIC/PSC, and it does not directly
interpret the numeric alias F = Rel(0,0). All membership atoms have value 4,
whereas the logical bottom has value 0.
"""
from pathlib import Path
import argparse
import itertools
import json

H = (0,2,3,4,6,7)
UP = (3,2,4)
TOP = 7
BOT = 0
Q = {0:0,2:0,3:2,4:4,6:4,7:7}
REL = 4
EQ = TOP

def require(condition, message):
    if not condition:
        raise ValueError(message)

def implies(a,b):
    """Heyting implication of upsets: {i: up(i) intersect a subset b}."""
    return sum(1<<i for i,up in enumerate(UP) if up&a&~b == 0)

def neg(a):
    return implies(a,BOT)

def peirce(a,b):
    return implies(implies(implies(a,b),a),a)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    require(tuple(s for s in range(8) if all(not(s>>i&1) or up&s==up
              for i,up in enumerate(UP)))==H,'domain is not the upset lattice')
    checks={}
    def check(name, tuples, pred):
        total=0
        for case in tuples:
            total+=1
            require(pred(*case),name+': failure at '+str(case))
        checks[name]=total
    check('implication closed',itertools.product(H,repeat=2),lambda a,b: implies(a,b) in H)
    check('implication top iff order',itertools.product(H,repeat=2),
          lambda a,b:(implies(a,b)==TOP)==(a&~b==0))
    check('modus ponens',itertools.product(H,repeat=2),
          lambda a,b:not(a==TOP and implies(a,b)==TOP) or b==TOP)
    check('K',itertools.product(H,repeat=2),lambda a,b:implies(a,implies(b,a))==TOP)
    check('S',itertools.product(H,repeat=3),lambda a,b,c:
          implies(implies(a,implies(b,c)),implies(implies(a,b),implies(a,c)))==TOP)
    check('ex falso',itertools.product(H,repeat=1),lambda a:implies(BOT,a)==TOP)
    check('rho2 quantified distribution',itertools.product(H,repeat=2),lambda a,b:
          implies(Q[implies(a,b)],implies(Q[a],Q[b]))==TOP)
    check('rho4 quantifier commutation',itertools.product(H,repeat=1),lambda a:
          implies(Q[Q[a]],Q[Q[a]])==TOP)
    check('rho6',itertools.product(H,repeat=1),lambda a:
          implies(neg(Q[neg(Q[a])]),a)==TOP)
    check('rho1 equality existence',[()],lambda:neg(Q[neg(EQ)])==TOP)
    check('rho7 Euclidean equality',[()],lambda:implies(EQ,implies(EQ,EQ))==TOP)
    check('rho3 and rho5 membership transport',[()],lambda:implies(EQ,implies(REL,REL))==TOP)
    check('atomic relation vacuity',[()],lambda:implies(REL,Q[REL])==TOP)
    check('atomic equality vacuity',[()],lambda:implies(EQ,Q[EQ])==TOP)
    check('GEN preserves designated truth',[()],lambda:Q[TOP]==TOP)
    value_p=Q[neg(REL)]
    value_pierce=peirce(value_p,BOT)
    require(value_p==2,'wrong witness value')
    require(value_pierce==6 and value_pierce!=TOP,'Peirce witness does not fail')
    result={
      'scope':'genuine-bottom Tarski logic; no CP/GIC/PSC or numeric alias model claimed',
      'carrier':H,'point_upper_sets':UP,'top':TOP,'bottom':BOT,
      'quantifier':Q,'all_equality_atoms':EQ,'all_membership_atoms':REL,
      'implication_table':[[implies(a,b) for b in H] for a in H],
      'negation':{a:neg(a) for a in H},
      'checks':checks,'total_finite_checks':sum(checks.values()),
      'witness':{'formula':'P = forall v0 (Rel(v0,v0) -> bottom)',
                 'P':value_p,'not_not_P':neg(neg(value_p)),
                 'Peirce(P,bottom)':value_pierce,'designated':False},
    }
    text=json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
