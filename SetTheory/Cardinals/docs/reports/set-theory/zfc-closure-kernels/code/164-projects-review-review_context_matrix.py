#!/usr/bin/env python3
"""Independent exhaustive review of the supplied finite context matrix."""
from itertools import product
from pathlib import Path
import json
import argparse
if not __debug__:raise RuntimeError('Run without Python optimization')
cli=argparse.ArgumentParser(description=__doc__);cli.add_argument('--output',type=Path,required=True);args=cli.parse_args()
M=[[3,3,2,3],[3,3,3,3],[0,3,3,3],[0,1,2,3]]
T=3;V=range(4)
def arrow(a,b):return M[a][b]
def axiom(a,b,c,u):return arrow(arrow(arrow(c,u),a),arrow(arrow(a,c),arrow(b,c)))
def fill(word,u,siblings):
 for letter,sibling in zip(reversed(word),reversed(siblings)):
  u=arrow(u,sibling)if letter=='L'else arrow(sibling,u)
 return u
assert arrow(T,T)==T
assert all(b==T for a,b in product(V,repeat=2)if a==T and arrow(a,b)==T)
assert all(axiom(a,b,c,T)==T for a,b,c in product(V,repeat=3))
family_checks={}
for word in ['','L','R','RRR']:
 count=0
 for values in product(V,repeat=len(word)+3):
  u,b,c,*siblings=values;a=fill(word,u,siblings);assert axiom(a,b,c,u)==T;count+=1
 family_checks[word or 'epsilon']=count
I=lambda a:arrow(a,a)
K=lambda a,b:arrow(a,arrow(b,a))
P=lambda a,b:arrow(arrow(arrow(a,b),a),a)
D=lambda a,b,c:arrow(arrow(a,b),arrow(arrow(arrow(a,c),a),b))
B=lambda a,b,c:arrow(arrow(a,b),arrow(arrow(b,c),arrow(a,c)))
S=lambda a,b,c:arrow(arrow(a,arrow(b,c)),arrow(arrow(a,b),arrow(a,c)))
assert all(I(a)==T for a in V)
assert all(K(a,b)==P(a,b)==T for a,b in product(V,repeat=2))
assert all(D(a,b,c)==T for a,b,c in product(V,repeat=3))
assert axiom(1,0,2,0)==2 and B(0,1,2)!=T and S(0,1,2)!=T
result={'status':'INDEPENDENT_EXHAUSTIVE_CONTEXT_MATRIX_REVIEW_PASS','table':M,'truth_and_designated_value':T,'zero_alias':True,'modus_ponens':True,'zero_family_assignments':64,'context_family_assignments':family_checks,'additional_valid_schemas':['I','K','Peirce','cd59'],'rho8_counterexample':[1,0,2,0],'rho8_counterexample_value':2,'B_S_counterexample':[0,1,2],'B_value':B(0,1,2),'S_value':S(0,1,2),'scope':'Propositional implication-context schemas only; not a model of total numerical destructors or the full native calculus.'}
args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
