#!/usr/bin/env python3
"""Static and finite-example audit of an uncompiled mathematical proof draft."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/current2011-sheared72-46-proof-draft/ShearDraft.lean';O=D/'Lean/DiophantineConsistency/ArithmeticCarrier94Indices.lean';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(P)=='a479640aa326cb2190d530bb806d199f29c77796acd8f93edaffe609e5a8af2a' and sha(O)=='afc99ad41536f55e0f467581e4fbdbd5308036f93b6e3e10b1a5d2f1c113de4a';s=P.read_text();o=O.read_text();assert 'UNCOMPILED DRAFT' in s and 'sorry' not in s and 'admit' not in s
for f in ['(hc : 0 < c) (hi : 0 < i) (hf : 0 < f)','(hmain : d*d = 1 + delta a*c*c)','(hord : (i*c*c)*(i*c*c) + delta a = delta a*f*f)','(hbig : (a+2)*delta a*delta a < c)','theorem auxiliary_shear','(hA : 1 ≤ A) (hy : 1 ≤ y)','(hV : V ≠ 1)','(hy : 1 ≤ y) (hI : 2 ≤ I) (hA : A=0 ∨ 2 ≤ A)','theorem auxiliary_abs']:assert f in s,f
# Verify the extraction preserves the proof-local dependency statements.
for f in ['solution_index a d c hmain','relaxed_auxiliary a c p i f hp hi hf hcp.symm hord\' hbig','ArithmeticPellStrongDivisibility.y_dvd_iff a p m','f*f=1+c*(delta a*t*ycoord m a)']:
 assert f in s and f in o,f
# Exhaustively test small integer specializations as counterexample search;
# this does not establish the universal ordered-ring lemmas.
positive_antecedents=0
for A in range(1,7):
 for V in range(-7,8):
  for y in range(1,7):
   z=A*(V*V-y*y)+y*y
   if z==1 and V!=1:
    positive_antecedents+=1;assert y>V
assert positive_antecedents>0
nonzero_antecedents=0
for A in [0,2,3,4,5,6]:
 for I in range(2,6):
  for V in range(-5,6):
   for y in range(1,6):
    for P0 in range(-2,3):
     for QW in range(-2,4):
      aux=A*(V*V-(V+y)**2)+(V+y)**2
      if P0*P0+aux*aux+(QW-1)**2+(I*I-A)**2-2==0:
       nonzero_antecedents+=1;assert V+y!=0
assert nonzero_antecedents>0
print(json.dumps({'status':'PASS_SCOPED_STATIC_REVIEW','positive_order_integer_examples':positive_antecedents,'nonzero_order_integer_examples':nonzero_antecedents,'scope':'Hypotheses/source comparison and finite counterexample search; no Lean replay or proof of remaining positivity/model/iPRA obligations.'},indent=2,sort_keys=True))
