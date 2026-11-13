#!/usr/bin/env python3
"""Independent graph, mod-4, signed-index and modulus-size controls."""
import hashlib,json,math
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for name,digest in json.loads((here/'pins.json').read_text()).items():
 assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
path='research/ordinary13-free-aux-square-compact-factor-obstruction/candidate.json'
r={x[0]:x[1:] for x in json.loads((root/path).read_text())['source']}
expected={'qm':['*','n_J','beta'],'q':['+',1,'qm'],'X':['*','q','n_w'],
 'q2':['*','q','q'],'q3':['*','q','q2'],'s':['+','n_s',1],
 'Y':['*','q3','s'],'U':['*','Y','q2'],'E':['*','X','Y'],
 'a':['+','E','Y'],'H':['+',3,'g15'],'Delta':['+','H','g17'],
 'r0base':['-','kbase','R'],'r0':['-','r0base',1],
 'g54':['*','U','n_gamma'],'shift':['-','g54','r0'],
 'b0':['+','X','g19'],'g58':['*','U','b0'],'g59':['*','H','shift'],
 'Dstar':['+','g58','g59'],'A1':['-','g61','g65'],
 'F1':['+',1,'A1'],'P01':['*','F0','F1'],
 'P012':['*','P01','Fa'],'P0123':['*','P012','Fs'],'out':['-','P0123',1]}
for k,v in expected.items():assert r[k]==v,(k,r[k])
src=(root/'Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
assert 'def betaNat : ℕ := 2^(67*8807)-1' in src
assert 67*8807==590069
rec=(root/'Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean').read_text()
for token in ('xcoord (time+1) b=(b+2)*xcoord time b+delta b*ycoord time b', 'ycoord (time+1) b=xcoord time b+(b+2)*ycoord time b'):
 assert token in rec,token
# Independently check all residues for the actual Delta shape.
for a in range(4):
 for c in range(4):
  t=(1+(a*a+4*a+3)*c*c)%4
  assert t in (0,1)
  for u in range(4):
   for d in range(4):assert (1+d*d-u*u*t)%4!=3
# Recurrence/conjugate and both signed-root size inequalities, including m=N.
controls=0
for N in range(2,13):
 q=1<<N;a=q**3*(q+1);H=4*a+3;A=a+2;U=q**5
 assert H%2==1 and math.gcd(H,U)==1 and H>q*q+1
 x,y=1,0
 for m in range(1,N+1):
  x,y=A*x+(A*A-1)*y,x+A*y
  assert x*x-(A*A-1)*y*y==1
  assert (x-a*y-pow(2,m,H))%H==0
  assert (x-a*y)*(x+a*y)%H==1
  if m<N:
   assert 0<q-2**m<H and (2**m-q)%H!=0
   controls+=1
  else:assert (2**m-q)%H==0
  assert 0<q*2**m+1<H and (q*2**m+1)%H!=0
print(json.dumps({'graph_rows_verified':len(expected),'all_256_mod4_unit_cases':True,
 'positive_and_negative_signed_main_controls':controls,
 'negative_sign_impossible_at_m_equal_N':True,
 'm_equal_N_positive_sign_left_open':True,'fixed_compact_early_indices_excluded':True,
 'full_graph_globally_unsolvable':False,'lean_executed':False},indent=2,sort_keys=True))
