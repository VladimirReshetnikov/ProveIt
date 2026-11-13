#!/usr/bin/env python3
"""Exact finite scalar counterexample; no graph-zero assertion."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
 raise SystemExit('invoke python3 -I -S -B')
here=Path(__file__).resolve().parent
candidate=here.parent/'trace74-mask-coordinate-probe/candidate.json'
assert hashlib.sha256(candidate.read_bytes()).hexdigest()=='dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353'
graph=json.loads(candidate.read_text());rows={r[0]:r[1:] for r in graph['source']}
# Evaluate only the required cones; K0, i, T, w and n are not supplied.
a={'beta':31,'J':1,'MC':14,'MF':43,'F':16,'C':17,'eta':1,'zeta':1}
def evaluate(n):
 if type(n) is int:return n
 if n in a:return a[n]
 op,x,y=rows[n];x=evaluate(x);y=evaluate(y)
 a[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]();return a[n]
R=evaluate('R');a['s']=R+1;c=evaluate('c');q=evaluate('q')
d=5; beta=a['beta'];MC=a['MC'];HP=a['MF']-beta; J=a['J'];F=a['F'];C=a['C'];M=MC*J+1;H=HP*J-1
pop=int.bit_count
assert (q,R,c)==(32,507775,33277607937)
assert q==2**d==beta*J+1 and 31<=beta and 0<MC<beta<a['MF']<2*beta
assert MC%2==0 and HP%8==4 and 0<=MC<q and 0<=HP<q and pop(MC)+pop(HP)==d
assert C>0 and C-1<q and F<q and M<q and HP*J>=1
assert R==(C-1)+M+q*(F+H)+q**2*(q-C)+q**3*(q-1-F)
assert pop(M)+pop(H)<=d+2 and 3*d+2<=pop(R)
assert (C-1)&M==0 and F&H==0
assert 3*q<R and R+q**3+q+1<q**4 and R%4==3 and 2*R<c
assert F>MC*J and F+C>q
assert hashlib.sha256(candidate.read_bytes()).hexdigest()=='dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353'
print(json.dumps({'status':'PASS','d':d,'beta':beta,'q':q,'J':J,'MC':MC,'MF':a['MF'],'HP':HP,'F':F,'C':C,'M':M,'H':H,'R':R,'R_population':pop(R),'M_population':pop(M),'H_population':pop(H),'mask_population':pop(MC)+pop(HP),'c':c,'eta':a['eta'],'zeta':a['zeta'],'s':a['s'],'alpha_for_old_graph':q-F-C,'source_candidate_sha256':'dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353','scope':'Exact finite scalar cones and inequalities only; non-fixed ports, no full graph zero, no fixed-BFS or iPRA claim.'},sort_keys=True,indent=2))
