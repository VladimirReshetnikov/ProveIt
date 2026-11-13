#!/usr/bin/env python3
"""Independent finite and source-interface review of the q=5 toy; no Lean."""
import hashlib,json,subprocess,sys
from math import comb
from pathlib import Path
D=Path(__file__).resolve().parents[2]; A=D/'research/ordinary14-direct-x73-q5-toy'
def sha(b): return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes(); assert sha(b)==h,str(p); return b
pin(A/'check.py','6ae4d7e5a9a2f7ba24f0d6188159d6689cac45f2538706e74a427dfe88458db1')
expected=pin(A/'result.json','36c780902131434a1b1e36b8caceb742996249c0ff61726e83a162a0c3c52ee0')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-direct-x73-q5-toy-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='3a31f47f48daf26b3381c39ae6a93c2fbae5b284a6c49fcd36a9052afcd0df7f'
pin(D/'research/ordinary13-folded-root86-negated-compact44-seed/README.md','7d1dc11038b1d12bb7862a226aabf1742823523bcc34adf9a7c82b7e3905c6f5')
pin(D/'research/current14-carrier64-pell-floor/README.md','8d3b46e7949b7db849a12ef1b6c3586cac661d3158e0347c402581c3b1d08db8')
graph=json.loads((D/'research/ordinary14-universal-trace-bound/candidate.json').read_text())
rows={name:(op,l,r) for name,op,l,r in graph['source']}
for name,row in {'Y':('*','q3','s'),'U':('*','Y','q2'),'ell':('*','E','kY'),
 'Dstar':('+','g58','g59'),'F0':('-','g38','g40'),
 'F1':('+',1,'A1'),'Fa':('-','y2','g82'),'Fs':('+',1,'g72'),
 'guard':('-','guard_base','bt_quotient'),'out':('-','P01234',1)}.items():
 assert rows[name]==row,(name,rows[name])
q=5; beta=4; F=2; alpha=1; K=1; MC=2; MF=5
G=beta*(q-F)+alpha; R=G*(q*q-1)+MC+q*MF; N=(R-1)//2; X=1<<R
assert (G,R,N)==(13,339,169) and R%4==3 and pow(2,R,5)==3
Y=sum(comb(2*N,j)*X**(N-j) for j in range(N+1))//2
assert Y%125==0 and (X*Y*Y)%(25*Y)==0
assert Y>X**N//2 and X>144*N and R+125+5+1<=625
assert (q-F-alpha)*(X+K)+(q-F)-beta*(1+X//2)==1
# Check the auxiliary same-index completion at an independent finite example.
def mul(u,v,d):return (u[0]*v[0]+d*u[1]*v[1],u[0]*v[1]+u[1]*v[0])
def pw(p,d,n):
 r=(1,0)
 while n:
  if n&1:r=mul(r,p,d)
  n//=2
  if n:p=mul(p,p,d)
 return r
x,y,rank=8,5,3; a=y*(x+1); delta=(a+2)**2-1
d,c=pw((a+2,1),delta,rank);f,L=pw((d,c),delta,c)
assert L%(c*c)==0
S=delta*L; assert S*S==delta*(f*f-1)
v0,yp=pw((S,1),S*S-1,rank);assert v0%S==0
V=v0//S; numerator=V+c+f*f*rank
assert numerator%(c*f*f)==0 and numerator>0
assert yp*yp-S*S*(yp*yp-V*V)==1
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not r.stderr and r.stdout==expected
print(json.dumps({'scope':'external symbolic source review and finite controls; no Lean or full parent exclusion',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'toy_rank':R,'auxiliary_finite_controls':1},sort_keys=True,indent=2))
