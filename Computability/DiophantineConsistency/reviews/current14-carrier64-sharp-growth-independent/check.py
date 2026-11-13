#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
from collections import defaultdict
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];pkg=root/'research/current14-carrier64-sharp-growth';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
# Independently expand (2A−1)^2−(X+1)(2P) in Z[X,Y].
def add(a,b):
 c=defaultdict(int,a)
 for m,v in b.items():c[m]+=v
 return {m:v for m,v in c.items() if v}
def mul(a,b):
 c=defaultdict(int)
 for (i,j),u in a.items():
  for (k,l),v in b.items():c[i+k,j+l]+=u*v
 return {m:v for m,v in c.items() if v}
def neg(a):return {m:-v for m,v in a.items()}
base={(1,1):2,(0,1):2,(0,0):3};den={(1,2):4,(0,0):2};xp={(1,0):1,(0,0):1}
assert add(mul(base,base),neg(mul(xp,den)))=={(1,2):4,(0,2):4,(1,1):12,(0,1):12,(1,0):-2,(0,0):7}
# Lower 2p−1 and upper 2p factors; monotone recurrence is the induction ingredient.
for p in range(2,50):
 a,b=0,1
 for t in range(1,40):
  assert (2*p-1)**(t-1)<=b<=(2*p)**(t-1) and b>=a>=0
  a,b=b,2*p*b-a
# Check X>8N and the geometric bound, plus strict interval in manageable cases.
for R in range(27,102,2):
 N=(R-1)//2;X=1<<R
 assert X>8*N and (X+2)**(2*N)<2*X**(2*N) and (X+1)**N>=X**N+2
 for t in range(1,R+1):assert R*N-3*t-1>=0
for f in ('current14-carrier64-growth-window-independent','current14-carrier64-two-sided-window-partial-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
x=subprocess.run([sys.executable,'-I','-S','-B',str(pkg/'check.py')],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)==json.loads((pkg/'result.json').read_text()) and json.loads(x.stdout)['checker_sha256']==sha(pkg/'check.py')
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','scope':'conditional sharp interval X^N/2 < Y < X^N; excludes power-of-two s and reviewed third partial; no general reverse-map or new Lean client'},indent=2))
