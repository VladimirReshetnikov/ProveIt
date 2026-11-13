from pathlib import Path
from hashlib import sha256
import json,math,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary9-compact-partial-main-index-constraints')
for p,h in json.loads((D/'pins.json').read_text()).items(): assert sha256(Path(p).read_bytes()).hexdigest()==h,p
Q=Path('research/ordinary9-shifted-two-norm-compact-first-compatible-partial')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(Q/'check.py')])==(Q/'receipt.json').read_bytes()
s=Path('Lean/DiophantineConsistency/Compact44/Compact943Data.lean').read_text().split('-- BEGIN PINNED ORDERED ROWS')[1].split('-- END PINNED ORDERED ROWS')[0]
rows=[tuple(map(int,x)) for x in re.findall(r'\((\d+),\s*(\d+),\s*(\d+),\s*(\d+)\)',s)]
s=Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicKernel.lean').read_text()
slots=list(map(int,re.search(r'def slots : List ℕ := \[([^]]+)\]',s).group(1).split(',')))
assert len(rows)==943 and len(slots)==41
values=[1+2**10*(2**41-(a+2**8*b+2**17*c+2**25*d+127*2**34)) for a,b,c,d in rows]
results=[]
for p in (16267,16979):
    assert all(p%i for i in range(2,math.isqrt(p)+1))
    rho=pow(2,67,p);q=pow(2,67*8807,p);pw=[1]*5496
    for i in range(1,len(pw)):pw[i]=pw[i-1]*rho%p
    kp=(sum(pw[i] for i in (30,62,1100,2201,42))+sum(v*(pw[4393-i]+pw[5495-i]) for i,v in enumerate(values))+sum(pow(2,10+i,p)*(pw[4393-j]+pw[5495-j]) for i,j in enumerate(slots)))%p
    w=((q-2)*pow(2,-1,p)-kp)%p;X=q*w%p;H=(4*pow(q,3,p)*(X+1)+3)%p
    assert H==0 and X
    logs={};t=1
    while t not in logs: logs[t]=len(logs);t=2*t%p
    assert t==1
    results.append([p,q,kp,w,X,len(logs),logs[X],logs[-pow(X,-1,p)%p]])
assert results==[[16267,2086,6569,10740,3981,5422,553,2158],[16979,16434,1864,6352,1876,16978,10155,15312]]
period=math.lcm(5422,16978); assert period==46027358
for m,i in ((31198741,6),(37842296,7)):
    assert all(m%v[5]==v[i] for v in results) and 0<=m<period
# Independent bounded controls for the interval and uniqueness inequalities.
controls=0
for X in range(1,5):
 for Y in range(8,13):
  M=X*Y*Y; af=2*M+1; a=Y*(X+1); am=a+2
  assert 2*am<af and 2*am-1>2*(Y+1) and (2*am-1)**2>2*af
  tf,k=1,0
  for n in range(1,7):
   tf,k=af*tf+2*M*(M+1)*k,2*tf+af*k
   t,c=1,0;found=[]
   for m in range(1,2*n+3):
    t,c=am*t+(am*am-1)*c,t+am*c
    if Y*k<=c<(Y+1)*k:found.append(m)
   assert len(found)<=1 and all(n<m<2*n for m in found)
   controls+=1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'predecessor_receipt_reproduced':True,'verified_prime_data':results,'common_period':period,'plus_residue':31198741,'minus_residue':37842296,'growth_controls':controls,'lean_executed':False,'full_zero_proved':False},sort_keys=True,indent=2))
