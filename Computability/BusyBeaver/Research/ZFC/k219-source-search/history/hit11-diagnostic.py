import sys,json,random,hashlib
from pathlib import Path
sys.path.insert(0,'Computability/BusyBeaver/Research/ZFC/k219-source-search')
from model import *
hits=list(map(freeze,json.loads(HITS.read_text())));h=hits[11];cleanup=h[1]
assert cleanup==((('CD',5),('CI',6)),((('CD',6),('CC',2)),('CB',1)))
rng=random.Random(219207);cases=[(a,b) for a in range(13) for b in range(13)]+[(0,10000),(10000,0),(10000,10000),(9999,10000),(10000,9999)]+[(rng.randrange(1001),rng.randrange(1001)) for _ in range(20)]
def run(t,a,b):
 g=localg(t);pc=0;r=[17,19,23,29,31,a,b,37,41]
 for k in range(64*(a+b+2)):
  op,i,ts=g[pc]
  if op=='CI':r[i]+=1;pc=ts[0]
  elif op=='CD':
   pos=r[i]>0
   if pos:r[i]-=1
   pc=ts[int(pos)]
  else:assert op in ('CB','CC');pc=ts[0]
  if pc<0:return pc,r,k+1
 raise AssertionError('budget')
for a,b in cases:
 e,r,k=run(cleanup,a,b);assert e==-2 and r==[17,19,23,29,31,0,0,37,41] and k==4*a+3*b+3
 e,r,k=run(h,a,b);assert e==(-1 if a==b else -2) and r==[17,19,23,29,31,0,0,37,41]
out={'status':'HIT11_FINITE_TRANSCRIPTION_DIAGNOSTIC_PASS','cases':len(cases),'checks_per_case':['full clean equality contract','cleanup Break1 + full register vector','exact cleanup4a+3b+3 step formula'],'scope':'Finite diagnostic; separate ordinary induction proves all-natural claim.','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'hits_sha256':hashlib.sha256(HITS.read_bytes()).hexdigest()}
p=HERE/'results/hit11-diagnostic.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');print(out)
