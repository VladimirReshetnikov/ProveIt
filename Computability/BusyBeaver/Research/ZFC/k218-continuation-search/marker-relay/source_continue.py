"""Exact finite source continuation from the observed relay frame; independent of binary correctness."""
from pathlib import Path
import argparse,json,gzip,hashlib
ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--step-bound',type=int,default=1000000);a=ap.parse_args();assert a.step_bound>0;assert not a.output.exists()
P=a.repo/'Computability/BusyBeaver/Research/ZFC/candidate-k218'
if not __debug__:raise RuntimeError("Run without -O")
for rel,expected in {'sites218.json': 'b0169f2d477d0584ac70f9bdb79c3a78ef2bc700d080b3cd80976210235b80d9'}.items():
 if hashlib.sha256((P/rel).read_bytes()).hexdigest()!=expected:raise ValueError("Input changed: "+rel)
R=Path(__file__).resolve().parent/'evidence/first-clean-frame.json';F=json.loads(R.read_text())
S=json.loads((P/'sites218.json').read_text());by={p:i for i,(p,*_)in enumerate(S)};prefixes={p[:j]for p in by for j in range(len(p))}
def resolve(word):
 p=''
 for j in range(64):
  if p in by:return by[p]
  assert p in prefixes
  p+=word[j]if j<len(word)else'0'
 raise AssertionError('no leaf')
def inc(p):
 n=len(p);x=(int(p,2)if p else 0)+1;return format(x%(2**n),'0'+str(n)+'b')if n else''
def strip(p,b,k):
 for j in range(len(p)-1,-1,-1):
  if p[j]==b:
   k-=1
   if k==0:return p[:j]
 return''
i=F['ordinal'];r=F['registers'].copy();trace=[];status='BOUND';bound=a.step_bound;executed=0
for step in range(bound):
 p,op,k=S[i];trace.append([i,r.copy()])
 if op=='CH':status='HALT';break
 if step and i in(0,9) and all(r[j]==0 for j in(1,2,3,5,6,7)):
  status='ROOT_SHAPED_SOURCE_BOUNDARY';break
 if op=='CI':r[k]+=1;w=inc(p)
 elif op=='CD'and r[k]:r[k]-=1;w=inc(p)
 elif op in('CD','CB'):w=inc(strip(p,'0',k if op=='CB'else 1))
 elif op=='CC':w=strip(p,'1',k)
 else:raise AssertionError(op)
 i=resolve(w);executed+=1
 if max(r).bit_length()>4096:status='INTEGER_BIT_BOUND';break
out=a.output;out.mkdir()
with gzip.open(out/'trace.json.gz','wt')as f:json.dump(trace,f,separators=(',',':'))
result={'status':status,'instruction_bound':bound,'source_steps':executed,'ordinal':i,'site':S[i],'registers':r,'initial_frame':F,'scope':'Finite exact source execution only. Requires a separate binary simulation proof to transfer to the candidate. No semantic calibration from arbitrary proof list is asserted.','inputs':{str(p):hashlib.sha256(p.read_bytes()).hexdigest()for p in[P/'sites218.json',R,Path(__file__)]}}
(out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(status,executed,i,r)
