"""Generate a reproducible, separately counted oracle and padding audit."""
import json, random, sys
from pathlib import Path
from time import perf_counter
from unknot_windows import Diagram, low_window, probe, adaptive_probe
from unknot_windows.cube import cube_ranks
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tests'))
from test_windows import random_knots

def discrepancy(d,ranks):
 n=len(d.pd); neg=sum(s<0 for s in d.signs())
 bad=[r for r in range(n+1) if ranks.get(r,0)!=(2 if r==neg else 0)]
 return min((min(r,n-r) for r in bad),default=None)

def main():
 start=perf_counter(); cases=[]; checks=0; stages=0
 for b,w,d in random_knots(seed=1701,count=100,max_crossings=9):
  truth=cube_ranks(d); n=len(w); outputs=[]
  for k in sorted({0,1,2,n}):
   r=low_window(d,k,trace=True)
   assert r.ranks=={h:v for h,v in truth.items() if h<=k}
   checks+=1; stages+=len(r.stages) if r.certificate.nice else 0
   outputs.append({'k':k,'ranks':r.ranks,'nice':r.certificate.nice,'girth':r.certificate.girth})
  p=adaptive_probe(d)
  assert p.verdict==('UNKNOT' if sum(truth.values())==2 else 'NONTRIVIAL')
  cases.append({'strands':b,'word':w,'full_ranks':truth,'windows':outputs,'adaptive_verdict':p.verdict})
 padding=[]
 for b,w in [(2,[1]*3),(3,[1,-2]*2),(3,[1,2]*4)]:
  d=Diagram.from_braid(b,w); truth=cube_ranks(d); delta=discrepancy(d,truth)
  for s in range(5):
   padded=Diagram.from_braid(b,w+[1,-1]*s)
   ranks=low_window(padded,len(padded.pd)).ranks
   assert ranks=={r+s:v for r,v in truth.items()}
   newdelta=discrepancy(padded,ranks); assert newdelta==delta+s
   padding.append({'base_strands':b,'base_word':w,'pairs':s,'n':len(padded.pd),'delta':newdelta,
                   'expected_delta':delta+s,'probe0':probe(padded,0).verdict})
 result={'seed':1701,'independent_cube_cases':len(cases),'window_comparisons':checks,
         'certified_nice_stages_checked':stages,'padding_cases':len(padding),
         'failures':0,'elapsed_seconds':perf_counter()-start,'cases':cases,'padding':padding}
 Path('results').mkdir(exist_ok=True)
 Path('results/validation.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k not in ('cases','padding')},indent=2))
if __name__=='__main__': main()
