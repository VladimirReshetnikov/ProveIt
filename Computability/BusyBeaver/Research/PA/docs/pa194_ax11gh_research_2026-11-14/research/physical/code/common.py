"""Portable source contracts for the frozen inputs; no repository reads."""
from pathlib import Path
import importlib.util,json
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('research_symbolic_runtime',ROOT/'vendor/symbolic_runtime.py')
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
def load_case(name):
 p=ROOT/'inputs'/name; rows={}
 for line in (p/'machine.native.tm').read_text().splitlines():
  q,b,w,d,n=line.split();rows[int(q),int(b)]=int(w),d=='R',int(n)
 sites=json.loads((p/'sites.json').read_text());ins=json.loads((p/'instructions.json').read_text())
 paths=[tuple(map(int,s[0])) for s in sites];cs=[]
 for i,op in enumerate(ins):
  st=c.frame(paths[i])
  def end(j,extra=0,effect=c.PLAIN):return c.canonical(c.frame(paths[j],extra,effect))
  if op[0]=='inc':cs.append((i,None,st,end(op[2],0,('x','inc',c.PHYSICAL[op[1]]))))
  elif op[0]=='dec':
   r,z,p=op[1:];cs.extend([(i,(c.PHYSICAL[r],True),st,end(z)),(i,(c.PHYSICAL[r],False),st,end(p,1,('x','dec',c.PHYSICAL[r])))])
  elif op[0]=='jump':cs.append((i,None,st,end(op[1])))
  else:assert op[0]=='halt';cs.append((i,None,st,None))
 return rows,sites,ins,cs

def startup_seed(path):
 expected={-3,46};expected.update(-2+i for i,b in enumerate(path) if int(b));pos=47
 for val in [0,0,0,0,0,0,2,0,0]+[1]*26:
  pos+=1;expected.update(range(pos,pos+val+1));pos+=val+1
 return expected
