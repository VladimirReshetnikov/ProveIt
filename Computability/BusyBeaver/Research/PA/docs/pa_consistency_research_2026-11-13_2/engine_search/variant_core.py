from pathlib import Path
import json,sys
import symbolic_core as c
ALLOC=Path(__file__).resolve().parent / 'inputs' / 'ProveIt'
sys.path.insert(0,str(ALLOC))
import source_language as sl

def load(path):
 path=Path(path)
 T={}
 for line in (path/'candidate.native.tm').read_text().splitlines():
  if line.startswith('#') or not line:continue
  q,b,w,d,n=line.split();T[int(q),int(b)]=(int(w),d=='R',int(n))
 sites=json.loads((path/'sites.json').read_text());graph,_=sl.graph_arithmetic(sites)
 assert graph==sl.graph_intervals(sites)
 contracts=[]
 for i,((effect,targets),(p,op,arg))in enumerate(zip(graph,sites)):
  p=tuple(map(int,p));st=c.frame(p)
  def frame(j,extra=0,eff=c.PLAIN):return c.canonical(c.frame(tuple(map(int,sites[j][0])),extra,eff))
  if effect[0]=='increment':contracts.append((i,None,st,frame(targets[0],0,('x','inc',c.PHYSICAL[arg]))))
  elif effect[0]=='decrement':
   contracts.append((i,(c.PHYSICAL[arg],True),st,frame(targets[0])))
   contracts.append((i,(c.PHYSICAL[arg],False),st,frame(targets[1],1,('x','dec',c.PHYSICAL[arg]))))
  elif effect[0]=='identity':contracts.append((i,None,st,frame(targets[0])))
  else:contracts.append((i,None,st,None))
 return T,sites,contracts
