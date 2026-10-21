"""Literal decoder-prefix census; no candidate execution or allocator."""
from pathlib import Path
import json,hashlib,argparse
ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
assert not args.output.exists(), 'output must be fresh'
R=args.repo.resolve();B=R/'Computability/BusyBeaver/Research/ZFC/candidate-k218'
T={}
for l in(B/'k218.native.tm').read_text().splitlines():
 if l and not l.startswith('#'):
  q,b,w,d,z=l.split();T[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(z))
rows=json.loads((B/'sites218.json').read_text());leaves={p:(i,op,arg)for i,(p,op,arg)in enumerate(rows)};prefixes={p[:i]for p in leaves for i in range(len(p))};entries={};cert=[]
def visit(p,q):
 if p in leaves:return
 entries.setdefault(q,[]).append(p)
 for bit in(0,1):
  child=p+str(bit)
  if child in leaves:continue
  assert child in prefixes
  O={-1}|{i for i,x in enumerate(child)if x=='1'};before=set(O);h=len(p);s=q;trace=[]
  for n in range(100):
   if h==len(p)+1:break
   assert -1<=h<len(child)
   b=int(h in O);w,d,z=T[s,b];trace.append([s,h,b,w,d,z]);O.add(h)if w else O.discard(h);s,h=z,h+d
  else:raise AssertionError(('bound',p,bit))
  assert O==before and h==len(p)+1
  if q in(196,122)or any(x[0]in(196,122)for x in trace):cert.append({'prefix':p,'state':q,'bit':bit,'target':s,'trace':trace})
  visit(child,s)
visit('',84)
result={'status':'SOURCE_PREFIX_CENSUS_PASS','paths':{str(q):entries.get(q,[])for q in(196,122,137,194,70,30)},'neighborhood':{str(q):{'rows':[T[q,b]for b in(0,1)],'incoming':[[s,b,*a]for(s,b),a in T.items()if a[2]==q]}for q in(196,122,137,194,70,30)},'certificates':cert,'source_fragments':{},'inputs':{str(p):hashlib.sha256(p.read_bytes()).hexdigest()for p in[B/'k218.native.tm',B/'sites218.json',Path(__file__)]}}
for q in(196,122):
 for p in entries.get(q,[]):
  result['source_fragments'][str(q)+':'+p]=[[i,path[len(p):],op,arg]for i,(path,op,arg)in enumerate(rows)if path.startswith(p)]
args.output.parent.mkdir(parents=True,exist_ok=True)
args.output.write_text(json.dumps(result,indent=2)+'\n')
print('paths',result['paths'])
for name,frag in result['source_fragments'].items():print(name,'leaves',len(frag),'first',frag[:15])
