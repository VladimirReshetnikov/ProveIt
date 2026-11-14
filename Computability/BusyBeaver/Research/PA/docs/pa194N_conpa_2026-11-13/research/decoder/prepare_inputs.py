"""Expose one level of every pure-reader AX macro and retain fixed pairs.
Research input generation only; the complete source graph must be rechecked.
"""
from pathlib import Path
import json,re
import argparse
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--repo',type=Path,required=True)
ap.add_argument('--output',type=Path,required=True)
ap.add_argument('--depth',type=int,choices=[1,2],default=1)
ap.add_argument('--controller',choices=['original','nopush'],default='original')
args=ap.parse_args()
HERE=args.output.resolve();HERE.mkdir(parents=True,exist_ok=True)
REPO=args.repo.resolve()
BASE=REPO/'Computability/BusyBeaver/Research/PA/docs/pa194_conpa_2026-11-13'
nodes={}
for line in (REPO/'Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/PA196/Program.lean').read_text().splitlines():
 m=re.match(r'def (\w+) : Tree := \.node (.*)',line)
 if m:
  tok=re.findall(r'\(\.leaf \(\.(\w+)(?: (\d+))?\)\)|\b((?:node|x)\d+)\b',m[2])
  nodes[m[1]]=tuple(n if n else ('leaf',op,int(a) if a else None) for op,a,n in tok)
r={}
for ln in (BASE/'construction/tables/unfolded201.native.tm').read_text().splitlines():
 q,b,w,d,n=ln.split();r[int(q),int(b)]=int(w),int(d=='R'),int(n)
mac={'node65':90,'node55':98,'node58':12,'node70':166,'node49':19,'node72':69,'node75':213,'node142':194,'node150':221,('leaf','inc',1):61,'node60':99,'node61':190,('leaf','breakTo',1):-1}
original=dict(mac)
expansions={}
def expose(t,level):
 q=mac[t]
 if not level or not isinstance(t,str) or r[q,0][:2]!=(0,1) or r[q,1][:2]!=(1,1):return t
 for k,act in zip(nodes[t],(r[q,0],r[q,1])):
  if k in mac:assert mac[k]==act[2],(k,q)
  else:mac[k]=act[2]
 return tuple(expose(k,level-1) for k in nodes[t])
for t,q in original.items():expansions[t]=expose(t,args.depth if t in ('node65','node49','node75','node150') else 1)
# Retain source name identity even where a physical reader is shared by contexts.
assert len(set(mac.values()))==len(mac)
def expanded(t):
 if isinstance(t,str):return expanded(nodes[t])
 if t[0]=='leaf':return t
 return tuple(map(expanded,t))
def attrs(t):
 t=expanded(t)
 if t[0]=='leaf':return(0,0,0,0,int(t[1]=='inc'))
 a,b=map(attrs,t)
 return 1+max(a[0],b[0]),a[1]+1,max(a[1]+1,a[2],b[2]),max(a[3],b[3],1+a[1] if a[4] else 0),a[4]
(HERE/'leaf_attrs.txt').write_text(str(len(mac))+'\n'+''.join(str(q)+' '+' '.join(map(str,attrs(t)))+'\n' for t,q in mac.items()))
def gram(path):
 d=json.loads(path.read_text());rules=d['rules']
 def go(t):
  if isinstance(t,list):t=tuple(t)
  if isinstance(t,str) and t in rules:return tuple(map(go,rules[t]))
  return expansions[t]
 return go(d['root'])
seedpaths=[BASE/'construction/source/pa194.grammar.json',BASE/'construction/inputs/parent195S.grammar.json']
seeds=list(map(gram,seedpaths))
if args.controller=='nopush':
 assert r[164,1]==(1,1,98);r[164,1]=(1,1,114)
fixed=sorted({q for q,b in r if q<1300})
lines=[str(len(fixed))]+[' '.join(map(str,[q,*r[q,0],*r[q,1]])) for q in fixed]+[str(len(seeds))]
for i,root in enumerate(seeds):
 arr=[];ix={}
 def visit(t):
  if t in ix:return ix[t]
  z=[1,visit(t[0]),visit(t[1]),0] if isinstance(t,tuple) and len(t)==2 else [0,mac[t],-1,-1]
  ix[t]=len(arr);arr.append(z);return ix[t]
 rt=visit(root);lines.append(f'{i} {len(arr)} {rt}');lines+=[' '.join(map(str,a)) for a in arr]
(HERE/'seeds.txt').write_text('\n'.join(lines)+'\n')
(HERE/'source_map.json').write_text(json.dumps({str(q):list(k) if isinstance(k,tuple) else k for k,q in mac.items()},indent=2)+'\n')
print('Expanded roots:',{str(k):v for k,v in expansions.items() if k!=v})
