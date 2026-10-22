#!/usr/bin/env python3
"""Independent restricted readers for delivered literal data; never import delivery code."""
import hashlib,json,re
from pathlib import Path
P=Path(__file__).resolve().parent
R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
I=P/'review-inputs'
pins={}
def read(p):
 b=p.read_bytes();pins[str(p)]={'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()};return b.decode()
def declaration(s,n):
 return re.search(r'Definition '+re.escape(n)+r'\s*:[^\n]+:=\s*\n(.*?)\.\s*\n',s,re.S).group(1)
class Parser:
 def __init__(self,s):
  self.ts=re.findall(r'%positive|%N|Branch|Empty|Test|Arc|Halt|[0-9]+|[()\[\],;]',s);self.i=0
  assert re.sub(r'\s+','',s)==''.join(self.ts),'unparsed token'
 def pop(self,w=None):
  x=self.ts[self.i];self.i+=1
  if w is not None:assert x==w,(w,x,self.i)
  return x
 def num(self,suffix=None):
  x=int(self.pop())
  if suffix:self.pop(suffix)
  return x
 def arc(self):
  self.pop('(');self.pop('Arc');dest=self.num('%N');self.pop('[');pairs=[]
  while self.ts[self.i]!=']':
   self.pop('(');a=self.num();self.pop(',');b=self.num();self.pop(')');pairs.append((a,b))
   if self.ts[self.i]==';':self.pop(';')
   else:break
  self.pop(']');self.pop(')');return dest,pairs
 def node(self):
  if self.ts[self.i]=='Halt':self.pop();return None
  self.pop('(');self.pop('Test');r=self.num();a=self.arc();b=self.arc();self.pop(')');return r,a,b
 def tree(self,value,low=-1,high=10**100):
  if self.ts[self.i]=='Empty':self.pop();return {}
  self.pop('(');self.pop('Branch')
  left=self.tree(value,low,high)
  key=self.num('%N');val=value();right=self.tree(value,low,high);self.pop(')')
  assert low<key<high and all(k<key for k in left) and all(k>key for k in right)
  assert not set(left)&set(right) and key not in left and key not in right
  return {**left,key:val,**right}
 def parse(self,kind):
  v=self.node if kind=='node' else (lambda:self.num('%positive' if kind=='positive' else None))
  d=self.tree(v);assert self.i==len(self.ts);return d
s=read(I/'affine_core/K215DrainData.v')
g=Parser(declaration(s,'k215_tree')).parse('node')
ranks=Parser(declaration(s,'rank_tree')).parse('nat')
def drain(v):
 x=g[v]
 return x is not None and x[1][0]==v and sum(n for r,n in x[1][1] if r==x[0])==0
drains={v for v in g if drain(v)};core=set(g)-drains
assert len(g)==1426 and len(drains)==1059 and len(core)==367
assert set(ranks)==drains and max(ranks.values())==6
assert sum(g[v] is None for v in core)==1 and g[0]==(8,(9,[]),(2,[]))
for v,x in g.items():
 if x is not None:
  assert x[0]<9
  for w,inc in x[1:]:
   assert w in g and all(0<=r<9 and n>0 for r,n in inc)
 if v in drains:assert ranks.get(g[v][2][0],0)<ranks[v]<=6
 v0=v
 for _ in range(6):
  if drain(v):v=g[v][2][0]
 assert v in core,v0
s=read(I/'affine_core/K215GraphBinding.v')
locs={name:Parser(declaration(s,name)).parse('positive') for name in ['locations_source','locations_reference']}
assert all(set(d)==set(g) for d in locs.values())
# Compare the delivered old literal dense table with the maintained exact table.
s=read(I/'lean_integration/cm215/CM215Tables.lean')
def actions(name):
 body=re.search(r'def '+name+r' : List Action := \[(.*?)\n\]',s,re.S).group(1)
 tok=re.findall(r'⟨(true|false), (true|false), ([0-9]+)⟩',body)
 assert re.sub(r'\s','',body)==','.join('⟨'+','.join(x)+'⟩' for x in tok)
 return [(a=='true',b=='true',int(c)) for a,b,c in tok]
old,new=actions('oldRows'),actions('newRows');assert len(old)==len(new)==430
cur=read(R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KDense215.lean')
body=cur.split('def rows215 :',1)[1].split(':= [',1)[1].split('\n]',1)[0]
actual=[(a=='true',b=='true',int(c)) for a,b,c in re.findall(r'\((true|false), (true|false), ([0-9]+)\)',body)]
assert actual==old
changed=[{'state':i//2,'read':i%2,'old':a,'new':b} for i,(a,b) in enumerate(zip(old,new)) if a!=b]
assert all(0<=a[2]<=215 for a in old+new)
# Exact implemented module alias census from the reviewed placement map.
m=json.loads((R/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake212-placement.json').read_text())
cm=[{'member':x['member'],'route':x['route'],'commit':x.get('commit'),'path':x.get('path')} for x in m['members'] if '/cm215/' in x['member'] and x['member'].endswith('.lean')]
assert len(cm)==8 and sum(x['route']=='git' for x in cm)==7
result={'status':'PASS_INDEPENDENT_LITERAL_SOURCE_READING','inputs':pins,'affine':{'vertices':len(g),'drains':len(drains),'core':len(core),'core_tests':sum(g[v] is not None for v in core),'core_halts':sum(g[v] is None for v in core),'rank_max':max(ranks.values()),'both_arc_targets_closed':True,'all_vertices_reach_core_within_six_drain_hops':True,'both_source_location_key_sets':1426},'cm215':{'old_actions_match_current_dense':430,'new_actions':430,'changed_rows':changed,'module_routes':cm},'scope':'Own finite literal parsing only: no submitted code, proof compiler, runtime execution, source segment checker, or checksum-manifest content execution. This does not certify the 2852 literal source-segment bindings or formal endpoint.'}
(P/'literal-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='inputs'},indent=2))
