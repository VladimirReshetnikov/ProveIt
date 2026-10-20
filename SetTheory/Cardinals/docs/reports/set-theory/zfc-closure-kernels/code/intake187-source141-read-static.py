"""Independent literal/source data check only; imports no delivered module."""
from pathlib import Path
import hashlib,json,subprocess
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
PKG=Path('/tmp/zfc-intake187/K219_Alternatives_2026-10-20/K219_Alternatives_2026-10-20')
OUT=Path(__file__).parent
BASE=ROOT/'Computability/BusyBeaver/Research/ZFC/candidate-k219'
def desc(p):return {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def table(p):
 d={}
 for line in p.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,di,z=line.split();k=(int(q),int(b));assert k not in d and di in ('L','R')
  d[k]=(int(w),di,int(z))
 assert len(d)==438 and len({q for q,b in d})==219
 return d
def tree(rows):
 leaves={p:(op,arg) for p,op,arg in rows};assert len(leaves)==4744
 nodes=dict(leaves)
 for p in sorted({p[:i] for p in leaves for i in range(len(p))},key=len,reverse=True):
  assert p not in leaves and p+'0' in nodes and p+'1' in nodes
  nodes[p]=(nodes[p+'0'],nodes[p+'1'])
 assert [p for p,_,_ in rows]==sorted(leaves)
 return nodes[''],len(set(nodes.values()))
def cfg(rows):
 leaf={p:i for i,(p,_,_) in enumerate(rows)}
 def enter(p):
  while p not in leaf:p+='0'
  return leaf[p]
 def after(p):
  p=p.rstrip('1')
  return enter(p[:-1]+'1') if p else 0
 def control(p,bit,n):
  for i in range(len(p)-1,-1,-1):
   if p[i]==bit:
    n-=1
    if n==0:return after(p[:i]) if bit=='0' else enter(p[:i])
  return 0
 return [([] if op=='CH' else [after(p)] if op=='CI' else [control(p,'0',1),after(p)] if op=='CD' else [control(p,'0' if op=='CB' else '1',a)]) for p,op,a in rows]
def rewrite(t,a,b):
 if t==a:return b,1
 if isinstance(t[0],str):return t,0
 l,n=rewrite(t[0],a,b);r,m=rewrite(t[1],a,b);return (l,r),n+m
files={'baseline':BASE/'sites219.json'}
files.update({n:PKG/'machine'/n/'sites.json' for n in ('zero_terminal','retagged','composed')})
data={n:json.loads(p.read_text()) for n,p in files.items()}
trees={n:tree(r) for n,r in data.items()};graphs={n:cfg(r) for n,r in data.items()}
I=('CI',1);D5=('CD',5);D6=('CD',6);P=(D6,('CC',2));U=(P,('CB',1));V=(P,D6);Z=(D5,('CC',1))
old=(((D5,U),D6),(Z,U));new=(((D5,V),D6),(Z,V))
rot=(((I,I),(I,I)),('CC',2));rot2=((I,I),((I,I),('CC',3)))
assert rewrite(trees['baseline'][0],old,new)==(trees['zero_terminal'][0],4)
assert rewrite(trees['baseline'][0],rot,rot2)==(trees['retagged'][0],81)
assert rewrite(trees['zero_terminal'][0],rot,rot2)==(trees['composed'][0],81)
assert rewrite(trees['retagged'][0],old,new)==(trees['composed'][0],4)
assert graphs['baseline']==graphs['retagged'] and graphs['zero_terminal']==graphs['composed']
zero=[4570,4576,4588,4594,4602,4608,4711,4717]
for oldkey,newkey in [('baseline','zero_terminal'),('retagged','composed')]:
 a,b=data[oldkey],data[newkey];assert [i for i in range(4744) if a[i]!=b[i]]==zero
 incoming={i:[] for i in zero}
 for j,edges in enumerate(graphs[newkey]):
  for guard,k in enumerate(edges):
   if k in incoming:incoming[k].append((j,guard))
 for i in zero:
  assert a[i][1:]==['CB',1] and b[i][1:]==['CD',6] and a[i][0]==b[i][0]
  assert incoming[i]==[(i-2,0)] and a[i-2]==b[i-2] and b[i-2][1:]==['CD',6]
  assert graphs[oldkey][i]==graphs[newkey][i][:1]
base=table(BASE/'k219.native.tm');row=table(BASE/'variant-row157/k219-row157.native.tm')
assert {k:v for k,v in row.items() if base[k]!=v}=={(157,1):(1,'L',187)}
helpers={(157,1):(1,'L',148),(148,0):(0,'R',186),(187,0):(0,'R',186),(187,1):(1,'R',76),(76,1):(1,'L',148)}
res={}
for n in ('zero_terminal','retagged','composed'):
 p=PKG/'machine'/n/'k219.upstream-labels.tm';t=table(p)
 assert t.keys()==base.keys() and {k:t[k] for k in helpers}==helpers
 normalized=table(PKG/'machine'/n/'k219.native.tm');ren=lambda q:{102:301,120:302}.get(q,q)
 assert {(ren(q),b):(w,d,ren(z)) for (q,b),(w,d,z) in normalized.items()}==t
 res[n]={'source':desc(files[n]),'table':desc(p),'dag':trees[n][1], 'guard_cases':sum(2 if op=='CD' else 1 for _,op,_ in data[n]),'patch':[[*k,*base[k],*t[k]] for k in sorted(t) if t[k]!=base[k]],'row157_local_helper_rows_unchanged':True,'retagged_paths':sum(a[0]!=b[0] for a,b in zip(data['baseline'],data[n]))}
assert [len(res[n]['patch']) for n in res]==[9,3,12]
assert all(v['dag']==206 for v in res.values())
vendor=PKG/'vendor/K219_Construction_2026-10-20.zip'
arrival=subprocess.run(['git','show','26d5de6d21:docs/incoming/K219_Construction_2026-10-20.zip'],cwd=ROOT,stdout=subprocess.PIPE,check=True).stdout
assert vendor.read_bytes()==arrival
report={'status':'INDEPENDENT_STATIC_SOURCE_AND_LITERAL_COMPARISON_PASS','execution_scope':'Own literal and tree/CFG reader only; no delivered programs, symbolic runtime, startup simulation, checksum manifests, or proof compiler executed.','reader':desc(Path(__file__)),'variants':res,'vendor_matches_original_arrival':True,'source_transforms_commute':True,'all_eight_zero_entry_guards_rechecked_in_both_backgrounds':True,'retagged_complete_ordered_cfg_equal':True,'findings':[]}
(OUT/'static-comparison.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ('status','vendor_matches_original_arrival','source_transforms_commute')}))
print(json.dumps({n:{k:v[k] for k in ('dag','guard_cases','row157_local_helper_rows_unchanged','retagged_paths')} for n,v in res.items()}))
