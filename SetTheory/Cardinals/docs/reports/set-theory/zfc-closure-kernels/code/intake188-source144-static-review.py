"""Own inert literal/source reader; no delivered module imported or machine executed."""
from pathlib import Path
import hashlib,json,zipfile,subprocess
P=Path('/tmp/zfc-intake188/drop-k218/extracted/K218_Construction_2026-10-20')
O=Path(__file__).parent
h=lambda b:hashlib.sha256(b).hexdigest()
def desc(p):return {'path':str(p),'sha256':h(p.read_bytes())}
def table(raw):
 d={}
 for line in raw.decode().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,m,z=line.split();k=(int(q),int(b));assert k not in d and m in ('L','R')
  d[k]=(int(w),m,int(z))
 Q={q for q,b in d};assert set(d)=={(q,b)for q in Q for b in (0,1)}
 assert all(w in (0,1) and z in Q|{254,218} for w,m,z in d.values())
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

vendor=P/'portable/vendor/K219_Construction_2026-10-20.zip'
arrival=subprocess.check_output(['git','show','26d5de6d21:docs/incoming/K219_Construction_2026-10-20.zip'])
assert vendor.read_bytes()==arrival
with zipfile.ZipFile(vendor) as z:
 base=json.loads(z.read('K219_Construction_2026-10-20/machine/sites219.json'))
 old=table(z.read('K219_Construction_2026-10-20/machine/k219.native.tm'))
stage=json.loads((P/'verification/construction/intermediate_sites205.json').read_text())
new=json.loads((P/'machine/sites218.json').read_text())
assert [x[1:] for x in base]==[x[1:] for x in stage]==[x[1:] for x in new]
assert cfg(base)==cfg(stage)==cfg(new)
assert [tree(x)[1]for x in (base,stage,new)]==[206,205,205]
t=tree(stage)[0];pattern=t
prefix='110100100110111111110'
for bit in prefix:pattern=pattern[int(bit)]
A,B=pattern[0];C=pattern[1]
assert rewrite(t,pattern,(A,(B,C)))==(tree(new)[0],5)
assert sum(a[0]!=b[0] for a,b in zip(stage,new))==260
unfolded=table((P/'verification/construction/unfolded219.tm').read_bytes())
final=table((P/'machine/k218.native.tm').read_bytes())
assert len(old)==len(unfolded)==438 and len(final)==436
assert {q for q,b in old}-{q for q,b in final}=={212}
assert not {q for q,b in final}-{q for q,b in old}
assert sum(v!=old[k] for k,v in final.items())==32
assert {k:v for k,v in unfolded.items()if v[2]==85}=={(155,0):(0,'R',85)}
assert {k:v for k,v in unfolded.items()if v[2]==212}=={(177,1):(1,'R',212)}
expected={(q,b):(w,m,85 if z==212 else z)for(q,b),(w,m,z)in unfolded.items()if q!=212}
expected[85,1]=(1,'L',190);assert expected==final
rows={(85,0):(0,'R',98),(85,1):(1,'L',190),(190,0):(0,'R',188),(190,1):(1,'R',189),(188,1):(1,'R',12),(189,1):(1,'L',156),(156,1):(1,'R',176),(176,1):(1,'R',150)}
assert {k:final[k]for k in rows}==rows
can=json.loads((P/'machine/canonicalization.json').read_text());ren={int(k):v for k,v in can['native_to_canonical'].items()};assert len(set(ren.values()))==len(ren)
assert ren[0]==0 and ren[84]==23 and ren[254]==218
assert {(ren[q],b):(w,m,ren[z])for(q,b),(w,m,z)in final.items()}==table((P/'machine/k218.tm').read_bytes())
result={'status':'OWN_LITERAL_SOURCE_PREMISES_PASS','reader':desc(Path(__file__)),'parent_archive_matches_arrival':True,'source_word_and_full_CFG_equal':True,'source_vertices':len(new),'nonhalt_CFG_edges':sum(map(len,cfg(new))),'guarded_cases':sum(2 if x[1]=='CD' else 1 for x in new),'DAG':[206,205,205],'exact_closed_reassociation_occurrences':5,'changed_addresses':260,'state_count':218,'rows':436,'retained_delta':32,'removed':[212],'marker_entries_and_all_local_helper_rows_exact':True,'canonicalization_exact':True,'scope':'Own JSON/tree/CFG and literal-row comparisons only. No delivered executable, source interpretation, binary simulation, symbolic runtime, startup, manifest validation or compiler invoked.'}
(O/'static-review.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
