#!/usr/bin/env python3
"""Check inert combined source snapshots and lexical imports; do not run Lean."""
from pathlib import Path
import hashlib,json,re,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('Run with python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
def pinned(path,digest):
 data=path.read_bytes();assert sha(data)==digest,(str(path),sha(data));return data
oldp=D/'research/ordinary14-natural81-combined-slim-overlay/inventory.json'
newp=D/'research/ordinary14-natural80-endpoint-import-inventory/inventory.json'
old=json.loads(pinned(oldp,'dea1250279ce9004e6784b6179f55f775d3751829a869d94f47216347a396ba9'))
new=json.loads(pinned(newp,'47677589f08a55c6d8a46c5801476c4ffc5ffd64299ef7d1b19017eb86b09301'))
a={r['module']:r for r in old['order']};b={r['module']:r for r in new['drafts_topological']}
assert len(a)==173 and len(b)==184 and set(a)<=set(b)
extra=set(b)-set(a)
assert extra=={'GammaPremises','GammaZeroNarrow','Natural80Endpoint','Natural80GammaClient','Natural80GammaShift','Natural80GuardGap','Natural80JPos','Natural80MainPairs','Natural80OwnZeroNorm','Natural80Partial74','P80NaturalForcedGamma'}
assert extra==set(new['natural81_comparison']['added_modules'])
assert all(p.is_file() and not p.is_symlink() and p.name.endswith('.lean.src') for p in (P/'source').iterdir())
files={p.name[:-9]:p for p in (P/'source').glob('*.lean.src')}
assert set(files)==set(b)
patchdir=D/'research/ordinary14-natural-partial-keyword-patch'
patches={
 'PartialShift82To74':('33b1d66bc3ab8010d83b91bff8604b015a3df000630a8d09fabbd77aa3e30a7e','47cb83c7a8cf4053e19eb7afbb391e00528b8b0ce5fdf4a2edda9c909163170e',8),
 'GraphPredecessors82':('7972ddb132643d0fd46bfd66e200bdf80a48e5d0df1b75f719b9c4ef5db5de54','44c47be7c5725bd5bbe11ed810780938c3b885eb394ae69d5bfc9797d8ce9c5e',7)}
assert set(patches)<=set(a)
pat=re.compile(r"(?<![A-Za-z0-9_'])partial(?![A-Za-z0-9_'])")
def rename(data,count):
 output=[];total=0
 for line in data.decode().splitlines(keepends=True):
  if line.lstrip().startswith('/--'):output.append(line);continue
  line,n=pat.subn('partialValuation',line);total+=n;output.append(line)
 assert total==count
 return ''.join(output).encode()
def imports(data):
 out=[]
 for line in data.decode().splitlines():
  if not line.strip():continue
  m=re.fullmatch(r'import\s+([A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*)\s*',line)
  if not m:break
  out.extend(m.group(1).split())
 return out
rows={};direct=set();modified=[]
for n,row in b.items():
 original=pinned(D/row['path'],row['sha256']);actual=files[n].read_bytes()
 if n in a:
  prev=a[n];assert prev['original_sha256']==row['sha256'],n
  prior=pinned(D/'research/ordinary14-natural81-combined-slim-overlay'/prev['overlay_path'],prev['overlay_sha256'])
  if n in patches:
   oh,ph,count=patches[n];assert row['sha256']==oh and prior==original,n
   expected=pinned(patchdir/(n+'.lean.src'),ph)
   assert rename(original,count)==expected,n
   kind='keyword-alternative';modified.append({'module':n,'replacements':count,'previous_sha256':sha(prior),'overlay_sha256':sha(expected)})
  else:expected=prior;kind='natural81-overlay-snapshot'
  prevbare,prevqual=prev['bare_imports'],prev['qualified_imports']
 else:
  expected=original;kind='natural80-endpoint-addition';prevbare,prevqual=row['bare_imports'],row['qualified_imports']
 assert actual==expected,n
 imps=imports(actual);bare=[i for i in imps if '.' not in i];qual=[i for i in imps if '.' in i]
 assert bare==prevbare and qual==prevqual,n
 direct.update(qual)
 rows[n]={'module':n,'kind':kind,'original_path':row['path'],'original_sha256':row['sha256'],'overlay_path':'source/'+n+'.lean.src','overlay_sha256':sha(actual),'bare_imports':bare,'qualified_imports':qual}
assert {x['module']:x['replacements'] for x in modified}=={'PartialShift82To74':8,'GraphPredecessors82':7}
order=[];seen=set();active=set()
def visit(n):
 assert n in rows,('unresolved bare import',n)
 if n in seen:return
 assert n not in active,('cycle',n)
 active.add(n)
 for x in rows[n]['bare_imports']:visit(x)
 active.remove(n);seen.add(n);order.append(n)
visit('Natural80Endpoint');assert seen==set(rows),sorted(set(rows)-seen)
q=[]
for n in sorted(direct):
 path=D/'Lean'/('/'.join(n.split('.'))+'.lean');assert path.is_file(),n
 q.append({'module':n,'path':str(path.relative_to(D)),'sha256':sha(path.read_bytes())})
origq={r['module']:r for r in new['qualified_direct_sources']};newq={r['module']:r for r in q}
assert set(origq)-set(newq)=={'DiophantineConsistency.Compact44.C44Short15Facts'}
assert set(newq)<=set(origq) and all(origq[n]==newq[n] for n in newq)
priorq={r['module'] for r in old['qualified_direct_sources']}
out={'scope':'inert draft snapshots and simple initial-header graph only; no Lean/provider/axiom/physical binding claim',
 'natural81_combined_inventory_sha256':sha(oldp.read_bytes()),'natural80_inventory_sha256':sha(newp.read_bytes()),
 'root':'Natural80Endpoint','draft_count':len(order),'shared_natural81_drafts':len(a),'added_natural80_modules':sorted(extra),
 'keyword_alternatives':sorted(modified,key=lambda x:x['module']),'drafts_topological':[rows[n] for n in order],
 'qualified_direct_count':len(q),'qualified_direct_sources':q,'additional_direct_qualified_vs_natural81':sorted(direct-priorq),
 'omitted_direct_qualified_vs_natural81':sorted(priorq-direct)}
print(json.dumps(out,sort_keys=True,indent=2))
