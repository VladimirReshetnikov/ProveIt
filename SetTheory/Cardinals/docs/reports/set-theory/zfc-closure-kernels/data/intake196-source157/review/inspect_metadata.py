#!/usr/bin/env python3
"""Own file/data inventory. Does not import or execute packet code."""
from pathlib import Path
import hashlib,json,collections,difflib,ast
P=Path('/tmp/zfc-intake196/scanner/extracted/ZFC_217_Scanner_Source_Research_2026-10-21')
Q=Path('/tmp/zfc-intake195/extracted/K216_Partial_Selector_2026-10-20')
O=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def write(n,x):(O/n).write_text(json.dumps(x,indent=2)+'\n')
files=[dict(path=p.relative_to(P).as_posix(),bytes=p.stat().st_size,sha256=sha(p))for p in sorted(P.rglob('*'))if p.is_file()]
write('inventory.json',dict(package=str(P),file_count=len(files),bytes=sum(f['bytes']for f in files),files=files,scope='Own inventory only; no delivered manifest validation or supplied execution.'))
def table(p):
 t={}
 for line in p.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split(); k=int(q),int(b)
  assert k not in t
  t[k]=int(w),d,int(z)
 return t
selected=[(34,0),(34,1),(50,0),(50,1),(75,0),(77,0),(77,1),(196,0),(196,1),(122,1),(1,1)]
a=table(P/'inputs/primary218.native.tm');b=table(P/'inputs/dominated218.native.tm');c=table(Q/'machine/prefold217.native.tm')
rows=[dict(row=list(k),primary=list(a[k]),dominated=list(b[k]),new216_prefold=list(c[k]),equal=a[k]==b[k]==c[k])for k in selected]
assert all(x['equal']for x in rows)
# The final216 fold changes only164/0 and the redirect of183; preserve
# the final construction instructions as DATA rather than run the emitter.
r=json.loads((Q/'source/table_recipe.json').read_text())
assert not set(selected)&{tuple(x[:2])for x in r['replacement_rows']}
local_dependency={'164/0':[0,'L',201],'201/1':list(c[201,1]),'196/0':list(c[196,0]),'77/1':list(c[77,1])}
def met(p):
 rows=json.loads(p.read_text()); nodes={}; paths={x[0]for x in rows}
 for path,op,arg in rows:nodes[path]=(op,arg)
 for x in sorted({p[:i]for p in paths for i in range(len(p))},key=len,reverse=True):nodes[x]=(nodes[x+'0'],nodes[x+'1'])
 return dict(path=str(p),sha256=sha(p),leaves=len(rows),dag=len(set(nodes.values())),depth=max(map(len,paths)),zero_run=max(len(z)for p in paths for z in p.split('1'))),rows
sources=[];words=[]
for p in [P/'inputs/primary-sites.json',P/'inputs/dominated-sites.json',Q/'source/sites216.json',P/'experiments/equality-hit11-sites.json']:
 m,rr=met(p);sources.append(m);words.append([r[1:]for r in rr])
write('comparison216.json',dict(status='STATIC_SOURCE_AND_ROW_COMPARISON',rows=rows,new216_final_row_dependency=local_dependency,sources=sources,primary_vs_dominated_word=words[0]==words[1],dominated_vs_new216_word=words[1]==words[2],dominated_vs_eq11_word=words[1]==words[3],conclusion='All scanner local rows survive into new216 before its final164/183 fold. The new marker-one selector route also reaches77 via196/0. Replacing77/1 therefore requires its equality/decoder roles to be re-proved, even though the final selector patches are disjoint. No runtime, source reallocation or composed-machine claim.'))
# Author inert source-only successor for the selected source check, removing
# exactly the delivery manifest loop. Keep all mathematical assertions.
p=P/'source-layout/verify_sources.py';old=p.read_text();before="    manifest=json.loads((HERE/'manifest.json').read_text())\n    for rel,sha in manifest.items():\n        need(digest((HERE/rel).read_bytes())==sha,('Input changed',rel))\n"
assert old.count(before)==1
new=old.replace(before,'    # Delivery-manifest replay omitted by intake policy; selected inputs are pinned in the replay plan.\n')
ast.parse(new)
(O/'verify_sources_intake.py').write_text(new)
(O/'source-check-adapter.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='delivered/source-layout/verify_sources.py',tofile='copy/source-layout/verify_sources.py')))
write('adapter.json',dict(original=dict(path=str(p),sha256=sha(p)),successor=dict(path=str(O/'verify_sources_intake.py'),sha256=sha(O/'verify_sources_intake.py')),exact_removed_text=before,all_other_bytes_preserved=True,parsed_only=True,executed=False))
print(json.dumps({'files':len(files),'bytes':sum(f['bytes']for f in files),'all_scanner_rows_equal':all(x['equal']for x in rows),'source_metrics':sources},indent=2))
