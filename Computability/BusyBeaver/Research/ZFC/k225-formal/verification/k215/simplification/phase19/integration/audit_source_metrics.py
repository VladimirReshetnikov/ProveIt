# Owned inert byte/line audit; never imports or runs the producer or Lean.
from pathlib import Path
import hashlib,json
O=Path(__file__).resolve().parent
A=Path('/tmp/k215-phase19-transfer-aliases'); I=Path('/tmp/k215-next-single-use')
sha=lambda b:hashlib.sha256(b).hexdigest()
a=json.loads((A/'candidate-map.json').read_text());i=json.loads((I/'candidate-map.json').read_text())
rows=[]
for r in a['files']:
 rows.append((r,Path(r['before']),Path(r['candidate'])))
for r in i['sources']:
 rows.append((r,I/'before'/r['path'],I/'candidate'/r['path']))
assert len(rows)==len({r['path'] for r,_,_ in rows})==8
result=[]
for r,b,c in rows:
 old=b.read_bytes();new=c.read_bytes();assert sha(old)==r['before_sha256'] and sha(new)==r['after_sha256']
 result.append({'path':r['path'],'before_source':str(b),'candidate_source':str(c),'before_sha256':sha(old),'after_sha256':sha(new),'before_bytes':len(old),'after_bytes':len(new),'before_lines':len(old.splitlines()),'after_lines':len(new.splitlines()),'bytes_removed':len(old)-len(new),'lines_removed':len(old.splitlines())-len(new.splitlines())})
lean=[r for r in result if r['path'].endswith('.lean')];producer=[r for r in result if r['path'].endswith('.py')]
assert len(lean)==7 and len(producer)==1
m={'status':'PASS_SOURCE_ONLY_EXACT_BYTES_AND_LINES_NOT_ELABORATION','source_maps':{str(A/'candidate-map.json'):sha((A/'candidate-map.json').read_bytes()),str(I/'candidate-map.json'):sha((I/'candidate-map.json').read_bytes())},'files':result,'lean_lines_removed':sum(r['lines_removed'] for r in lean),'lean_bytes_removed':sum(r['bytes_removed'] for r in lean),'producer_lines_removed':sum(r['lines_removed'] for r in producer),'producer_bytes_removed':sum(r['bytes_removed'] for r in producer),'maintenance_lines_removed':sum(r['lines_removed'] for r in result),'maintenance_bytes_removed':sum(r['bytes_removed'] for r in result),'canonical_writes':False,'compiler_or_supplied_producer_execution':False}
assert (m['lean_lines_removed'],m['lean_bytes_removed'],m['maintenance_lines_removed'],m['maintenance_bytes_removed'])==(169,6449,167,6241)
# Derive the exact selected 215 endpoint scope independently from frozen old rows.
selection=Path('/tmp/k215-phase19-check-draft/expanded-old-baseline-rows.json')
graph=json.loads(selection.read_text());by_module={r['module']:r for r in graph['modules']}
visited=set()
def visit(n):
 if n=='Init' or n in visited:return
 assert n in by_module,n
 visited.add(n)
 for dep in by_module[n]['imports']:visit(dep)
visit('BusyBeaver.ZFC.KEndpoint215')
changed={r['path']:r for r in result};size_before=0;size_after=0;endpoint_changes=[]
R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
for n in sorted(visited):
 r=by_module[n];rel=str(Path(r['source']).relative_to(R))
 if rel in changed:
  c=changed[rel];old=Path(c['before_source']).read_bytes();new=Path(c['candidate_source']).read_bytes();endpoint_changes.append({'module':n,'bytes_removed':len(old)-len(new)})
 else:old=new=Path(r['source']).read_bytes()
 assert sha(old)==r['source_sha256'],n
 size_before+=len(old);size_after+=len(new)
assert (len(visited),size_before,size_after,size_before-size_after)==(178,1767300,1765109,2191)
m['endpoint_source_scope']={'status':'STATIC_SOURCE_IMPORT_CLOSURE_NOT_COMPILER_EVIDENCE','selection_sha256':sha(selection.read_bytes()),'target':'BusyBeaver.ZFC.KEndpoint215','module_count_before':len(visited),'module_count_after':len(visited),'source_bytes_before':size_before,'source_bytes_after':size_after,'source_bytes_removed':size_before-size_after,'edited_endpoint_sources':endpoint_changes,'note':'The other five changed Lean files are compatibility targets outside this 215 endpoint closure.'}
(O/'source-metrics.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:v for k,v in m.items() if k not in ['source_maps','files']},indent=2))
