from pathlib import Path
import hashlib,json,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs');S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';P=Path('/tmp/adaptive13-ranklower-postmerge-tjqelwlk');L=P/'lib/DiophantineConsistency';new={'ArithmeticOuterSeed','ArithmeticPellSquaredSeed','ArithmeticPellAuxiliarySeed','ArithmeticConstructionBoundPell'};seen=set();rows=[]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def visit(n):
 if n in seen:return
 seen.add(n);p=S/(n+'.lean');assert p.is_file(),p;imports=re.findall(r'^import\s+([\w.]+)',p.read_text(),re.M)
 for m in imports:
  if m.startswith('DiophantineConsistency.') and (S/(m.split('.',1)[1]+'.lean')).is_file():visit(m.split('.',1)[1])
 if n in new:return
 obj=L/(n+'.olean');assert obj.is_file(),n;resolved=obj.resolve();source_hash=sha(p);row={'module':n,'source_sha256':source_hash,'object_sha256':sha(obj),'resolved_object':str(resolved),'imports':imports};base=next((x.parent for x in resolved.parents if x.name=='lib'),None);record=None
 if base and (base/'state.json').is_file():
  state=json.loads((base/'state.json').read_text())
  for r in state.get('records',state.get('completed',[])):
   if r.get('name')==n or r.get('module')=='DiophantineConsistency.'+n:record=r;break
 if record and 'source_sha256' in record:
  assert record['source_sha256']==source_hash,(n,'source differs')
  if record.get('object_sha256'):assert record['object_sha256']==row['object_sha256'],(n,'object differs')
  row.update(provenance='provider state',record_source_sha256=record['source_sha256'])
 elif (Path('/tmp/object-current-deps-_hgxk1r0') in resolved.parents):
  state=json.loads(Path('/tmp/object-current-deps-_hgxk1r0/dependency-replay.json').read_text());record=next((r for r in state['modules'] if r.get('module')=='DiophantineConsistency.'+n),None);assert record and record['source_sha256']==source_hash,n;row.update(provenance='dependency replay metadata',record_source_sha256=record['source_sha256'])
 elif str(resolved).startswith('/home/codex/.codex/worktrees/62ff/Proofs/.lake/'):
  other=Path('/home/codex/.codex/worktrees/62ff/Proofs/Computability/DiophantineConsistency/Lean/DiophantineConsistency')/(n+'.lean');assert other.is_file() and sha(other)==source_hash,n;row.update(provenance='62ff cache boundary; source matches, no cache-to-source proof',record_source_sha256=sha(other))
 else:row['provenance']='unmatched boundary'
 rows.append(row)
for n in new:visit(n)
res={'scope':'DiophantineConsistency transitive source closure of four new Pell modules; package and cross-namespace internals are inherited boundaries','provider':str(P),'provider_state_sha256':sha(P/'state.json'),'targets':sorted(new),'rows':rows,'cross_namespace_imports':sorted({m for r in rows for m in r['imports'] if not m.startswith('DiophantineConsistency.')})};Path('/tmp/adaptive13-assembly-pell-audit.json').write_text(json.dumps(res,indent=2)+'\n');print('inherited',len(rows),'unmatched',[(r['module'],r['resolved_object']) for r in rows if r['provenance']=='unmatched boundary']);print('cache boundaries',[(r['module'],r['resolved_object']) for r in rows if r['provenance'].startswith('62ff')]);print('cross imports',res['cross_namespace_imports'])
