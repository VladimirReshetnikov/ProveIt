from pathlib import Path
import hashlib,json,subprocess,re,functools,datetime
root=Path('/home/codex/.codex/worktrees/9c9b/Proofs')
p=Path('/tmp/gowers-merge68ad-native-tools')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
assert sha(p/'freeze.json')=='8cdac1bc02ac895dd19aa01d82738c8c6f75bcb8f5ef1119effd5bc8d3daa3b3'
freeze=read(p/'freeze.json')
for name,h in freeze.items():assert sha(p/name)==h,name
for n in ('common.py','capture.py','run.py'):
 assert (p/n).read_bytes()==(Path('/tmp/gowers-next829-native-tools')/n).read_bytes()
old=read('/tmp/gowers-next829-native-tools/plan.json');plan=read(p/'plan.json')
assert list(plan)==['core','shared','supplemental']
for k in plan:
 assert plan[k]['roots']==old[k]['roots']
 for field in plan[k]:
  if field!='source_lines':assert plan[k][field]==old[k][field]
rows=read(p/'source-rows.json');graph=read(p/'fullgraph-imports.json')
assert len(rows)==len(graph)==6021 and set(rows)==set(graph)
paths={row['path'] for row in rows.values()}
tracked=set(subprocess.check_output(['git','ls-files','Combinatorics/Ramsey/Lean','lib/openai-math/lean']).decode().splitlines())
tracked={x for x in tracked if x.endswith('.lean')}
assert paths==tracked,(len(paths),len(tracked),sorted(paths^tracked)[:10])
for m,row in rows.items():
 file=root/row['path']; assert sha(file)==row['sha256'],m
 s=file.read_text(); assert len(s.splitlines())==row['source_lines'],m
 assert re.findall(r'^import\s+(\S+)',s,re.M)==graph[m],m
assert graph==read(p/'baseline-fullgraph-imports.json')
@functools.lru_cache(None)
def closure(m):return frozenset({m}).union(*(closure(d) for d in graph[m] if d in graph))
mode_modules={};cumulative=set()
for label,spec in plan.items():
 mods=set().union(*(closure(r) for r in spec['roots']));cumulative.update(mods)
 assert len(mods)==spec['module_count']
 assert len(mods)+3==spec['input_count']
 assert sum(rows[m]['source_lines'] for m in mods)==spec['source_lines']
 expected={'roots':spec['roots'],'modules':sorted(mods),'module_count':len(mods),'input_count':len(mods)+3,'source_lines':spec['source_lines'],'cumulative_modules':sorted(cumulative)}
 assert read(p/'mode-closures.json')[label]==expected
 mode_modules[label]=mods
owners=read(p/'changed-owners.json');owner_set={r['module'] for r in owners}
diff=subprocess.check_output(['git','diff','--name-only','685a309568b28cc4914662c144f38bcda92ce4a1','HEAD']).decode().splitlines()
changed=set(diff)&paths
assert changed=={r['path'] for r in owners} and len(changed)==153
assert owner_set<=cumulative
consumer_set={m for m in graph if closure(m)&owner_set}
covered=consumer_set&cumulative
excluded={'GowersSzemeredi','GowersSzemeredi.Audit','GowersSzemeredi.PortImportAudit'}
assert len(consumer_set)==1671 and len(covered)==1668 and consumer_set-cumulative==excluded
cov=[{'module':m,'changed_owner':m in owner_set,'affected_before':True,'affected_current':True,'selected_modes':[mode for mode in plan if m in mode_modules[mode]],'excluded_facade':m in excluded} for m in sorted(consumer_set)]
assert cov==read(p/'consumer-coverage.json')
assert len(cumulative)==1964
assert subprocess.check_output(['git','rev-parse','HEAD']).decode().strip()=='a87906dc3960604bc3a0b423868d392b43ba85c0'
assert subprocess.check_output(['git','status','--porcelain'])==b''
report={'status':'PASS: independent source-only native-plan review; checker not invoked','source_commit':'a87906dc3960604bc3a0b423868d392b43ba85c0','reviewed_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'freeze_sha256':sha(p/'freeze.json'),'measurement_sha256':sha(p/'measurement.json'),'plan_sha256':sha(p/'plan.json'),'verified_assets':len(freeze),'source_pins_and_import_rows':len(rows),'changed_owners':len(owners),'dependent_consumers':len(consumer_set),'covered_consumers':len(covered),'excluded_facades':sorted(excluded),'union_modules':len(cumulative),'helper_bytes_identical_to_previous_reviewed_pack':True,'native_started':False}
out=Path('/tmp/gowers-merge68ad-native-tools-root-review.json')
assert not out.exists()
out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2));print('report_sha256',sha(out))
