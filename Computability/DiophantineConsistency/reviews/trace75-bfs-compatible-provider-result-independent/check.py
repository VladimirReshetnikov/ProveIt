from pathlib import Path
import hashlib,json,os,re
root=Path(__file__).resolve().parents[2];H=root/'research/trace75-bfs-compatible-provider-rebuild';a=H/'observations/attempt01';o=H/'observations/outer-attempt01';r=json.loads((a/'result.json').read_text());outer=json.loads((o/'terminal.json').read_text());plan=json.loads((root/'research/trace75-bfs-compatible-provider-plan/observations/plan-attempt01/result.json').read_text());bfs=json.loads((root/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/result.json').read_text());initial=json.loads((root/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/initial-project.json').read_text());scan=json.loads((root/'research/trace75-bfs-provider-preflight/observations/scan-attempt01/result.json').read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'result.json')=='04cd437011c9a8b753a310da6c7691f229f9758b9050fdba9b61b812697fbc3c' and sha(o/'terminal.json')=='8714c2ca237d88faa4bc373ed827ede93ee9cb2b4af9d77f0217d5363e3bd964'
assert r['status']=='PASS' and outer['exit']==0 and outer['child_status']=='PASS' and outer['child_result_sha256']==sha(a/'result.json') and outer['inputs_before']==outer['inputs_after'] and outer['wrapper_sha256_before']==outer['wrapper_sha256_after']==sha(H/'run-outer.py')
for n in ('stdout','stderr'):assert sha(o/n)==outer[n+'_sha256']
for p,d in {**r['inputs'],**outer['inputs_before']}.items():assert sha(p)==d,p
assert sha(H/'run.py')==r['runner_sha256'] and sha(a/'initial-union.json')==r['initial_union_sha256']
base=json.loads((a/'initial-union.json').read_text());assert len(base)==1946 and r['stage_order']==plan['stage_order'] and len(r['stages'])==31
oldbase=initial|bfs['built'];assert len(oldbase)==1931
def hashes(bundle):return {s:(None if v is None else v['sha256']) for s,v in bundle.items()}
for n,b in oldbase.items():assert n in base and hashes(base[n])==hashes(b),n
for i,s in enumerate(r['stages'],1):
 n=s['module'];p=plan['producers'][n];assert s['index']==i and n==r['stage_order'][i-1] and s['status']=='PASS' and s['exit']==0 and s['reason'] is None and n not in base
 assert sha(s['source'])==sha(a/f'stage-{i:02}.source.lean')==s['source_sha256']==p['source_sha256'];assert sha(a/f'stage-{i:02}.stdout')==s['stdout_sha256']==p['stdout_sha256'] and sha(a/f'stage-{i:02}.stderr')==s['stderr_sha256']==p['stderr_sha256']
 assert s['object']['.olean'] and sha(s['object']['.olean']['path'])==s['object']['.olean']['sha256'];base[n]=s['object']
 for snap in [s['preflight'],s['postflight'],*s['samples']]:assert snap['mem_available_kib']>=8*1024**2 and len(snap['lean'])<=2
assert len(base)==r['union_count']==1977
lib=Path(r['output_root'])/'lib'; actual={str(x.relative_to(lib)) for x in lib.rglob('*') if x.is_file() or x.is_symlink()};want={n.replace('.','/')+suffix for n,b in base.items() for suffix,v in b.items() if v is not None};assert actual==want
for n,bundle in base.items():
 for suffix,v in bundle.items():
  p=lib/(n.replace('.','/')+suffix)
  if v is None:assert not os.path.lexists(p)
  else:assert p.is_file() and str(p.resolve(strict=True))==v['resolved'] and sha(p)==v['sha256']
heads=r['serialized_headers'];assert set(heads)==set(r['selected_project']) and len(heads)==901 and len(r['selected_outside'])==44
def closure(n):
 pending=[n];ins=set();out=set()
 while pending:
  x=pending.pop()
  if x in ins or x in out:continue
  if x not in heads:out.add(x);continue
  ins.add(x);pending.extend(heads[x])
 return {'project':sorted(ins),'outside':sorted(out)}
prior=bfs['closure']['project']
def bfs_closure(n):
 pending=[n];ins=set();out=set()
 while pending:
  x=pending.pop()
  if x in ins or x in out:continue
  if x not in prior:out.add(x);continue
  ins.add(x);pending.extend(prior[x]['imports'])
 return {'project':sorted(ins),'outside':sorted(out)}
for n in r['closures']:
 assert closure(n)==r['closures'][n]
 if n in ('DirectBFSBandCarry','DirectBFSHaltPellSeed'):
  assert bfs_closure(n)==r['closures'][n]
  for dep in r['closures'][n]['project']:assert dep in prior and hashes(r['selected_project'][dep])==hashes(prior[dep]['companions']),dep
for n in r['header_reuse']:
 h=r['selected_project'][n]['.olean']['sha256']
 if n in scan['selected_project'] and scan['selected_project'][n]['.olean']['sha256']==h:assert heads[n]==scan['headers'][n]
 else:assert n in prior and prior[n]['record']['sha256']==h and heads[n]==prior[n]['imports']
for i,row in enumerate(r['headers']):
 assert row['status']=='PASS' and row['exit']==0 and row['reason'] is None
 out=a/f'header-{i:03}.stdout';err=a/f'header-{i:03}.stderr';assert sha(out)==row['stdout_sha256'] and sha(err)==row['stderr_sha256'] and not err.read_bytes()
 current=None;parsed={}
 for line in out.read_text().splitlines():
  if line.startswith('BEGIN '):current=Path(line[6:]).relative_to(lib).as_posix()[:-6].replace('/','.');assert current not in parsed;parsed[current]=[]
  elif line.startswith('IMPORT ') and current is not None:parsed[current].append(line[7:])
  elif line=='END' and current is not None:current=None
  else:raise AssertionError(line)
 assert current is None
 for n,imports in parsed.items():assert heads[n]==imports
for n,b in r['selected_outside'].items():
 candidates=[p/(n.replace('.','/')+'.olean') for p in (lib,Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')) if os.path.lexists(p/(n.replace('.','/')+'.olean'))];assert candidates and candidates[0].is_file() and str(candidates[0])==b['.olean']['path']
 for suffix,v in b.items():
  if v is not None:assert Path(v['path']).is_file() and str(Path(v['path']).resolve(strict=True))==v['resolved'] and sha(v['path'])==v['sha256']
print('PASS outer, 31 stage sources/logs/objects, 1977 union bundles, 901 project headers and 44 outside bundles, two BFS root closure/companions')
print('roots', {n:(len(v['project']),len(v['outside'])) for n,v in r['closures'].items()})
