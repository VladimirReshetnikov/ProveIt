#!/usr/bin/env python3
"""Gate on terminal PASS before independently checking a BFS coherent rebuild; no Lean replay."""
from pathlib import Path
from hashlib import sha256
from collections import deque
import argparse,json,re
D=Path(__file__).resolve().parents[2];H=D/'research/direct-bfs-80-coherent-rebuild';PL=D/'research/direct-bfs-80-coherent-rebuild-plan/observations/attempt01/result.json';F=D/'research/direct-bfs-80-ipra-serialized-audit/observations/attempt01/result.json';T=['standard_consistency','standard_translated_consistency','reference_consistency','reference_translated_consistency']
p=argparse.ArgumentParser();p.add_argument('--attempt',required=True);a=p.parse_args();assert re.fullmatch(r'attempt[0-9]{2,}',a.attempt)
O=H/'observations'/a.attempt;OUT=H/'observations'/('outer-'+a.attempt)
def sha(p):
 h=sha256()
 with Path(p).open('rb') as f:
  for chunk in iter(lambda:f.read(4*1024*1024),b''):h.update(chunk)
 return h.hexdigest()
def j(p):return json.loads(Path(p).read_text())
# The wrapper writes this only after the child terminates. Refuse to inspect a live attempt.
outer=j(OUT/'terminal.json');assert outer['exit']==0 and outer['inner_status']=='PASS' and outer['pins']==outer['after'];assert outer['pins']['runner']=='b19034d2e356e4656ba3f7efdec8c2a1b841152a834aea521f7f7d8b1f5663e7' and outer['pins']['outer']=='03524406be2ecc22769f92c60b816b5cbb84dce9f5a42a357329a36b3239bbbb'
assert sha(H/'run-v2.py')==outer['pins']['runner'] and sha(H/'run-v2-outer.py')==outer['pins']['outer'] and sha(OUT/'stdout')==outer['stdout_sha256'] and sha(OUT/'stderr')==outer['stderr_sha256'] and sha(O/'result.json')==outer['inner_sha256']
r=j(O/'result.json');plan=j(PL);fixed=j(F);A=fixed['closure']['project'];ext=fixed['closure']['outside'];init=j(O/'initial-project.json');outside=j(O/'outside-baseline.json');built=r['built'];union=Path(r['output_root'])/'lib';src=Path(r['output_root'])/'src'
assert r['status']=='PASS' and r['runner_sha256']==outer['pins']['runner'] and len(r['stages'])==len(built)==65 and len(init)==1866 and len(outside)==80
assert sha(O/'initial-project.json')==r['initial_project_sha256'] and sha(O/'outside-baseline.json')==r['outside_baseline_sha256']
B=j(D/'reviews/ten-positive-80-coherent-rebuilt-closure/observations/attempt01/result.json')['selected_project'];supp=plan['unaffected_missing_supplements'];assert set(init)==set(B)|set(supp) and len(B)==1765 and len(supp)==101
for n,rows in init.items():
 ref=B[n] if n in B else A[n]['companions']
 for suffix,rec in rows.items():
  e=ref[suffix];assert (rec is None)==(e is None)
  if rec is not None:assert rec['sha256']==e['sha256'] and rec['resolved']==(e['real_path'] if n in B else e['resolved'])
for n,rows in outside.items():
 for suffix,rec in rows.items():
  e=ext[n]['companions'][suffix];assert (rec is None)==(e is None)
  if rec is not None:assert rec['sha256']==e['sha256'] and rec['resolved']==e['resolved']
stagepos={x['module']:x['index'] for x in plan['rebuild_order']}
for p,h in r['inputs'].items():assert sha(p)==h,p
for row in r['stages']:
 i=row['index'];n=row['module'];expected=plan['rebuild_order'][i-1];stage=O/f'stage-{i:03}'
 assert n==expected['module'] and row['exit']==0 and row['reason'] is None and row['source_sha256']==expected['producer']['source_sha256']
 assert sha(stage/'source.lean')==sha(src/(n.replace('.','/')+'.lean'))==sha(expected['producer']['source_snapshot'])==row['source_sha256'] and sha(expected['producer']['receipt'])==expected['producer']['receipt_sha256']
 assert sha(stage/'stdout')==row['stdout_sha256'] and sha(stage/'stderr')==row['stderr_sha256']
 log=(stage/'stdout').read_text()+(stage/'stderr').read_text();assert not re.search(r'(?i)\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b',log)
 assert row['direct_before']==row['direct_after'] and set(row['direct_before'])==set(A[n]['imports'])
 assert all(stagepos.get(dep,0)<i for dep in row['direct_before'])
 assert row['preflight']['mem_available_kib']>=8*1024**2 and len(row['preflight']['lean'])<2
 assert all(x['mem_available_kib']>=8*1024**2 and len(x['lean'])<=2 for x in row['samples'])
 assert row['output']==built[n]
 for dep,actual in row['direct_before'].items():
  expected_dep=built.get(dep,init.get(dep,outside.get(dep)));assert expected_dep is not None
  for suffix,base in expected_dep.items():
   got=actual[suffix];assert (base is None)==(got is None),(n,dep,suffix)
   if got is not None:assert got['sha256']==base['sha256'] and got['resolved']==base['resolved'],(n,dep,suffix)
  if dep in built or dep in init:assert actual['.olean']['path']==str(union/(dep.replace('.','/')+'.olean'))
# Independently rehash every current initial, built, and directly selected outside companion.
for group,kind in ((init,'link'),(built,'regular'),(outside,'outside')):
 for n,rows in group.items():
  for suffix,rec in rows.items():
   path=Path(str(union/n.replace('.','/'))+suffix) if kind!='outside' else Path(ext[n]['path'][:-6]+suffix)
   assert path.exists() or not path.is_symlink(),(n,suffix)
   assert path.is_file()==(rec is not None),(n,suffix)
   if rec is not None:
    assert sha(path)==rec['sha256'] and str(path.resolve())==rec['resolved'],(n,suffix)
    if kind=='link':assert path.is_symlink()
    if kind=='regular':assert not path.is_symlink() and str(path.absolute())==str(path.resolve())
c=r['closure'];assert set(c['project'])==set(A) and set(c['outside'])==set(ext)
for n,row in c['project'].items():
 assert row['imports']==A[n]['imports'];expect=built.get(n,init.get(n));assert expect is not None
 for suffix,rec in row['companions'].items():
  e=expect[suffix];assert (rec is None)==(e is None)
  if rec is not None:assert rec['sha256']==e['sha256'] and rec['resolved']==e['resolved']
for n,row in c['outside'].items():
 for suffix,rec in row['companions'].items():
  e=outside[n][suffix];assert (rec is None)==(e is None)
  if rec is not None:assert rec['sha256']==e['sha256'] and rec['resolved']==e['resolved']
seen=set();leaves=set();todo=deque(c['roots'])
while todo:
 n=todo.popleft()
 if n in seen or n in leaves:continue
 if n not in c['project']:leaves.add(n);continue
 seen.add(n);todo.extend(c['project'][n]['imports'])
assert seen==set(A) and leaves==set(ext)
# Reparse exactly the author's captured header-reader outputs.
found={};paths={row['path']:n for n,row in c['project'].items()}
for i in range(c['header_batches']):
 label=f'post-headers-{i:03}';meta=j(O/(label+'.json'));so=O/(label+'.stdout');se=O/(label+'.stderr');assert meta['exit']==0 and meta['reason'] is None and sha(so)==meta['stdout_sha256'] and sha(se)==meta['stderr_sha256'] and not se.read_text()
 assert meta['preflight']['mem_available_kib']>=8*1024**2 and len(meta['preflight']['lean_pids'])<2
 assert all(x['mem_available_kib']>=8*1024**2 and len(x['lean_pids'])<=2 for x in meta['samples'])
 cmd=meta['command'];assert cmd[1:5]==['-M3000','-j1','-DElab.async=false','--run'] and Path(cmd[5]).name=='ReadObjectImports.lean' and 0<len(cmd[6:])<=32
 cur=None
 for line in so.read_text().splitlines():
  if line.startswith('BEGIN '):
   path=line[6:];assert cur is None and path in cmd[6:] and path in paths and paths[path] not in found;cur=paths[path];found[cur]=[]
  elif line.startswith('IMPORT ') and cur is not None:found[cur].append(line[7:])
  elif line=='END' and cur is not None:cur=None
  else:raise AssertionError((i,line))
 assert cur is None
assert found=={n:row['imports'] for n,row in c['project'].items()}
assert all(row['output']['.olean']['sha256']==A[row['module']]['record']['sha256'] for row in r['stages'])
assert built['DirectBFS80FixedIPRA']['.olean']['sha256']=='2155f5f05a8e993dc3582f3c14ce9c56916d0ac09dc326c02093d83a878e4703'
print('All 65 rebuilt objects are byte-identical to prior capture; direct-provider observations are separate evidence.')
text=(O/'stage-065'/'stdout').read_text()
for name in T:
 pattern=r"'DirectBFS80FixedIPRA\."+re.escape(name)+r"' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)";m=re.findall(pattern,text,re.S);assert len(m)==1 and set(v.strip() for v in m[0].split(',') if v.strip())<={'propext','Classical.choice','Quot.sound'}
print('PASS actual child exit 0; 65 stage source, direct inputs, diagnostics, products; 1866 initial and 80 outside baselines; 1795 selected project/80 leaves and',c['header_batches'],'retained header batches; four endpoint reports')
print('Outer wrapper process exit remains separately observable, not certified by its own receipt; no independent Lean replay, full historical/source/package/dynamic ancestry, or external file binding.')
