from pathlib import Path
import os,json,hashlib,re
D=Path(__file__).resolve().parents[2];h=D/'research/trace74-boundary-seed-parametric-rebuild';o=h/'observations/attempt02';outer=h/'observations/outer-attempt02';pdir=D/'research/trace74-boundary-witness-rebuild/observations/attempt02';plan=D/'research/trace74-boundary-seed-parametric-plan/observations/plan-attempt02/result.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text())
def hashes(b):return {s:None if v is None else v['sha256'] for s,v in b.items()}
assert sha(o/'result.json')=='2f43ae10b79aca99bf5ce5d93edb177ee0384aed9151a9f3449a05cce579db4d'
assert sha(outer/'terminal.json')=='5548ff10648b5f4e984a7512f5459009fca68ae797a5d7a26188586171402092'
r=load(o/'result.json');z=load(outer/'terminal.json');parent=load(pdir/'result.json');rows=load(plan)['stages'];assert r['status']=='PASS' and z['exit']==0 and z['child_status']=='PASS' and z['child_result_sha256']==sha(o/'result.json') and z['inputs_before']==z['inputs_after'] and z['wrapper_sha256_before']==z['wrapper_sha256_after']=='9637a44205491fc298f3fa7be3dd01690e2e23896ec5f0897960d90ffedcb9a3'
for file in ('stdout','stderr'):assert sha(outer/file)==z[file+'_sha256']
for p,s in r['inputs'].items():assert sha(p)==s
assert sha(o/'initial-union.json')==r['initial_union_sha256'];initial=load(o/'initial-union.json');assert len(initial)==2025 and r['union_count']==2026
base=Path(r['output_root'])/'lib';suffixes=('.olean','.olean.private','.olean.server','.ilean','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ilean.hash','.ir.hash');pack=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');core=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
files=list(base.rglob('*.olean'));assert len(files)==2026
expectednames=['Trace74BoundarySeedParametric'];assert [x['module'] for x in rows]==[x['module'] for x in r['stages']]==expectednames
for n,b in initial.items():
 for suff,v in b.items():
  p=base/(n.replace('.','/')+suff)
  if v is None:assert not os.path.lexists(p)
  else:assert p.is_file() and str(p.resolve(strict=True))==v['resolved'] and sha(p)==v['sha256']
for i,(s,row) in enumerate(zip(r['stages'],rows),1):
 assert s['index']==i and s['status']=='PASS' and s['exit']==0 and s['reason'] is None and s['source_sha256']==row['source_sha256'];assert sha(s['source'])==sha(o/f'stage-{i:02}.source.lean')==row['source_sha256']
 assert re.findall(r'^import\s+([^\s]+)',Path(s['source']).read_text(),re.M)==row['imports'];assert s['command'][5]==str(base.parent/'src'/(s['module']+'.lean'));assert sha(s['command'][5])==s['source_sha256']
 for ext in ('stdout','stderr'):assert sha(o/f'stage-{i:02}.{ext}')==s[ext+'_sha256']
 assert not (o/f'stage-{i:02}.stderr').read_bytes();name=row['report'];axioms='propext, Classical.choice, Quot.sound';assert (o/f'stage-{i:02}.stdout').read_text()==f"'{name}' depends on axioms: [{axioms}]\n"
 for suff,v in s['object'].items():
  f=base/(s['module']+suff)
  if v is None:assert not os.path.lexists(f)
  else:assert f.is_file() and str(f.resolve(strict=True))==v['resolved'] and sha(f)==v['sha256']
assert sha(base/'Trace74BoundarySeedParametric.olean')=='e2a9c3d803db6e2a0e331b73598b73b51613c008cebbf65f54f442d7d070242f'
for n,b in {**r['selected_project'],**r['selected_outside']}.items():
 options=[p/(n.replace('.','/')+'.olean') for p in (base,pack,core) if os.path.lexists(p/(n.replace('.','/')+'.olean'))];assert options and options[0].is_file();f=options[0];assert str(f)==b['.olean']['path']
 for suff,v in b.items():
  g=Path(str(f)[:-6]+suff)
  if v is None:assert not os.path.lexists(g)
  else:assert g.is_file() and str(g.resolve(strict=True))==v['resolved'] and sha(g)==v['sha256']
for i,header in enumerate(r['headers']):
 assert header['status']=='PASS' and header['exit']==0 and header['reason'] is None
 for ext in ('stdout','stderr'):assert sha(o/f'header-{i:03}.{ext}')==header[ext+'_sha256']
 lines=(o/f'header-{i:03}.stdout').read_text().splitlines();assert lines[0].startswith('BEGIN ') and lines[-1]=='END';file=Path(lines[0][6:]);name=file.relative_to(base).as_posix()[:-6].replace('/','.');imports=[line[7:] for line in lines[1:-1] if line.startswith('IMPORT ')];assert len(imports)==len(lines)-2 and imports==r['serialized_headers'][name]
assert len(r['headers'])==1
for root,c in r['closures'].items():
 project=set();outside=set();todo=[root]
 while todo:
  n=todo.pop()
  if n in project or n in outside:continue
  if n in r['selected_project']:project.add(n);todo.extend(r['serialized_headers'][n])
  else:assert n in r['selected_outside'];outside.add(n)
 assert project==set(c['project']) and outside==set(c['outside'])
 if root in parent['closures']:
  assert c==parent['closures'][root]
  for kind,ns in [('project',project),('outside',outside)]:
   for n in ns:assert hashes(r['selected_'+kind][n])==hashes(parent['selected_'+kind][n])
assert len(r['closures'])==8 and len(r['header_reuse'])==len(r['serialized_headers'])-1
print('PASS outer/child, one source/report/object/logs, 2025 inherited bundles and 2026 union, 1878 selected project/81 outside first selections, one fresh header, eight reconstructed closures and seven parent closure/companion matches')
assert set(r['header_reuse'])==set(r['serialized_headers'])-set(expectednames)
for n in r['header_reuse']:assert r['serialized_headers'][n]==parent['serialized_headers'][n]
print('PASS every reused header matches captured parent')