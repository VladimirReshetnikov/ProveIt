from pathlib import Path
import os,json,hashlib,re
D=Path(__file__).resolve().parents[2];h=D/'research/trace74-boundary-compatible-rebuild';o=h/'observations/attempt03';outer=h/'observations/outer-attempt03';pdir=D/'research/trace75-bfs-ipra-final-assembly-plan/observations/attempt01';plan=D/'research/trace74-boundary-compatible-plan/observations/plan-attempt03/result.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text())
def hashes(b):return {s:None if v is None else v['sha256'] for s,v in b.items()}
assert sha(o/'result.json')=='aa17ffeb0a2446d44392d986af54a9cd687dd544c67dc145a87c77f600e7a2d3'
assert sha(outer/'terminal.json')=='2493accc873ec46391494ef5125de3b61d460b4bef61fb56f54f966ccbc036d0'
r=load(o/'result.json');z=load(outer/'terminal.json');parent=load(pdir/'result.json');rows=load(plan)['stages'];assert r['status']=='PASS' and z['exit']==0 and z['child_status']=='PASS' and z['child_result_sha256']==sha(o/'result.json') and z['inputs_before']==z['inputs_after'] and z['wrapper_sha256_before']==z['wrapper_sha256_after']=='93c94980548d287f107d7269af6b0df4d31b933ccca5ec5aed376fd2a3179c19'
for file in ('stdout','stderr'):assert sha(outer/file)==z[file+'_sha256']
for p,s in r['inputs'].items():assert sha(p)==s
assert sha(o/'initial-union.json')==r['initial_union_sha256'];initial=load(o/'initial-union.json');assert len(initial)==2016 and r['union_count']==2021
base=Path(r['output_root'])/'lib';suffixes=('.olean','.olean.private','.olean.server','.ilean','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ilean.hash','.ir.hash');pack=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');core=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
files=list(base.rglob('*.olean'));assert len(files)==2021
expectednames=['Trace74Mask','Trace74BoundaryParent','Trace74BoundaryParts','Trace74BoundaryNatural','Trace74BoundaryGraph'];assert [x['module'] for x in rows]==[x['module'] for x in r['stages']]==expectednames
for n,b in initial.items():
 for suff,v in b.items():
  p=base/(n.replace('.','/')+suff)
  if v is None:assert not os.path.lexists(p)
  else:assert p.is_file() and str(p.resolve(strict=True))==v['resolved'] and sha(p)==v['sha256']
for i,(s,row) in enumerate(zip(r['stages'],rows),1):
 assert s['index']==i and s['status']=='PASS' and s['exit']==0 and s['reason'] is None and s['source_sha256']==row['source_sha256'];assert sha(s['source'])==sha(o/f'stage-{i:02}.source.lean')==row['source_sha256']
 assert re.findall(r'^import\s+([^\s]+)',Path(s['source']).read_text(),re.M)==row['imports'];assert s['command'][5]==str(base.parent/'src'/(s['module']+'.lean'));assert sha(s['command'][5])==s['source_sha256']
 for ext in ('stdout','stderr'):assert sha(o/f'stage-{i:02}.{ext}')==s[ext+'_sha256']
 assert not (o/f'stage-{i:02}.stderr').read_bytes();name=('Trace74Mask.coordinate_identity' if i==1 else row['report']);axioms=('propext, Quot.sound' if i==1 else 'propext, Classical.choice, Quot.sound');assert (o/f'stage-{i:02}.stdout').read_text()==f"'{name}' depends on axioms: [{axioms}]\n"
 for suff,v in s['object'].items():
  f=base/(s['module']+suff)
  if v is None:assert not os.path.lexists(f)
  else:assert f.is_file() and str(f.resolve(strict=True))==v['resolved'] and sha(f)==v['sha256']
assert sha(base/'Trace74BoundaryGraph.olean')=='176c7f05e52bfe9ac46195b42abd680725df397cd8fdd02d70fcac02178533e5'
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
assert len(r['headers'])==5
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
assert len(r['closures'])==6 and len(r['header_reuse'])==len(r['serialized_headers'])-5
print('PASS outer/child, five source/report/object/logs, 2016 inherited bundles and 2021 union, 1873 selected project/81 outside first selections, five fresh headers, six reconstructed closures and five parent closure/companion matches')
assert set(r['header_reuse'])==set(r['serialized_headers'])-set(expectednames)
for n in r['header_reuse']:assert r['serialized_headers'][n]==parent['serialized_headers'][n]
print('PASS every reused header matches captured parent')
