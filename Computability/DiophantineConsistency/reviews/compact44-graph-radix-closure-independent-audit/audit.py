#!/usr/bin/env python3
"""Independent point-in-time source/project-object closure verification."""
from pathlib import Path
import json,hashlib,subprocess,sys,os
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
root=Path(__file__).resolve().parents[4];base=root/'Computability/DiophantineConsistency';b=base/'research/ordinary12-ipra-bridge';plan=b/'compact44-graph-derived-radix-closure-plan';r=json.loads((plan/'scan.json').read_text());H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for name in ('README.md','scan.py','scan.json'):
 p=plan/name;rel=p.relative_to(root).as_posix();historic=subprocess.run(['git','show','374ea9696b:'+rel],cwd=root,capture_output=True,check=True).stdout
 assert historic==p.read_bytes(),('plan drift',name)
q=subprocess.run([sys.executable,'-I','-S','-B',str(plan/'scan.py')],capture_output=True,timeout=120,check=True);assert not q.stderr and json.loads(q.stdout)==r
parent=base/'reviews/compact44-fixed-graph-independent-audit/CHECK.json';assert H(parent)=='3d380723c818d4f16dc78e5c942b5e3cab8f7a01cf8a5bfad47ad3af3941abc1';assert json.loads(parent.read_bytes())['status']=='PASS_INDEPENDENT_COMPACT44_FIXED_GRAPH_DIGITS_AUDIT'
libs=[Path('/tmp/ipra-compact-fixed-graph-digits-pair-01')/s/'lib' for s in ('author','peer')];actual=[]
for lib in libs:
 items={p.relative_to(lib).as_posix():H(p) for p in lib.rglob('*.olean') if p.is_file()};actual.append(items)
assert actual[0]==actual[1] and len(actual[0])==140
assert {x['module_path']:x['sha256'] for x in r['inherited_objects']}==actual[0]
for x in r['inherited_objects']:
 rel=Path(x['module_path']);assert str((libs[0]/rel).resolve())==x['author_resolved_path'];assert str((libs[1]/rel).resolve())==x['peer_resolved_path']
modules=r['modules'];names=[x['module'] for x in modules];assert names==['DiophantineConsistency.FreeJPowerCancel','DiophantineConsistency.FreeJRadixAlignment','DiophantineConsistency.CompactGraphDerivedRadix'];seen=set();srcs={}
for x in modules:
 p=Path(x['source']);assert p.is_file() and H(p)==x['source_sha256'];imports=[v for l in p.read_text().splitlines() if l.startswith('import ') for v in l[7:].split()];assert imports==x['imports']
 for dep in imports:
  assert dep not in names or dep in seen
  if dep not in seen:assert dep.replace('.','/')+'.olean' in actual[0],(x['module'],dep)
 for lib in libs:
  output=lib/(x['module'].replace('.','/')+'.olean');assert not output.exists() and not output.is_symlink()
 seen.add(x['module']);srcs[x['module'].split('.')[-1]]=p
for name,choice in r['explicit_choices'].items():
 assert len(choice['all_candidates'])==1 and Path(choice['selected'])==Path(choice['all_candidates'][0]['path']) and H(choice['selected'])==choice['selected_sha256']==choice['all_candidates'][0]['sha256']
for name,prior in r['prior_audits'].items():
 p=base/'reviews'/prior['directory']/'CHECK.json';assert H(p)==prior['sha256'];data=json.loads(p.read_bytes());assert data['recorded_outer_exit']==0
 rel=srcs[name].relative_to(root).as_posix();blob=subprocess.run(['git','show',data['source_commit']+':'+rel],cwd=root,capture_output=True,check=True).stdout;assert hashlib.sha256(blob).hexdigest()==H(srcs[name])
s=srcs['CompactGraphDerivedRadix'].read_text()
for token in ('theorem fixed_graph_digits (K : ℕ)', '(hv : ∀ j,0<v j)', '(hz : InternalZero', '∃ N : V, 0<N', 'v 0=rep', 'dig 67 C 0=1', 'dig 67 C k≤3'):assert token in s,token
print(json.dumps({'status':'PASS_INDEPENDENT_GRAPH_RADIX_SOURCE_CLOSURE','reviewed_commit':'374ea9696b','parent_objects_per_side':140,'ordered_sources':names,'historical_source_bindings':2,'scope':'Point-in-time source/import and object inventory only; no audit rerun, atomic freeze, Lean build, full package/dynamic ancestry, retained tuple binding, machine/checker or PRA proof.'},indent=2))
