from pathlib import Path
import json,hashlib,subprocess,sys,os
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
root=Path(__file__).resolve().parents[4];b=root/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';plan=b/'compact44-fixed-graph-closure-plan';r=json.loads((plan/'scan.json').read_text())
for name in ('README.md','scan.py','scan.json'):
 p=plan/name;rel=p.relative_to(root).as_posix();historic=subprocess.run(['git','show','de388d977d:'+rel],cwd=root,capture_output=True,check=True).stdout
 assert historic==p.read_bytes(),('source plan drift',name)
p=plan/'scan.py';q=subprocess.run([sys.executable,'-I','-S','-B',str(p)],capture_output=True,timeout=120,check=True);assert not q.stderr and json.loads(q.stdout)==r,'source scan rerun drift'
audit=root/'Computability/DiophantineConsistency/reviews/compact44-symbolic-graph-join-independent-audit/CHECK.json';assert hashlib.sha256(audit.read_bytes()).hexdigest()=='3164ef421742c093b07fb1ff491c19d9586f2ff19f83d2371f3311b4958721ec';assert json.loads(audit.read_text())['status']=='PASS_INDEPENDENT_SYMBOLIC_GRAPH_JOIN_PAIR_AUDIT'
libs=[Path('/tmp/ipra-compact-symbolic-graph-join-pair-01')/s/'lib' for s in ('author','peer')]
hashf=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
actual=[]
for lib in libs:
 items={p.relative_to(lib).as_posix():hashf(p) for p in lib.rglob('*.olean') if p.is_file()}
 actual.append(items)
assert actual[0]==actual[1] and len(actual[0])==134
assert {x['module_path']:x['sha256'] for x in r['inherited_objects']}==actual[0]
for item in r['inherited_objects']:
 rel=Path(item['module_path'])
 assert str((libs[0]/rel).resolve())==item['author_resolved_path']
 assert str((libs[1]/rel).resolve())==item['peer_resolved_path']
modules=r['modules']; names=[x['module'] for x in modules]; assert len(names)==6 and len(set(names))==6
seen=set();srcs={}
for x in modules:
 path=Path(x['source']);assert path.is_file();data=path.read_bytes();assert hashf(path)==x['source_sha256']
 imports=[j for l in data.decode().splitlines() if l.startswith('import ') for j in l[7:].split()];assert imports==x['imports'];assert all(j not in names or j in seen for j in imports)
 for dep in imports:
  if dep not in seen:assert dep.replace('.','/')+'.olean' in actual[0],(x['module'],dep)
 for lib in libs:assert not (lib/(x['module'].replace('.','/')+'.olean')).exists(),x['module']
 seen.add(x['module']);srcs[x['module']]=str(path)
assert names[-1]=='DiophantineConsistency.CompactGenericGraphDigits'
for k,v in r['explicit_choices'].items():
 selected=Path(v['selected']); assert hashf(selected)==v['selected_sha256']; assert any(Path(z['path'])==selected and z['sha256']==v['selected_sha256'] for z in v['all_candidates'])
 for z in v['all_candidates']:assert hashf(Path(z['path']))==z['sha256']
assert len(r['explicit_choices']['CompactFixedBeta']['all_candidates'])==2
assert len(r['explicit_choices']['CompactSymbolicPorts']['all_candidates'])==2
p=Path(srcs[names[-1]]);s=p.read_text();
for token in ['theorem fixed_graph_digits (K : ℕ)', '(hv : ∀ j,0<v j)', '(hN : 0<N)', '(hq :', '(hJ :', '(hz : InternalZero', 'dig 67 C 0=1', 'dig 67 C k≤3']:
 assert token in s,token
print(json.dumps({'status':'PASS_INDEPENDENT_POINT_IN_TIME_FIXED_GRAPH_CLOSURE','parent_object_count_each':len(actual[0]),'ordered_sources':names,'fixed_beta_candidates':2,'symbolic_ports_candidates':2,'checks':['independent project import topology','source sha and selected candidates','same-side inherited object paths/content','selected output absence','fixed theorem textual hypotheses'], 'scope':'Read-only point-in-time source and olean comparison; no Lean build, parent audit rerun, simultaneous source/object freeze, package/dynamic ancestry, retained tuple equality, graph construction or PRA theorem.'},indent=2))
