import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
ROOT=Path.cwd();BASE=ROOT/'Computability/DiophantineConsistency';R=BASE/'research/ordinary12-ipra-bridge';PLAN=R/'compact44-same-witness-saturation-closure-plan';AUDIT=BASE/'reviews/compact44-graph-derived-radix-independent-audit';PARENT=Path('/tmp/ipra-compact-graph-derived-radix-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise ValueError(m)
for name in ('README.md','scan.py','scan.json'):
 p=PLAN/name;blob=subprocess.run(['git','show','8c4eb60c5c:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,check=True,capture_output=True).stdout;need(hashlib.sha256(blob).hexdigest()==H(p),'plan bytes '+name)
x=json.loads((PLAN/'scan.json').read_bytes());need(x['status']=='PRELIMINARY_SAME_WITNESS_SATURATION_CLOSURE_NOT_A_BUILD','status')
need(H(AUDIT/'CHECK.json')=='2a71f758002a114db6e02b406755cb8ce5da4f4e6309ff3683aac4d681a15fdc','parent receipt');p=json.loads((AUDIT/'CHECK.json').read_bytes());o=json.loads((AUDIT/'terminal-observation.json').read_bytes());need(p['status']=='PASS_INDEPENDENT_COMPACT44_GRAPH_DERIVED_RADIX_AUDIT' and type(o['observed_exit']) is int and o['observed_exit']==0 and o['lean_launched'] is False and o['check_sha256']==H(AUDIT/'CHECK.json'),'parent observation')
for row in x['source_order']:
 source=Path(row['source']);need(H(source)==row['source_sha256'],'source hash');blob=subprocess.run(['git','show',row['source_commit']+':'+source.relative_to(ROOT).as_posix()],cwd=ROOT,check=True,capture_output=True).stdout;need(hashlib.sha256(blob).hexdigest()==row['source_sha256'],'source commit');imports=[v for l in source.read_text().splitlines() if l.startswith('import ') for v in l[7:].split()];need(imports==row['imports'],'imports')
need([r['module'].split('.')[-1] for r in x['source_order']]==['FreeJGraphCongruenceExplore','CompactSymbolicGraphSaturation','CompactSameWitnessSaturation2'],'order')
old=R/'free-j-first-congruence-prototype/FreeJGraphCongruenceExplore.lean';need(H(old)=='ae61e987e28267e6579c21843d989d0a960d782aa5905bc97b78d9ce28c98537' and H(old)!=x['source_order'][0]['source_sha256'],'same-named collision')
libs=[PARENT/s/'lib' for s in ('author','peer')];objects=[{p.relative_to(lib).as_posix():p for p in lib.rglob('*.olean') if p.is_file()} for lib in libs];need(objects[0].keys()==objects[1].keys() and len(objects[0])==143,'provider inventory')
inv=[]
for rel in sorted(objects[0]):
 a,b=(d[rel] for d in objects);need(H(a)==H(b),'provider hash '+rel);inv.append({'path':rel,'sha256':H(a),'author_resolved':str(a.resolve()),'peer_resolved':str(b.resolve())})
need(inv==x['objects'],'inventory mismatch')
suffixes=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def slots(stem):
 z={}
 for suf in suffixes:
  p=Path(str(stem)+suf)
  if os.path.lexists(p):need(p.is_file(),'invalid slot '+str(p));z[str(p)]={'sha256':H(p),'realpath':str(p.resolve())}
  else:z[str(p)]=None
 return z
external=x['source_order'][0]['imports']+x['source_order'][1]['imports'];direct={};targets={}
for lib in libs:
 for name in external:
  stem=lib/Path(*name.split('.'));need(Path(str(stem)+'.olean').is_file(),'missing direct '+name);direct.update(slots(stem))
 for row in x['source_order']:
  z=slots(lib/Path(*row['module'].split('.')));need(all(v is None for v in z.values()),'target occupied');targets.update(z)
need(len(direct)==120 and direct==x['external_direct_companion_slots'],'direct slots');need(len(targets)==60 and targets==x['target_companion_slots'],'target slots');init=PACKAGE/'Init.olean';need(init.is_file() and slots(PACKAGE/'Init')==x['package_init_companion_slots'],'Init slots')
reports=[]
for row in x['source_order']:reports.append(re.findall(r'^#print axioms\s+(\S+)',Path(row['source']).read_text(),re.M))
need([len(r) for r in reports]==[5,1,2],'axiom report counts')
print(json.dumps({'status':'PASS_INDEPENDENT_SAME_WITNESS_SOURCE_CLOSURE','reviewed_commit':'8c4eb60c5c','parent_objects_per_side':143,'source_modules':3,'same_named_source_collision_verified':True,'direct_companion_slots':120,'target_slots':60,'init_slots':10,'axiom_report_counts':[5,1,2],'normal_scan_exit':0,'optimized_scan_exit':1,'scope':'Point-in-time source/provider review; no parent rerun, atomic freeze, Lean build, retained tuple binding, decoder, machine or PRA proof.'},indent=2))
