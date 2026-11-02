#!/usr/bin/env python3
"""Read-only same-side nine-module source and companion-slot inventory."""
import hashlib,json,os,subprocess,re
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('optimized Python rejected')
REPO=Path.cwd();ROOT=REPO/'Computability/DiophantineConsistency';BASE=ROOT/'research/ordinary12-ipra-bridge';REVIEWS=ROOT/'reviews';PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');PREFIX=Path('/tmp/ipra-same-witness-saturation-pair-01')
SELECTOR=BASE/'compact44-selector-graph-closure-plan/scan.json';KPLAN=BASE/'compact44-direct-symbolic-k-closure-plan/scan.json';AUDIT=REVIEWS/'compact44-same-witness-saturation-independent-audit/CHECK.json';OBS=AUDIT.parent/'terminal-observation.json'
PINS={SELECTOR:'514042651521a9200019e4fed4fa296ca7008c57eb8f3c3a16d8d92f97d1a035',KPLAN:'e09c94bcda39978c52f920c6aa682d95c9993d0bed10628a45d2e6988ced461c',AUDIT:'5d8c620fc76d741a7d1b398f9e442ce7dfea83a90cd39a42c53e9320d75dd754',OBS:'109b331fc4e435f4a59fa63fceb909c49057f82b8542131a9adec8eac8ff4915'}
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def h(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(ok,msg):
 if not ok:raise ValueError(msg)
def inventory(stem):
 out={}
 for suffix in SUFFIXES:
  p=Path(str(stem)+suffix)
  if os.path.lexists(p):need(p.is_file(),('nonregular',str(p)));out[str(p)]={'resolved':str(p.resolve()),'sha256':h(p)}
  else:out[str(p)]=None
 return out
for p,sha in PINS.items():need(p.is_file() and h(p)==sha,('fixed input drift',str(p)))
a=json.loads(AUDIT.read_bytes());o=json.loads(OBS.read_bytes());need(a['status']=='PASS_INDEPENDENT_SAME_WITNESS_PAIR_ARTIFACT_AUDIT' and type(a['recorded_outer_exit']) is int and a['recorded_outer_exit']==0 and type(o['observed_exit']) is int and o['observed_exit']==0 and o['lean_launched'] is False and o['check_sha256']==PINS[AUDIT],'bad parent audit schema')
rows=json.loads(SELECTOR.read_bytes())['source_order']+json.loads(KPLAN.read_bytes())['source_order'][:3]
for name,sha in [('CompactSupportSlot','9b8c126b63cab1e3d6e629cad5d3a0597bd00a51c708d41a54a5b1be3ad65596'),('CompactCopySupport','a2c3fc4a396229bef7e8b95b712c0cee7be79a1d4f91e2f6cb440a35db1df24e')]:
 source=BASE/'compact44-copy-support-prototype'/(name+'.lean');rows.append({'module':'DiophantineConsistency.'+name,'source':str(source),'source_sha256':sha,'source_commit':'89303c9fc5'})
need(len(rows)==9 and len({x['module'] for x in rows})==9,'module count')
available=set();sources=[];external=set()
for row in rows:
 p=Path(row['source']);need(p.is_file() and h(p)==row['source_sha256'],('source drift',str(p)));rel=p.relative_to(REPO)
 old=subprocess.run(['git','show',f'{row["source_commit"]}:{rel}'],capture_output=True,check=True,timeout=15).stdout;need(hashlib.sha256(old).hexdigest()==row['source_sha256'],('git source mismatch',str(p)))
 imports=[x[7:] for x in p.read_text().splitlines() if x.startswith('import ')];expected=row.get('imports',imports);need(imports==expected,('imports mismatch',str(p)))
 names=re.findall(r'^#print axioms\s+([^\s]+)',p.read_text(),re.M);need(len(names)>0 and len(names)==len(set(names)),('axiom names',str(p)))
 for dep in imports:
  if dep not in available:
   need(not any(x['module']==dep for x in rows),('out-of-order dependency',row['module'],dep));external.add(dep)
 sources.append({'module':row['module'],'source':str(p),'source_commit':row['source_commit'],'source_sha256':h(p),'imports':imports,'axiom_reports':names});available.add(row['module'])
need(external=={'DiophantineConsistency.ArithmeticWindowDigits','DiophantineConsistency.CompactMixedIncrement','DiophantineConsistency.CompactSameWitnessSaturation2'},('unexpected externals',external))
objects={};targets={};direct={};prior=None
for side in ('author','peer'):
 lib=PREFIX/side/'lib';files={p.relative_to(lib):p for p in lib.rglob('*.olean')};need(len(files)==146,('object count',side,len(files)));canonical=[]
 for rel,p in sorted(files.items()):canonical.append({'path':str(rel),'sha256':h(p),'resolved':str(p.resolve())})
 compare=[(r['path'],r['sha256']) for r in canonical]
 if prior is None:prior=compare
 else:need(compare==prior,'author peer mismatch')
 objects[side]=canonical
 for row in sources:
  name=row['module'];stem=lib/Path(*name.split('.'));inv=inventory(stem);need(not any(inv.values()),('target collision',side,name));targets.update(inv)
 for name in sorted(external):
  stem=lib/Path(*name.split('.'));inv=inventory(stem);need(inv[str(stem)+'.olean'] is not None,('missing direct object',side,name));direct.update(inv)
init=inventory(PACKAGE/'Init');need(init[str(PACKAGE/'Init.olean')] is not None,'missing Init')
need(len(targets)==180 and len(direct)==60 and len(init)==10,'slot inventory count')
print(json.dumps({'status':'PRELIMINARY_COPY_SUPPORT_CLOSURE_NOT_A_BUILD','parent_audit_sha256':h(AUDIT),'source_order':sources,'objects':objects,'external_direct_slots':direct,'target_slots':targets,'init_slots':init,'scope':'Point-in-time same-side source and object inventory; positive graph coordinates, literal graph zero, position and residue assumptions remain explicit; not retained K binding, paired build, machine or iPRA proof.'},indent=2,sort_keys=True))
