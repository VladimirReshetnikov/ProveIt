#!/usr/bin/env python3
"""Independent no-Lean check of first-root congruence source closure."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';P=BASE/'research/ordinary12-ipra-bridge/free-j-first-congruence-closure-plan';SOURCE=BASE/'research/ordinary12-ipra-bridge/free-j-first-congruence-prototype/FreeJGraphCongruenceExplore.lean';AUDIT=BASE/'reviews/compact44-graph-derived-radix-independent-audit';PARENT=Path('/tmp/ipra-compact-graph-derived-radix-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(c,m):
 if not c:raise ValueError(m)
for name in ('README.md','scan.py','scan.json','terminal-observation.json'):
 p=P/name;blob=subprocess.run(['git','show','7b0366359b:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,check=True,capture_output=True).stdout;need(hashlib.sha256(blob).hexdigest()==H(p),'plan bytes '+name)
need(H(SOURCE)=='ae61e987e28267e6579c21843d989d0a960d782aa5905bc97b78d9ce28c98537','source hash')
blob=subprocess.run(['git','show','df486043d0:'+SOURCE.relative_to(ROOT).as_posix()],cwd=ROOT,check=True,capture_output=True).stdout;need(hashlib.sha256(blob).hexdigest()==H(SOURCE),'source commit')
need(H(AUDIT/'CHECK.json')=='2a71f758002a114db6e02b406755cb8ce5da4f4e6309ff3683aac4d681a15fdc','parent receipt')
parent=json.loads((AUDIT/'CHECK.json').read_bytes());obs=json.loads((AUDIT/'terminal-observation.json').read_bytes());need(parent.get('status')=='PASS_INDEPENDENT_COMPACT44_GRAPH_DERIVED_RADIX_AUDIT' and type(obs.get('observed_exit')) is int and obs['observed_exit']==0 and obs.get('check_sha256')==H(AUDIT/'CHECK.json') and obs.get('lean_launched') is False,'parent observation')
q=subprocess.run([sys.executable,'-I','-S','-B',str(P/'scan.py')],cwd=ROOT,capture_output=True,timeout=120);need(q.returncode==0 and not q.stderr and q.stdout==(P/'scan.json').read_bytes(),'normal scan')
o=subprocess.run([sys.executable,'-O','-I','-S','-B',str(P/'scan.py')],cwd=ROOT,capture_output=True,timeout=120);need(o.returncode==1 and b'requires nonoptimized python3 -I -S' in o.stderr,'optimized scan')
scan=json.loads(q.stdout);need(scan.get('status')=='PRELIMINARY_CONGRUENCE_SOURCE_CLOSURE_NOT_A_BUILD','scan status')
imports=[x for line in SOURCE.read_text().splitlines() if line.startswith('import ') for x in line[7:].split()];need(imports==scan['imports']==['DiophantineConsistency.CompactGraphDerivedRadix','DiophantineConsistency.ArithmeticModularCancellation'],'source imports')
reports=re.findall(r'^#print axioms\s+(\S+)',SOURCE.read_text(),re.M);need(reports==['FreeJGraphCongruenceExplore.first_pair_mod','FreeJGraphCongruenceExplore.graph_congruence','FreeJGraphCongruenceExplore.graph_aligned_congruence'],'report names')
objs=[]
for side in ('author','peer'):
 lib=PARENT/side/'lib';m={p.relative_to(lib).as_posix():p for p in lib.rglob('*.olean') if p.is_file()};need(len(m)==143,'provider count '+side);objs.append(m)
need(objs[0].keys()==objs[1].keys(),'provider paths');inventory=[]
for rel in sorted(objs[0]):
 a,b=(m[rel] for m in objs);need(H(a)==H(b),'provider hash '+rel);inventory.append({'path':rel,'sha256':H(a),'author_resolved':str(a.resolve()),'peer_resolved':str(b.resolve())})
need(inventory==scan['objects'],'provider inventory differs')
slots={}
for side in ('author','peer'):
 lib=PARENT/side/'lib'
 for name in imports:
  stem=lib/Path(*name.split('.'));need(Path(str(stem)+'.olean').is_file(),'missing direct object '+name)
  for suffix in SUFFIXES:
   p=Path(str(stem)+suffix)
   if os.path.lexists(p):need(p.is_file(),'invalid companion '+str(p));slots[str(p)]={'sha256':H(p),'realpath':str(p.resolve())}
   else:slots[str(p)]=None
 target=lib/'DiophantineConsistency/FreeJGraphCongruenceExplore';need(all(not os.path.lexists(Path(str(target)+suffix)) for suffix in SUFFIXES),'occupied output slot '+side)
need(slots==scan['direct_project_companion_slots'] and len(slots)==40,'direct companion inventory')
init=PACKAGE/'Init.olean';need(init.is_file() and scan['package_init']=={'path':str(init),'sha256':H(init),'resolved_path':str(init.resolve())},'Init object')
print(json.dumps({'status':'PASS_INDEPENDENT_FIRST_CONGRUENCE_SOURCE_CLOSURE','reviewed_commit':'7b0366359b','normal_scan_exit':q.returncode,'optimized_scan_exit':o.returncode,'parent_objects_per_side':143,'direct_companion_slots_checked':len(slots),'source_sha256':H(SOURCE),'scope':'Point-in-time source, import and provider inventory only; no parent audit rerun, atomic freeze, paired Lean build, retained K/tuple binding, decoder, machine or PRA proof.'},indent=2))
