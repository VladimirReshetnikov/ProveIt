#!/usr/bin/env python3
"""Point-in-time same-side closure for the conditional same-witness symbolic congruence."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4];BASE=ROOT/'Computability/DiophantineConsistency';SOURCE=BASE/'research/ordinary12-ipra-bridge/free-j-symbolic-congruence-prototype/FreeJGraphCongruenceExplore.lean';AUDIT=BASE/'reviews/compact44-graph-derived-radix-independent-audit';PARENT=Path('/tmp/ipra-compact-graph-derived-radix-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert H(SOURCE)=='d748f8bbad7a45a328322eec1acd4643bc3e2c3f40d015b6b653f790fd8978d0'
blob=subprocess.run(['git','show','f3afbc380f:'+SOURCE.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True).stdout;assert hashlib.sha256(blob).hexdigest()==H(SOURCE)
assert H(AUDIT/'CHECK.json')=='2a71f758002a114db6e02b406755cb8ce5da4f4e6309ff3683aac4d681a15fdc';audit=json.loads((AUDIT/'CHECK.json').read_bytes());obs=json.loads((AUDIT/'terminal-observation.json').read_bytes());assert audit['status']=='PASS_INDEPENDENT_COMPACT44_GRAPH_DERIVED_RADIX_AUDIT' and obs['observed_exit']==0 and obs['check_sha256']==H(AUDIT/'CHECK.json') and obs['lean_launched'] is False
imports=[v for l in SOURCE.read_text().splitlines() if l.startswith('import ') for v in l[7:].split()];assert imports==['DiophantineConsistency.CompactGraphDerivedRadix','DiophantineConsistency.ArithmeticModularCancellation']
libs=[PARENT/x/'lib' for x in ('author','peer')];objs=[]
for lib in libs:objs.append({p.relative_to(lib).as_posix():p for p in lib.rglob('*.olean') if p.is_file()})
assert set(objs[0])==set(objs[1]) and len(objs[0])==143
inventory=[]
for rel in sorted(objs[0]):
 a,b=objs[0][rel],objs[1][rel];assert H(a)==H(b);inventory.append({'path':rel,'sha256':H(a),'author_resolved':str(a.resolve()),'peer_resolved':str(b.resolve())})
slots={}
for side,lib in zip(('author','peer'),libs):
 for name in imports:
  stem=lib/Path(*name.split('.'));obj=Path(str(stem)+'.olean');assert obj.is_file()
  for suffix in SUFFIXES:
   p=Path(str(stem)+suffix)
   if os.path.lexists(p):assert p.is_file();slots[str(p)]={'sha256':H(p),'realpath':str(p.resolve())}
   else:slots[str(p)]=None
 target=lib/'DiophantineConsistency/FreeJGraphCongruenceExplore';assert all(not os.path.lexists(Path(str(target)+s)) for s in SUFFIXES)
init=PACKAGE/'Init.olean';assert init.is_file()
print(json.dumps({'status':'PRELIMINARY_SYMBOLIC_CONGRUENCE_SOURCE_CLOSURE_NOT_A_BUILD','source_sha256':H(SOURCE),'imports':imports,'parent_audit_sha256':H(AUDIT/'CHECK.json'),'objects':inventory,'direct_project_companion_slots':slots,'package_init':{'path':str(init),'sha256':H(init),'resolved_path':str(init.resolve())},'scope':'Point-in-time extended same-witness source and corresponding graph-derived-radix provider inventory; no parent rerun, frozen pair, full transitive/package/dynamic ancestry, retained K binding, decoder, machine or iPRA proof.'},indent=2,sort_keys=True))
