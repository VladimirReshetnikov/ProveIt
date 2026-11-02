#!/usr/bin/env python3
"""Point-in-time seven-source same-side closure scan; no Lean build."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4];BASE=ROOT/'Computability/DiophantineConsistency';RESEARCH=BASE/'research/ordinary12-ipra-bridge';AUDIT=BASE/'reviews/compact44-graph-derived-radix-independent-audit';PARENT=Path('/tmp/ipra-compact-graph-derived-radix-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
ROWS=[
('Compact943Data','compact44-943-table-prototype/Compact943Data.lean','8c9e4816b7','10a75f23bf358ac745949b9d2717da33c8ccbc4e069892128b913d78d43617f8',['ArithmeticWindowDigits']),
('CompactCoefficientMass','compact44-coefficient-mass-prototype/CompactCoefficientMass.lean','49d10be3df','ca20b0796cbdd1b6c86e6032998fec7d5577b0f775b88d8395db349c7b1b2e6e',['Compact943Data']),
('CompactSymbolicKernel','compact44-symbolic-kernel-prototype/CompactSymbolicKernel.lean','5a0836d866','f34e96b3d4df160c980632a426aee1340e5c06c93500e899b255610c317da7ae',['CompactCoefficientMass']),
('CompactSymbolicKernelCast','compact44-symbolic-kernel-cast-prototype/CompactSymbolicKernelCast.lean','293e8620f5','9bc4e25ddf502a45e7b5cc080762b37e746b29f012ea1677f955121ef3561edc',['CompactSymbolicKernel','ArithmeticStandardCasts']),
('CompactSymbolicKernelGeneric','compact44-symbolic-kernel-cast-prototype/CompactSymbolicKernelGeneric.lean','293e8620f5','7ca0de8055204d2f9dc021a1ad6ec902c72c6f91ed53db19f6f54d9700549e28',['CompactSymbolicKernelCast']),
('CompactSymbolicKernelOpaque','compact44-symbolic-kernel-param-prototype/CompactSymbolicKernelOpaque.lean','2433689aa3','fbef8642de957bb39493607cb67edda418f53332af5a92ee594a2a437241e0b8',['CompactSymbolicKernelGeneric']),
('CompactDirectParamGraphDraft','compact44-direct-symbolic-k-prototype/CompactDirectParamGraphDraft.lean','8ca0d03752','fdab453be9f780c7b7b0ffff8088ff6c890c9e923c3dc952885d38dad778a691',['CompactSymbolicKernelOpaque','CompactGraphDerivedRadix'])]
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def slots(stem):
 r={}
 for suffix in SUFFIXES:
  p=Path(str(stem)+suffix)
  if os.path.lexists(p):
   if not p.is_file():raise ValueError(('invalid slot',str(p)))
   r[str(p)]={'sha256':H(p),'realpath':str(p.resolve())}
  else:r[str(p)]=None
 return r
assert H(AUDIT/'CHECK.json')=='2a71f758002a114db6e02b406755cb8ce5da4f4e6309ff3683aac4d681a15fdc' and H(AUDIT/'terminal-observation.json')=='111f0b17cc873126d6c55fa40387c763ccfe5a7f616e03bd87d13fe3359e4c5b'
a=json.loads((AUDIT/'CHECK.json').read_bytes());o=json.loads((AUDIT/'terminal-observation.json').read_bytes());assert a['status']=='PASS_INDEPENDENT_COMPACT44_GRAPH_DERIVED_RADIX_AUDIT' and type(o['observed_exit']) is int and o['observed_exit']==0 and o['lean_launched'] is False and o['check_sha256']==H(AUDIT/'CHECK.json')
sources=[]
for name,rel,commit,sha,imports in ROWS:
 p=RESEARCH/rel; assert H(p)==sha
 blob=subprocess.run(['git','show',commit+':'+p.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True).stdout;assert hashlib.sha256(blob).hexdigest()==sha
 found=[line[7:] for line in p.read_text().splitlines() if line.startswith('import ')];assert found==['DiophantineConsistency.'+x for x in imports]
 sources.append({'module':'DiophantineConsistency.'+name,'source':str(p),'source_commit':commit,'source_sha256':sha,'imports':found})
libs=[PARENT/side/'lib' for side in ('author','peer')];inv=[{p.relative_to(lib).as_posix():p for p in lib.rglob('*.olean') if p.is_file()} for lib in libs];assert set(inv[0])==set(inv[1]) and len(inv[0])==143
objects=[]
for path in sorted(inv[0]):
 a,b=inv[0][path],inv[1][path];assert H(a)==H(b);objects.append({'path':path,'sha256':H(a),'author_resolved':str(a.resolve()),'peer_resolved':str(b.resolve())})
external={};targets={}
for lib in libs:
 for module in ('ArithmeticWindowDigits','ArithmeticStandardCasts','CompactGraphDerivedRadix'):
  stem=lib/'DiophantineConsistency'/module;assert Path(str(stem)+'.olean').is_file();external.update(slots(stem))
 for name,*_ in ROWS:
  stem=lib/'DiophantineConsistency'/name;s=slots(stem);assert all(v is None for v in s.values());targets.update(s)
init=slots(PACKAGE/'Init');assert Path(str(PACKAGE/'Init')+'.olean').is_file()
print(json.dumps({'status':'PRELIMINARY_DIRECT_SYMBOLIC_K_CLOSURE_NOT_A_BUILD','source_order':sources,'parent_audit_sha256':H(AUDIT/'CHECK.json'),'objects':objects,'external_direct_slots':external,'target_slots':targets,'init_slots':init,'scope':'Point-in-time source and same-side provider plan only; no parent rerun or paired build, retained byte/display binding, graph semantics or iPRA proof.'},indent=2,sort_keys=True))
