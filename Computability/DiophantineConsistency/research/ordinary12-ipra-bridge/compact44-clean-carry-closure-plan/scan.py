#!/usr/bin/env python3
"""Point-in-time same-side source/object scan for the clean carry-reset client."""
import hashlib,json,os
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('optimized Python rejected')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2];BASE=ROOT/'research/ordinary12-ipra-bridge'
PREFIX=Path('/tmp/ipra-compact-heterogeneous-carry-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
AUDIT=ROOT/'reviews/compact44-heterogeneous-carry-independent-audit/CHECK.json'
SOURCE=BASE/'compact44-clean-carry-reset-prototype/CompactCarryReset.lean'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
if H(AUDIT)!='415d5b4056e35eda01b7896c330d9298af4a410fffca31edad12fe902afd11f9':raise ValueError('parent audit drift')
check=json.loads(AUDIT.read_text())
if check.get('status')!='PASS_INDEPENDENT_COMPACT44_HETEROGENEOUS_CARRY_AUDIT' or type(check.get('recorded_outer_exit')) is not int or check['recorded_outer_exit']!=0:raise ValueError('invalid parent audit')
if H(SOURCE)!='f80d473cb579a24086ae29e560cce33a8ed282bf90ce7458302ec8a3d244928d':raise ValueError('client source drift')
imports=[v for line in SOURCE.read_text().splitlines() if line.startswith('import ') for v in line[7:].split()]
if imports!=['DiophantineConsistency.CompactHeterogeneousCarry']:raise ValueError(('unexpected client imports',imports))
init=PACKAGE/'Init.olean'
if not init.is_file():raise ValueError('missing package Init object')
a=PREFIX/'author/lib';b=PREFIX/'peer/lib';aa={p.relative_to(a):p for p in a.rglob('*.olean')};bb={p.relative_to(b):p for p in b.rglob('*.olean')}
if aa.keys()!=bb.keys() or len(aa)!=115:raise ValueError('provider object sets differ')
objects=[]
for rel in sorted(aa):
 h=H(aa[rel])
 if H(bb[rel])!=h:raise ValueError(('provider object drift',str(rel)))
 objects.append({'module_path':str(rel),'sha256':h,'author_resolved_path':str(aa[rel].resolve()),'peer_resolved_path':str(bb[rel].resolve())})
seed_rel=Path('DiophantineConsistency/CompactHeterogeneousCarry.olean');seeds=[]
for side,lib in (('author',a),('peer',b)):
 if os.path.lexists(lib/seed_rel):raise ValueError(('seed collision',side))
 seed=PREFIX/side/'CompactHeterogeneousCarry.olean';row=next((r for r in check['runs'] if r['side']==side),None)
 if row is None or not seed.is_file() or H(seed)!=row['object_sha256']:raise ValueError(('seed mismatch',side))
 seeds.append({'side':side,'source':str(seed),'resolved_path':str(seed.resolve()),'sha256':H(seed),'target_relative_path':str(seed_rel)})
result={'status':'PRELIMINARY_SOURCE_CLOSURE_SCAN_NOT_A_BUILD','parent_audit_path':str(AUDIT),'parent_audit_sha256':H(AUDIT),'inherited_objects':objects,'seeds':seeds,'package_init':{'path':str(init),'resolved_path':str(init.resolve()),'sha256':H(init)},'client':{'module':'DiophantineConsistency.CompactCarryReset','source':str(SOURCE),'source_sha256':H(SOURCE),'imports':imports},'scope':'Point-in-time same-side object and client import inventory; no simultaneous freeze, Lean build, all-model clean-column transport, graph instance, checker, machine or PRA proof.'}
print(json.dumps(result,indent=2,sort_keys=True))
