#!/usr/bin/env python3
"""Bounded point-in-time Foundation object search; read only, no Lean."""
import collections,hashlib,json
from pathlib import Path
R=Path(__file__).resolve().parents[2]; D=Path(__file__).resolve().parent
pin=json.loads((D/'pins.json').read_text())
p=R/'research/adaptive87-peer-nonproject-frontier/receipt.json'
assert hashlib.sha256(p.read_bytes()).hexdigest()==pin['frontier_receipt_sha256']
prior=json.loads(p.read_text());assert not prior['summary']['multiple_recorded_hashes']; want={e['input']:e['recorded_sha256'] for e in prior['edges'] if not e['recorded_path_matches']}
assert len(want)==26 and all(n.startswith('Foundation.') for n in want)
roots=set();errors=[];logical=0
for p in Path('/tmp').iterdir():
 try:
  if not p.is_dir():continue
  for rel in ('lib','package-lib','.lake/build/lib/lean','lib/lean','.'):
   x=p/rel/'Foundation'
   if x.is_dir():logical+=1;roots.add(str(x.resolve()))
 except OSError:errors.append(str(p))
for x in ['/home/codex/src/Proofs/.lake/build/lib/lean/Foundation','/home/codex/.codex/worktrees/46be/Proofs/.lake/build/lib/lean/Foundation']:roots.add(x)
cache={};same=collections.defaultdict(set);other=collections.defaultdict(set);broken=0;present=0
for root in sorted(roots):
 for n,h in want.items():
  p=Path(root)/(n[len('Foundation.'):].replace('.','/')+'.olean')
  try:
   if not p.is_file():
    if p.is_symlink():broken+=1
    continue
   present+=1; target=str(p.resolve());digest=cache.get(target)
   if digest is None:digest=hashlib.sha256(Path(target).read_bytes()).hexdigest();cache[target]=digest
   (same if digest==h else other)[n].add(target)
  except OSError:errors.append(str(p))
rows={}
for n,h in sorted(want.items()):
 paths=sorted(other[n]); samples=paths[:2]
 rows[n]={'expected_sha256':h,'exact_matches':sorted(same[n]),'different_physical_count':len(paths),'different_samples':[{'path':p,'sha256':cache[p]} for p in samples]}
print(json.dumps({'logical_tmp_roots':logical,'distinct_roots_including_explicit':len(roots),'readable_candidate_paths':present,'distinct_resolved_objects':len(cache),'broken_candidate_symlinks':broken,'inaccessible_paths':sorted(errors),'names_with_exact_match':sum(bool(v) for v in same.values()),'names_with_different_candidate':sum(bool(v) for v in other.values()),'names_with_no_readable_candidate':sum(not same[n] and not other[n] for n in want),'rows':rows,'limits':'Only immediate /tmp children with the five stated layouts and two explicit paths; no historical inventory exhaustiveness, symlink target compatibility, package ancestry or Lean claim.'},indent=2,sort_keys=True))
