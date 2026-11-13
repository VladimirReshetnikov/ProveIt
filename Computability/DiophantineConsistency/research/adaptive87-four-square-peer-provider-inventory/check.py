#!/usr/bin/env python3
"""Read-only inventory of peer overlay for one pinned lexical endpoint closure."""
from pathlib import Path
import collections,hashlib,json
HERE=Path(__file__).resolve().parent;TASK=HERE.parents[1]
RECEIPT=TASK/'research/adaptive87-four-square-local-mod4-model-draft/result.json'
ROOT=Path('/tmp/nine-ipra-guarded-peer-20261102-a/lib')
HA=Path('/tmp/ha87-full-transitive-p3xt6wra/lib')
HASRC=Path('/tmp/ha87-frozen-full-e_jgyudl/tree/Computability/DiophantineConsistency/Lean')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
 return h.hexdigest()
assert sha(RECEIPT)=='84afb37c10d87b71240e0631b2288d1ee06efd46611efc79de8c17477c7fca08'
inputs=json.loads(RECEIPT.read_text())['instantiated_endpoint_sources'];rows={};kinds=collections.Counter();src_counts=collections.Counter();ha_counts=collections.Counter();providers=collections.Counter()
for name,row in sorted(inputs.items()):
 if not name.startswith('DiophantineConsistency.'):continue
 source=TASK/row['source'];assert sha(source)==row['sha256'],name
 rel=Path(*name.split('.'));p=(ROOT/rel).with_suffix('.olean')
 if not p.is_file():
  kinds['broken' if p.is_symlink() else 'missing']+=1;rows[name]={'exists':False,'symlink':p.is_symlink()};continue
 kind='symlink' if p.is_symlink() else 'regular';kinds[kind]+=1
 resolved=p.resolve();assert '/lib/' in str(resolved),str(resolved)
 provider=Path(str(resolved).split('/lib/')[0]);providers[str(provider)]+=1
 candidate=(provider/'src'/rel).with_suffix('.lean')
 if candidate.is_file():
  h=sha(candidate);state='same' if h==row['sha256'] else 'different';src_counts[state]+=1
  src={'path':str(candidate),'sha256':h,'comparison':state}
 else:src_counts['absent']+=1;src=None
 entry={'exists':True,'symlink':p.is_symlink(),'object_sha256':sha(p),'resolved':str(resolved),'adjacent_source':src}
 if resolved.is_relative_to(HA):
  snap=(HASRC/rel).with_suffix('.lean')
  assert snap.is_file(),name
  h=sha(snap);state='same' if h==row['sha256'] else 'different';ha_counts[state]+=1
  entry['ha87_frozen_source']={'path':str(snap),'sha256':h,'comparison':state}
 rows[name]=entry
assert len(rows)==658
print(json.dumps({'status':'PASS','scope':'658 pinned project modules only; current objects resolved through one peer overlay',
 'receipt_sha256':sha(RECEIPT),'overlay':str(ROOT),'object_counts':dict(kinds),'adjacent_source_heuristic_counts':dict(src_counts),
 'ha87_frozen_source_comparison':dict(ha_counts),'resolved_provider_counts':dict(sorted(providers.items())),
 'objects':rows,'limits':['No Lean execution, build, provider changes, object provenance, source/object authenticity, search-path validation, companion-file or package-closure audit.',
 'Adjacent src path is a heuristic; matching source bytes do not prove the object was built from them.',
 'Historical HA87 frozen source comparison does not prove current compatibility or incompatibility.',
 'This is neither a selected coherent provider nor build readiness.']},sort_keys=True,indent=2))
