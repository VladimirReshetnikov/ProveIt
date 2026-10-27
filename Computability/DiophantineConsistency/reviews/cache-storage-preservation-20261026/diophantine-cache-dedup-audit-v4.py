from pathlib import Path
import hashlib,json,os
bases=[Path('/tmp')/s for s in ['current-positive-zero2011-closure-validation-20261026a/lib','current-narrow-native-root-2wv7shqg/lib','fixed-consistency73-root-xu0y__b6/lib','merged-native-20261026-054ycdsy/lib','zfc-native90-integration-qm3yz_m4','zfc-native91-integration-yduvdh8f','zfc-quotient89-integration-66alav7r']]
groups={};records=[]
for base in bases:
 for p in base.rglob('*'):
  if not p.is_file() or p.is_symlink() or p.suffix not in {'.olean','.private','.server','.ilean'}:continue
  h=hashlib.sha256(p.read_bytes()).hexdigest();key=(p.stat().st_size,h)
  if key not in groups:groups[key]=p;continue
  q=groups[key]
  if os.path.samefile(p,q):continue
  records.append(dict(duplicate=str(p),keeper=str(q),bytes=key[0],sha256=h))
d=dict(scope='Read-only proposal: exact byte duplicate regular compiled artifacts in seven completed immutable caches; no active output, source or symlink is selected.',records=records,reclaimable_bytes=sum(e['bytes'] for e in records))
Path('/tmp/diophantine-cache-dedup-audit-v4.json').write_text(json.dumps(d,indent=2)+'\n')
print(json.dumps(dict(files=len(records),bytes=d['reclaimable_bytes'],examples=records[:8]),indent=2))
