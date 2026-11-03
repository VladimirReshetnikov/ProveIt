from pathlib import Path
from hashlib import sha256
import os,json
b=Path('research/trace75-bfs-provider-preflight');p=b/'observations/compare-attempt01/result.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def rec(p):
 p=Path(p)
 if not os.path.lexists(p):return None
 assert p.is_file(),p
 return {'path':str(p),'real_path':str(p.resolve(strict=True)),'sha256':sha(p),'link':os.readlink(p) if p.is_symlink() else None}
assert sha(p)=='7466cf187de963c0ccc2c112d7b8dc77dcddaf0ae3fda47f76e8ad9d54cf64a8';j=json.loads(p.read_text());assert j['status']=='PASS' and sha(b/'compare.py')==j['runner_sha256'];assert sha(j['bfs_receipt'])==j['bfs_receipt_sha256']=='ca79d2e68509999cb2a6cd43759e31d656796f09719239c0adac259b7cadb559'
a=Path(j['trace75_overlay']);z=Path(j['bfs_union']); aa={x.relative_to(a).as_posix():x for x in a.rglob('*.olean') if x.is_file()};bb={x.relative_to(z).as_posix():x for x in z.rglob('*.olean') if x.is_file()};common=aa.keys()&bb.keys();different={n for n in common if sha(aa[n])!=sha(bb[n])};assert len(common)==j['common_count']==997 and len(different)==j['mismatch_count']==5
assert different==set(j['mismatches'])=={'ModelRatioBounds.olean','ArithmeticNegativeNorms.olean','ArithmeticCarrierRadix2011.olean','ArithmeticWindowInterface.olean','ArithmeticCarrierSoundness2011.olean'}
for n in sorted(different):
 r=j['mismatches'][n];assert r['same'] is False and r['trace75']==rec(aa[n]) and r['bfs']==rec(bb[n]);stem=n[:-6]
 for label,root in [('trace75',a),('bfs',z)]:
  for suffix,value in r['companions'][label].items():assert rec(root/(stem+suffix))==value,(n,label,suffix)
 print(n,r['trace75']['sha256'],r['bfs']['sha256'])
print('PASS: all 997 shared objects rehashed; exact five mismatches and all reported companion paths/hash/link records rechecked; namespace overlap alone does not establish either ancestry.')
