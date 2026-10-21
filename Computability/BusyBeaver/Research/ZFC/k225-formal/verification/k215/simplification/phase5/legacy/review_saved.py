"""Validate archived legacy records; never execute archived code or inspect live objects."""
from pathlib import Path
import argparse,json,tarfile
from evidence import digest,read,safe,save,sha,validate
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--packet',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--primary-packet',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 assert not a.output.exists();s=read(a.packet/'review.json');idx=read(a.packet/'index.json');m={}
 assert sha(a.packet/'execution.tar.gz')==s['archive_sha256']
 with tarfile.open(a.packet/'execution.tar.gz','r:gz')as t:
  for x in t:
   assert x.isfile()and safe(x.name)and x.name not in m
   b=t.extractfile(x).read();assert idx[x.name]=={'sha256':digest(b),'bytes':len(b)};m[x.name]=b
 assert set(m)==set(idx);r=validate(m)
 lr=json.loads(m['publication/live-review.json']);assert lr==read(a.packet/'live-review.json')
 assert lr['status']=='PASS_LIVE_LEGACY_POST_AUDIT_REVIEW' and lr['all199_objects_rehashed_after_audit'] and lr['basis184_unchanged']
 assert lr['result_sha256']==digest(m['execution/result.json'])
 assert lr['evidence_manifest']=={n:idx[n]for n in idx if not n.startswith('publication/')}
 assert all(s[k]==v for k,v in lr.items()if k!='evidence_manifest')
 assert all(lr[k]==v and s[k]==v for k,v in r.items()if k!='status')
 ref=read(a.packet/'primary-reference.json');assert ref==json.loads(m['publication/primary-reference.json'])
 assert set(ref['files'])=={'execution.tar.gz','index.json','result.json','live-review.json'}
 assert ref['original_result_sha256']==digest(m['execution/basis-result.json'])
 if a.primary_packet:
  for name,h in ref['files'].items():assert sha(a.primary_packet/name)==h
  pr=read(a.primary_packet/'result.json');pl=read(a.primary_packet/'live-review.json')
  assert all(pr[k]==v for k,v in json.loads(m['execution/basis-result.json']).items())
  assert pl==json.loads(m['execution/basis-review.json'])
  assert pr['execution_archive_sha256']==ref['files']['execution.tar.gz']
 r.update(primary_packet_hashes_checked=bool(a.primary_packet),scope=r['scope']+' Primary archive is not duplicated or revalidated internally by this reader.')
 save(a.output,r);print(json.dumps(r,indent=2))
