"""Validate the compact archived legacy packet and pinned predecessor data only."""
from pathlib import Path
import argparse,json
from evidence import sha,digest,read,save,members,manifest_hash,validate

def review(packet,basis_repo,current_repo=None):
 summary=read(packet/'result.json');index=read(packet/'index.json');assert sha(packet/'execution.tar.gz')==summary['execution_archive_sha256']
 m=members(packet/'execution.tar.gz',index);assert len(m)==summary['archive_members']
 raw=json.loads(m['execution/result.json']);assert all(summary[k]==v for k,v in raw.items())
 livebytes=m.pop('publication/live-review.json');live=json.loads(livebytes)
 assert livebytes==(packet/'live-review.json').read_bytes()and digest(livebytes)==summary['live_review_sha256']
 assert live['status']=='PASS_LIVE_LEGACY_POST_AUDIT_REVIEW'and live['evidence_manifest_sha256']==manifest_hash(m)
 assert live['all202_selected_objects_and_logs_rehashed_after_audit']and live['all_immutable_predecessor_inputs_unchanged']and live['fresh_audit_object_rehashed']
 assert digest(m['review/review.py'])==live['reviewer_sha256']and digest(m['review/evidence.py'])==live['validator_sha256']and digest(m['review/capture.py'])==live['capture_sha256']
 for n in ['evidence.py','review_saved.py']:assert(packet/n).read_bytes()==m['review/'+n]
 assert(packet/'references.json').read_bytes()==m['publication/references.json']
 check=validate(m,basis_repo,current_repo);assert all(live[k]==v for k,v in check.items()if k!='status')
 assert not summary['compiled_objects_in_archive']
 return {**check,'status':'PASS_SAVED_LEGACY_EVIDENCE','archive_sha256':sha(packet/'execution.tar.gz'),'summary_sha256':sha(packet/'result.json'),'archive_members':len(index),'current_sources_checked':current_repo is not None,'reviewer_sha256':sha(__file__),'no_live_objects_or_compiler':True}
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--packet',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--basis-repo',type=Path,required=True);p.add_argument('--repo',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args();assert not a.output.exists();r=review(a.packet,a.basis_repo,a.repo);save(a.output,r);print(json.dumps(r,indent=2))
