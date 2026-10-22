"""Validate phase15 recorded evidence and its pinned local phase14 predecessor."""
from pathlib import Path
import argparse,json,tarfile
import packet

def review(directory,basis_repo,repo=None):
 directory=Path(directory);summary=json.loads((directory/'result.json').read_text());index=json.loads((directory/'index.json').read_text());members={}
 assert summary['status']=='PASS_COLLECTED_PHASE15'and packet.sha(directory/'execution.tar.gz')==summary['archive_sha256']and packet.sha(directory/'index.json')==summary['index_sha256']
 with tarfile.open(directory/'execution.tar.gz','r:gz')as stream:
  for item in stream:
   packet.safe(item.name);assert item.isfile()and item.name not in members;b=stream.extractfile(item).read();assert index[item.name]=={'sha256':packet.digest(b),'bytes':len(b)};members[item.name]=b
 assert packet.manifest(members)==index and len(members)==summary['archive_members']
 for n in ['basis.py','basis-reference.json','packet.py','review_saved.py','README.md']:assert(directory/n).read_bytes()==members['review/'+n]
 freeze=json.loads(members['review/freeze.json']);assert freeze['status']=='FROZEN_PUBLICATION_HELPERS_NOT_EXECUTED'
 for n,p in freeze['files'].items():assert packet.digest(members['review/'+n])==p
 checked=packet.validate(members,basis_repo,current_repo=repo)
 assert all(summary[k]==v for k,v in checked.items()if k not in {'status','current_sources_checked'})
 post=json.loads(members['review/live-postcheck.json']);assert post==summary['live_postcheck']and post['status']=='PASS_LIVE_POSTCHECK'
 assert post['providers']=={packet.FIRST:87,packet.SECOND:193,packet.MAIN:194,packet.COMP:71}and post['combined_project_sources']==199 and post['endpoint_audit_objects']==2
 assert post['all_live_sources_objects_logs_dependencies_rehashed']and post['both_failed_primary_attempts_preserved']and post['resumed_provider_counts']==[87,193]and post['selected_primary_fresh_by_attempt']==[19,25,1]
 cfg=json.loads(members['review/config.json']);assert post['historical_inputs']==cfg['historical_inputs']and post['current_adoptions']==packet.ADOPTIONS and post['unchanged_prior_adoptions']==packet.PRIOR_ADOPTIONS
 assert post['retained_absences']==packet.RETAINED_ABSENCES and post['created_path']==packet.CREATED
 for root,label in [(packet.FIRST,'failed-primary1'),(packet.SECOND,'failed-primary2'),(packet.MAIN,'execution'),(packet.COMP,'compatibility')]:assert post['before_input_counts'][root]==len(json.loads(members[label+'/before.json'])['inputs'])
 return {**checked,'status':'PASS_SAVED_PHASE15','archive_sha256':summary['archive_sha256'],'archive_members':len(members),'reviewer_sha256':packet.sha(__file__),'validator_sha256':packet.sha(Path(__file__).with_name('packet.py'))}
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--packet',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--basis-repo',type=Path,required=True);p.add_argument('--repo',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args();assert not a.output.exists();r=review(a.packet,a.basis_repo,a.repo);a.output.write_bytes(packet.dump(r));print(json.dumps(r,indent=2))
