"""Review compact phase12 records and an exact local phase11 reference, without Lean."""
from pathlib import Path
import argparse,json,tarfile
import packet

def review(directory,basis_repo,repo=None):
 directory=Path(directory);summary=json.loads((directory/'result.json').read_text());index=json.loads((directory/'index.json').read_text());members={}
 assert summary['status']=='PASS_COLLECTED_PHASE12'and packet.sha(directory/'execution.tar.gz')==summary['archive_sha256']and packet.sha(directory/'index.json')==summary['index_sha256']
 with tarfile.open(directory/'execution.tar.gz','r:gz')as stream:
  for item in stream:
   packet.safe(item.name);assert item.isfile()and item.name not in members;data=stream.extractfile(item).read();assert index[item.name]=={'sha256':packet.digest(data),'bytes':len(data)};members[item.name]=data
 assert packet.manifest(members)==index and len(members)==summary['archive_members']
 for name in ['basis.py','basis-reference.json','packet.py','review_saved.py']:
  assert (directory/name).read_bytes()==members['review/'+name]
 checked=packet.validate(members,basis_repo,current_repo=repo)
 assert all(summary[k]==v for k,v in checked.items()if k not in{'status','current_sources_checked'})
 post=json.loads(members['review/live-postcheck.json']);assert post==summary['live_postcheck']and post['status']=='PASS_LIVE_POSTCHECK'
 assert post['primary_providers']==184 and post['compatibility_providers']==69 and post['combined_project_sources']==199 and post['endpoint_audit_objects']==2
 assert post['all_live_sources_objects_logs_rehashed']and post['all_before_inputs_rehashed_except_one_explicit_historical_producer']
 assert post['historical_producer']==packet.ROOT+'/'+packet.PRODUCER and post['historical_sha256']==packet.OLD_PRODUCER and post['current_producer_sha256']==packet.NEW_PRODUCER
 assert post['current_writes']==8 and post['current_absent_templates']==2
 return{**checked,'status':'PASS_SAVED_PHASE12','archive_sha256':summary['archive_sha256'],'archive_members':len(members),'reviewer_sha256':packet.sha(__file__),'validator_sha256':packet.sha(Path(__file__).with_name('packet.py'))}
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--packet',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--basis-repo',type=Path,required=True);p.add_argument('--repo',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args();assert not a.output.exists();result=review(a.packet,a.basis_repo,a.repo);a.output.write_bytes(packet.dump(result));print(json.dumps(result,indent=2))
