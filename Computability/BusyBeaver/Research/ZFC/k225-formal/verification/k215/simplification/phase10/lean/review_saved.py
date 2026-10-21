"""Check compact saved phase10 evidence and its exact local phase9 reference."""
from pathlib import Path
import argparse,json,tarfile
import packet

def review(directory,basis_repo,repo=None):
 directory=Path(directory);summary=json.loads((directory/'result.json').read_text());index=json.loads((directory/'index.json').read_text());members={}
 assert summary['status']=='PASS_COLLECTED_PHASE10'and packet.sha(directory/'execution.tar.gz')==summary['archive_sha256']and packet.sha(directory/'index.json')==summary['index_sha256']
 with tarfile.open(directory/'execution.tar.gz','r:gz')as stream:
  for item in stream:
   packet.safe(item.name);assert item.isfile()and item.name not in members;data=stream.extractfile(item).read();assert index[item.name]=={'sha256':packet.digest(data),'bytes':len(data)};members[item.name]=data
 assert packet.manifest(members)==index and len(members)==summary['archive_members']
 for name in ['basis.py','basis-reference.json','packet.py','review_saved.py']:
  assert (directory/name).read_bytes()==members['review/'+name]
 checked=packet.validate(members,basis_repo,current_repo=repo)
 assert all(summary[k]==v for k,v in checked.items()if k not in{'status','current_sources_checked'})
 post=json.loads(members['review/live-postcheck.json']);assert post==summary['live_postcheck']and post['status']=='PASS_LIVE_POSTCHECK'
 assert post['main_modules']==197 and post['isolated_modules']==16 and post['audit_objects']==2
 assert post['all_live_sources_objects_logs_rehashed']and post['all_nonproducer_inputs_current_exact']and post['old5_producer_snapshot_pins_exact']
 return {**checked,'status':'PASS_SAVED_PHASE10','archive_sha256':summary['archive_sha256'],'archive_members':len(members),'reviewer_sha256':packet.sha(__file__),'validator_sha256':packet.sha(Path(__file__).with_name('packet.py'))}

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--packet',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--basis-repo',type=Path,required=True);p.add_argument('--repo',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args();assert not a.output.exists();result=review(a.packet,a.basis_repo,a.repo);a.output.write_bytes(packet.dump(result));print(json.dumps(result,indent=2))
