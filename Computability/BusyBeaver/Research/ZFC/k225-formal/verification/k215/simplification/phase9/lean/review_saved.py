"""Read a phase9 packet and exact local phase8 ancestry; no proof tools are run."""
from pathlib import Path
import argparse
import json
import tarfile
from evidence import digest, manifest, safe_name, save, sha, validate


def review(packet,basis_repo,repo=None):
    packet=Path(packet);summary=json.loads((packet/'result.json').read_text())
    index=json.loads((packet/'index.json').read_text());archive=packet/'execution.tar.gz'
    assert summary['status']=='PASS_COLLECTED_PHASE9_EVIDENCE'
    assert sha(archive)==summary['archive_sha256'] and sha(packet/'index.json')==summary['index_sha256']
    members={}
    with tarfile.open(archive,'r:gz')as stream:
        for entry in stream:
            safe_name(entry.name);assert entry.isfile()and entry.name not in members
            data=stream.extractfile(entry).read()
            assert index[entry.name]=={'sha256':digest(data),'bytes':len(data)}
            members[entry.name]=data
    assert manifest(members)==index and len(members)==summary['archive_members']
    for name in ('basis_reference.py','basis-reference.json','evidence.py','review_saved.py','auxiliary.py'):
        assert (packet/name).read_bytes()==members['review/'+name]
    post=json.loads(members['review/collector-postcheck.json'])
    assert post==summary['collector_postcheck'] and post['status']=='PASS_COLLECTOR_POSTCHECK'
    assert post['all_current_objects_rehashed_after_audits']and post['all_before_inputs_unchanged']
    assert post['modules']==197 and post['typed_clients']==2
    assert post['auxiliary']['status']=='PASS_COLLECTOR_POSTCHECK' and post['auxiliary']['modules']==18
    assert post['auxiliary']['all_current_objects_rehashed_after_audits'] and post['auxiliary']['all_before_inputs_unchanged']
    assert post['auxiliary']['result_sha256']==summary['auxiliary']['result_sha256']
    assert post['collector_sha256']==digest(members['review/bundle.py'])
    assert post['result_sha256']==digest(members['execution/result.json'])
    checked=validate(members,basis_repo,repo)
    # --repo adds current-source checking rather than altering the saved historical receipt.
    assert all(summary[k]==v for k,v in checked.items()if k not in {'status','current_sources_checked'})
    return {**checked,'status':'PASS_SAVED_PHASE9_PACKET','archive_sha256':sha(archive),
            'archive_members':len(members),'reviewer_sha256':sha(__file__),
            'validator_sha256':sha(Path(__file__).with_name('evidence.py'))}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet',type=Path,default=Path(__file__).resolve().parent)
    parser.add_argument('--basis-repo',type=Path,required=True)
    parser.add_argument('--repo',type=Path)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();assert not args.output.exists()
    result=review(args.packet,args.basis_repo,args.repo);save(args.output,result)
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
