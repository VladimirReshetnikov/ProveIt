#!/usr/bin/env python3
"""One exact norm-tail saving for the three accepted position-zero circuits."""
import argparse
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1]
DEST=ROOT/'candidates/position-zero-norm-sharing'
sys.path.insert(0,str(ROOT/'tools'))
from build_norm_tail_sharing import transform,verify


def need(ok,text):
    if not ok:raise ValueError(text)


def encoded(x):return(json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()


def build():
    spec=importlib.util.spec_from_file_location('independent_position_norm',DEST/'check.py')
    check=importlib.util.module_from_spec(spec);spec.loader.exec_module(check)
    files={};pins={};cases=[]
    with check.load_archive()as z:
        for case in check.CASES:
            name=case['name'];member=check.BASE+'equations/'+name+'.json';raw=z.read(member)
            need(check.digest(raw)==case['parent_sha256'],'accepted parent bytes')
            parent=json.loads(raw)
            configured=dict(case,parent='ZIP:'+str(check.ARCHIVE.relative_to(check.REPO))+'!'+member,
                            fixed_binding='FIXED_BINDINGS.json#'+case['profile'])
            child,cert=transform(parent,configured);verify(parent,child,cert)
            fixed,pin=check.fixed_values(z,case['profile'],parent);pins[case['profile']]=pin
            cert.update(parent_archive_sha256=check.ARCHIVE_SHA,parent_member=member,parent_sha256=check.digest(raw),
                        child_sha256=check.digest(encoded(child)))
            check.verify_identity(parent,child,cert,case)
            files[name+'.json']=encoded(child);files[name+'_identity.json']=encoded(cert)
            cases.append(dict(name=name,operations=child['total_operations'],degree=case['degree'],parent_sha256=check.digest(raw)))
        retained_proofs={name:check.digest(z.read(check.BASE+name))for name in
                         ['report_section.tex','normalization_check.py','exact_audit.py','SOURCE_PINS.json']}
    files['FIXED_BINDINGS.json']=encoded(pins)
    files['SOURCE_PINS.json']=encoded(dict(archive=str(check.ARCHIVE.relative_to(check.REPO)),archive_sha256=check.ARCHIVE_SHA,
        parents=check.CASES,required_inherited_proof_members=retained_proofs,
        fixed_storage='All fixed payloads are read directly from the authenticated incoming ZIP; no component copy or new native generation.',
        prior_ordinary_review='reviews/constructive-nine-peer.md',
        prior_review_sha256=check.digest((ROOT/'reviews/constructive-nine-peer.md').read_bytes())))
    files['BUILD.json']=encoded(dict(status='PASS',generator_sha256=check.digest(Path(__file__).read_bytes()),
        shared_transform_sha256=check.digest((ROOT/'tools/build_norm_tail_sharing.py').read_bytes()),
        independent_checker_sha256=check.digest((DEST/'check.py').read_bytes()),cases=cases,
        sha256={name:check.digest(raw)for name,raw in files.items()}))
    return files,cases


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');args=ap.parse_args()
    files,cases=build()
    for name,raw in files.items():
        path=DEST/name
        if args.check:need(path.read_bytes()==raw,'byte-exact new sibling '+name)
        else:path.write_bytes(raw)
    print(json.dumps(dict(status='PASS',check=args.check,cases=cases),indent=2))


if __name__=='__main__':main()
