#!/usr/bin/env python3
"""Create a deterministic ZIP only from a trusted, exact report inventory."""
import argparse, hashlib, json, zipfile
from pathlib import Path
from verify_release import authenticate
ROOT=Path(__file__).resolve().parent
def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',required=True,type=Path)
    parser.add_argument('--manifest-sha256',required=True)
    args=parser.parse_args();out=args.output.resolve()
    if out==ROOT or ROOT in out.parents:raise RuntimeError('Archive output must be external')
    manifest=authenticate(ROOT,args.manifest_sha256)
    paths=sorted(set(manifest['files'])|{'MANIFEST.json'})
    with zipfile.ZipFile(out,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as archive:
        for name in paths:
            info=zipfile.ZipInfo('free83-report43/'+name,(2026,10,4,0,0,0))
            info.create_system=3;info.external_attr=0o100644<<16
            info.compress_type=zipfile.ZIP_DEFLATED
            archive.writestr(info,(ROOT/name).read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
    authenticate(ROOT,args.manifest_sha256)
    raw=out.read_bytes()
    print(json.dumps({'status':'PASS','files':len(paths),'bytes':len(raw),
                      'sha256':hashlib.sha256(raw).hexdigest()},sort_keys=True,indent=2))
if __name__=='__main__':main()
