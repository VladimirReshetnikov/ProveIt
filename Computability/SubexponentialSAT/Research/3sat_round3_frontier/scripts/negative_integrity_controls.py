#!/usr/bin/env python3
"""Independent malformed-bundle controls for verifier rejection paths."""
import argparse,json,pathlib,stat,tempfile,zipfile
from verify_bundle import verify

def main():
    p=argparse.ArgumentParser();p.add_argument('archive');a=p.parse_args()
    with zipfile.ZipFile(a.archive) as z:original=[(i,z.read(i.filename)) for i in z.infolist()]
    results={}
    with tempfile.TemporaryDirectory(prefix='sat-negative-') as tmp:
        for case in ['corrupt_payload','extra_member','missing_member','unsafe_path','symlink','duplicate']:
            dest=pathlib.Path(tmp)/(case+'.zip');rows=list(original)
            if case=='corrupt_payload':
                for j,(info,b) in enumerate(rows):
                    if info.filename=='README.md':rows[j]=(info,b+b'changed');break
            if case=='extra_member':rows.append((zipfile.ZipInfo('unexpected.txt'),b'x'))
            if case=='missing_member':rows=[x for x in rows if x[0].filename!='README.md']
            if case=='unsafe_path':rows.append((zipfile.ZipInfo('../escape'),b'x'))
            if case=='symlink':
                info=zipfile.ZipInfo('link');info.external_attr=(stat.S_IFLNK|0o777)<<16;rows.append((info,b'target'))
            if case=='duplicate':rows.append(rows[0])
            with zipfile.ZipFile(dest,'w',zipfile.ZIP_DEFLATED) as z:
                for i,b in rows:z.writestr(i,b)
            try:verify(dest)
            except (ValueError,KeyError):results[case]='rejected'
            else:raise RuntimeError('negative control accepted: '+case)
    print(json.dumps({'status':'PASS','negative_controls':results},indent=2))
if __name__=='__main__':main()
