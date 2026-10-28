#!/usr/bin/env python3
"""Build a deterministic compact ZIP from an explicit manifest allowlist."""
import argparse,hashlib,json,pathlib,zipfile
ROOT=pathlib.Path(__file__).resolve().parent.parent

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('output',type=pathlib.Path);p.add_argument('--validation-summary',action='store_true');a=p.parse_args()
    names=json.loads((ROOT/'scripts/bundle_allowlist.json').read_text())
    if a.validation_summary:names+=['qa/RELEASE_VALIDATION.json','qa/VISUAL_REVIEW.md']
    data={n:(ROOT/n).read_bytes() for n in sorted(names)}
    m={'format':1,'source_pin':'047f4f0426fa38d1fe02f194aa6aac254c42f643',
       'scope':'Relative normalized coefficient refinement; no stronger unrestricted logarithmic order or formal proof.',
       'files':{n:{'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()} for n,b in data.items()}}
    data['MANIFEST.sha256.json']=(json.dumps(m,indent=2,sort_keys=True)+'\n').encode()
    a.output.parent.mkdir(parents=True,exist_ok=True)
    with zipfile.ZipFile(a.output,'w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
        for n,b in sorted(data.items()):
            i=zipfile.ZipInfo(n,(2026,10,27,0,0,0));i.compress_type=zipfile.ZIP_DEFLATED;i.external_attr=0o100644<<16;z.writestr(i,b)
    b=a.output.read_bytes()
    if len(b)>=4_000_000:raise ValueError('archive is not below 4 MB')
    print(json.dumps({'archive':str(a.output),'bytes':len(b),'entries':len(data),'sha256':hashlib.sha256(b).hexdigest()},indent=2))
if __name__=='__main__':main()
