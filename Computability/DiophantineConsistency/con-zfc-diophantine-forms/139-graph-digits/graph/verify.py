#!/usr/bin/env python3
"""Independent coefficient/certificate checks and optional exact reconstruction."""
import argparse
import hashlib
import json
from pathlib import Path
from independent_verify import verify_data, negative_controls

ROOT=Path(__file__).resolve().parent

def main():
    pa=argparse.ArgumentParser(description=__doc__)
    pa.add_argument('--rebuild',action='store_true');pa.add_argument('--output',type=Path)
    args=pa.parse_args();results=[]
    pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for entry in pins['files']:
        b=(ROOT/entry['local']).read_bytes()
        blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        if len(b)!=entry['size'] or blob!=entry['git_blob'] or hashlib.sha256(b).hexdigest()!=entry['sha256']:
            raise ValueError('Pinned source identity failed: '+entry['local'])
    for profile in json.loads((ROOT/'profiles.json').read_text()):
        source=ROOT/profile['source'];d=ROOT/'equations'/profile['name']
        s=json.loads(source.read_text());p=json.loads((d/'polynomial.json').read_text());c=json.loads((d/'certificate.json').read_text())
        if c.get('source_sha256')!=hashlib.sha256(source.read_bytes()).hexdigest():raise ValueError('Certificate source hash mismatch')
        r=verify_data(s,p,c);r['negative_controls']=negative_controls(s,p,c);r['profile']=profile['name']
        if args.rebuild:
            from build import build
            p2,c2=build(profile)
            for name,val in [('polynomial.json',p2),('certificate.json',c2),('metrics.json',p2['metrics'])]:
                raw=(json.dumps(val,sort_keys=True,separators=(',',':'))+'\n').encode()
                if raw!=(d/name).read_bytes():raise ValueError('Rebuild differs: '+str(d/name))
            r['byte_exact_rebuild']=True
        r['sha256']={name:hashlib.sha256((d/name).read_bytes()).hexdigest() for name in ['polynomial.json','certificate.json']}
        results.append(r)
        print(profile['name']+': PASS; '+str(r['metrics']['variables'])+' variables; '+str(r['metrics']['monomials'])+' terms',flush=True)
    out={'status':'pass','source_commit':pins['commit'],'profiles':results,'checker_sha256':hashlib.sha256((ROOT/'independent_verify.py').read_bytes()).hexdigest(),
         'scope':'Exact finite algebra and certificate checks. The signed source calibration is inherited from pinned ProveIt sources.'}
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(out,indent=2)+'\n')

if __name__=='__main__':main()
