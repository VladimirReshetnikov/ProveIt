#!/usr/bin/env python3
"""Bind every nonliteral leaf to a fixed signed integer, without a network."""
from pathlib import Path
import gzip,hashlib,json
ROOT=Path(__file__).resolve().parent
def values(circuit):
    names=('beta','K','MC','MF_source');ports=[int.from_bytes(gzip.decompress((ROOT/'coefficients'/(n+'.bin.gz')).read_bytes()),'little') for n in names]
    result={'base_scale':1<<circuit['base_scale_exponent'],'threshold_scale':1<<circuit['threshold_scale_exponent']}
    for recipe in circuit['coefficient_recipes']:
        ans=0
        for t in recipe['terms']:
            v=t['coefficient']
            for p,e in zip(ports,t['powers']):v*=p**e
            ans+=v
        result[recipe['name']]=ans
    return result
def materialize():
    body=json.loads((ROOT/'generated/split_116_positive_global.json').read_text());fixed=values(body);used={n['name'] for n in body['nodes'] if n['kind']=='fixed'}
    out=ROOT/'fixed';out.mkdir(exist_ok=True);entries=[]
    for name in sorted(used):
        v=fixed[name];raw=abs(v).to_bytes((abs(v).bit_length()+7)//8,'little');p=out/(name+'.bin.gz');p.write_bytes(gzip.compress(raw,mtime=0))
        entries.append({'name':name,'sign':-1 if v<0 else 1,'bits':abs(v).bit_length(),'raw_bytes':len(raw),'file':str(p.relative_to(ROOT)),'raw_sha256':hashlib.sha256(raw).hexdigest(),'gzip_sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
    (ROOT/'fixed/BINDING.json').write_text(json.dumps({'whole_native_tuple':'compact44, base 2^590069','integer_encoding':'sign in metadata, unsigned little-endian magnitude in gzip file','entries':entries},indent=2)+'\n');print({'fixed_leaves':len(entries),'raw_bytes':sum(x['raw_bytes'] for x in entries),'compressed_bytes':sum((ROOT/x['file']).stat().st_size for x in entries)})
if __name__=='__main__':materialize()
