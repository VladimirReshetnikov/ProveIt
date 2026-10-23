#!/usr/bin/env python3
"""Materialize all twelve nonliteral integer leaves; no decimal expansion."""
from pathlib import Path
import gzip,hashlib,json
R=Path(__file__).resolve().parent

def values(variant='shared_taps'):
    binding=json.loads((R/'coefficients/COEFFICIENT_BINDING.json').read_text())
    vals={}
    for rec in binding['files']:
        raw=gzip.decompress((R/'coefficients'/rec['file']).read_bytes())
        if hashlib.sha256(raw).hexdigest()!=rec['sha256']:raise ValueError('native payload hash')
        vals[rec['port']]=int.from_bytes(raw,'little')
    ports=[vals['beta'],vals['K'],vals['MC'],vals['MF_source']]
    body=json.loads((R/'generated'/f'{variant}_positive.json').read_text())
    used={n['name'] for n in body['nodes'] if n['kind']=='fixed'}
    out={}
    for rec in body['coefficient_recipes']:
        if rec['name'] not in used:continue
        value=0
        for t in rec['terms']:
            term=t['coefficient']
            for p,e in zip(ports,t['powers']):term*=p**e
            value+=term
        out[rec['name']]=value
    out['base_scale']=1<<body['base_scale_exponent']
    out['threshold_scale']=1<<body['threshold_scale_exponent']
    if set(out)!=used:raise ValueError('fixed leaf coverage')
    return out

def main():
    result={}
    for variant in ['shared_taps','shared_taps_economy']:
        outdir=R/'fixed'/variant;outdir.mkdir(parents=True,exist_ok=True)
        records=[]
        for name,val in values(variant).items():
            raw=abs(val).to_bytes(max(1,(abs(val).bit_length()+7)//8),'little')
            compressed=gzip.compress(raw,mtime=0)
            (outdir/f'{name}.bin.gz').write_bytes(compressed)
            records.append(dict(name=name,sign=-1 if val<0 else 1,file=f'{name}.bin.gz',bit_length=abs(val).bit_length(),raw_bytes=len(raw),gzip_bytes=len(compressed),raw_sha256=hashlib.sha256(raw).hexdigest(),gzip_sha256=hashlib.sha256(compressed).hexdigest()))
        manifest={'format':'unsigned little-endian magnitude, sign in manifest','records':records,'total_raw_bytes':sum(x['raw_bytes'] for x in records),'total_gzip_bytes':sum(x['gzip_bytes'] for x in records)}
        (outdir/'BINDING.json').write_text(json.dumps(manifest,indent=2)+'\n')
        result[variant]={k:v for k,v in manifest.items() if k!='records'}
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
