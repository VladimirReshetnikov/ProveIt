#!/usr/bin/env python3
"""Materialize every live fixed leaf of the primary polynomial from its bound ports."""
from pathlib import Path
from math import prod
import gzip,hashlib,io,json
ROOT=Path(__file__).resolve().parent

def load_ports():
    binding=json.loads((ROOT/'COEFFICIENT_BINDING.json').read_text());values={}
    for item in binding['payloads']:
        payload=gzip.decompress((ROOT/item['path']).read_bytes())
        if hashlib.sha256(payload).hexdigest()!=item['sha256']:raise ValueError('port hash '+item['name'])
        z=int.from_bytes(payload,'little')
        if z.bit_length()!=item['bit_length']:raise ValueError('port bit length')
        values[item['name']]=z
    return [values[n] for n in ['beta','K','MC','MF_source']]

def leaf_values(body):
    ports=load_ports();needed={n['name'] for n in body['nodes'] if n['kind']=='fixed'}
    recipes={r['name']:r['terms'] for r in body['coefficient_recipes']}
    for name in sorted(needed):
        if name=='base_scale':value=1<<body['base_scale_exponent']
        elif name=='threshold_scale':value=1<<body['threshold_scale_exponent']
        else:value=sum(t['coefficient']*prod(z**e for z,e in zip(ports,t['powers'])) for t in recipes[name])
        yield name,value

def main():
    body=json.loads((ROOT/'generated/calibrated_absorbed_positive.json').read_text());(ROOT/'fixed').mkdir(exist_ok=True);records=[]
    for name,z in leaf_values(body):
        magnitude=abs(z);raw=bytes([int(z<0)])+magnitude.to_bytes(max(1,(magnitude.bit_length()+7)//8),'little')
        stream=io.BytesIO()
        with gzip.GzipFile(fileobj=stream,filename='',mode='wb',mtime=0) as out:out.write(raw)
        packed=stream.getvalue();path='fixed/'+name+'.bin.gz';(ROOT/path).write_bytes(packed)
        records.append({'name':name,'path':path,'sign':-1 if z<0 else 1,'magnitude_bit_length':magnitude.bit_length(),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),'gzip_bytes':len(packed),'gzip_sha256':hashlib.sha256(packed).hexdigest()})
    result={'encoding':'one sign byte (0 nonnegative, 1 negative), followed by minimal unsigned little-endian magnitude; gzip transport','equation':'generated/calibrated_absorbed_positive.json','leaf_count':len(records),'raw_bytes':sum(x['bytes'] for x in records),'gzip_bytes':sum(x['gzip_bytes'] for x in records),'leaves':records}
    (ROOT/'fixed/MANIFEST.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='leaves'},indent=2))
if __name__=='__main__':main()
