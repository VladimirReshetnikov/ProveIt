#!/usr/bin/env python3
"""Materialize every nonliteral leaf of the new nine-variable circuit."""
import gzip,hashlib,json,pathlib
R=pathlib.Path(__file__).resolve().parent
def main():
    ports={}
    binding=json.loads((R/'coefficients/BINDING.json').read_text())
    for row in binding['files']:
        packed=(R/'coefficients'/(row['name']+'.bin.gz')).read_bytes();raw=gzip.decompress(packed)
        if hashlib.sha256(packed).hexdigest()!=row['gzip_sha256'] or hashlib.sha256(raw).hexdigest()!=row['sha256']:raise ValueError('coefficient identity')
        ports[row['name']]=int.from_bytes(raw,'little')
    body=json.loads((R/'generated/split_111_positive.json').read_text());v=[ports[x] for x in ['beta','K','MC','MF_source']]
    fixed={row['name']:sum(t['coefficient']*__import__('math').prod(pow(z,e) for z,e in zip(v,t['powers'])) for t in row['terms']) for row in body['coefficient_recipes']}
    fixed['base_scale']=1<<body['base_scale_exponent'];fixed['threshold_scale']=1<<body['threshold_scale_exponent']
    leaves=sorted({n['name'] for n in body['nodes'] if n['kind']=='fixed'});out=R/'fixed';out.mkdir(exist_ok=True);rows=[]
    for name in leaves:
        value=fixed[name];raw=abs(value).to_bytes((abs(value).bit_length()+7)//8,'little');compressed=gzip.compress(raw,mtime=0)
        (out/(name+'.bin.gz')).write_bytes(compressed)
        rows.append({'name':name,'sign':(value>0)-(value<0),'file':name+'.bin.gz','bit_length':abs(value).bit_length(),'raw_bytes':len(raw),'raw_sha256':hashlib.sha256(raw).hexdigest(),'gzip_sha256':hashlib.sha256(compressed).hexdigest()})
    (out/'BINDING.json').write_text(json.dumps({'format':'signed magnitude, little-endian, gzip','files':rows},indent=2)+'\n')
    print(json.dumps({'fixed_leaves':len(rows),'raw_bytes':sum(x['raw_bytes'] for x in rows),'gzip_bytes':sum((out/x['file']).stat().st_size for x in rows)},indent=2))
if __name__=='__main__':main()
