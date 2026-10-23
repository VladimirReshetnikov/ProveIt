#!/usr/bin/env python3
"""Materialize every fixed coefficient for the ten-integer sparse equations."""
import json,gzip,hashlib
from pathlib import Path
from canonical_gzip import canonical_gzip
ROOT=Path(__file__).resolve().parent
def main():
    dag=json.loads((ROOT/'generated/sparse220_ten_integer.json').read_text());data=dag['coefficient_recipes']
    ports=[int.from_bytes(gzip.decompress((ROOT/'coefficients'/(n+'.bin.gz')).read_bytes()),'little') for n in ['beta','K','MC','MF_source']]
    live={x['name'] for x in dag['nodes'] if x['kind']=='fixed'};out=ROOT/'coefficients/fixed10';out.mkdir(exist_ok=True);rows=[]
    for name in sorted(live):
        if name=='beta_source':x=1<<data['beta_source_exponent'];recipe={'power_of_two':data['beta_source_exponent']}
        else:
            recipe=data['recipes'][name];x=0
            for t in recipe:
                y=t['coefficient']
                for p,e in zip(ports,t['powers']):y*=p**e
                x+=y
        raw=bytes([int(x<0)])+abs(x).to_bytes(max(1,(abs(x).bit_length()+7)//8),'little');enc=canonical_gzip(raw);fn=out/(name+'.bin.gz');fn.write_bytes(enc)
        rows.append(dict(name=name,file=str(fn.relative_to(ROOT)),recipe=recipe,raw_sha256=hashlib.sha256(raw).hexdigest(),gzip_sha256=hashlib.sha256(enc).hexdigest(),bit_length=abs(x).bit_length(),raw_bytes=len(raw),gzip_bytes=len(enc)))
    result=dict(source_pin='124c07c0b77a9e20e84676514d8b1ff78536ea3f',compiler_tuple_manifest='fixed_coefficients.json',live_fixed_coefficients=rows,encoding='gzip; sign byte then minimal unsigned little-endian magnitude')
    (ROOT/'fixed_coefficients10.json').write_text(json.dumps(result,indent=2)+'\n');print('Materialized',len(rows),'ten-integer leaves;',sum(r['gzip_bytes'] for r in rows),'compressed bytes')
if __name__=='__main__':main()
