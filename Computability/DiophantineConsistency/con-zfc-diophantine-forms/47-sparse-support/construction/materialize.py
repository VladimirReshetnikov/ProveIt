#!/usr/bin/env python3
"""Materialize every fixed coefficient from the complete pinned compiler tuple."""
import json, gzip, hashlib
from pathlib import Path
from canonical_gzip import canonical_gzip
ROOT=Path(__file__).resolve().parent

def sha(b): return hashlib.sha256(b).hexdigest()
def main():
    dag=json.loads((ROOT/'generated/sparse220_nine_positive.json').read_text())
    ports=[]; source=[]
    for name,fn in zip(['beta','K0','MC','MF'],['beta','K','MC','MF_source']):
        path=ROOT/'coefficients'/(fn+'.bin.gz'); encoded=path.read_bytes();raw=gzip.decompress(encoded)
        n=int.from_bytes(raw,'little');ports.append(n)
        source.append(dict(name=name,file=str(path.relative_to(ROOT)),bit_length=n.bit_length(),raw_bytes=len(raw),raw_sha256=sha(raw),gzip_sha256=sha(encoded)))
    if [x.bit_length() for x in ports] != dag['port_bit_lengths']:raise ValueError('wrong compiler tuple')
    live={x['name'] for x in dag['nodes'] if x['kind']=='fixed'}
    recipes={r['name']:r['terms'] for r in dag['coefficient_recipes']}
    out=ROOT/'coefficients/fixed';out.mkdir(exist_ok=True);payloads=[]
    for name in sorted(live):
        if name=='base_scale':
            x=1<<dag['base_floor_exponent'];recipe={'power_of_two':dag['base_floor_exponent']}
        else:
            recipe=recipes[name];x=0
            for t in recipe:
                y=t['coefficient']
                for p,e in zip(ports,t['powers']):y*=p**e
                x+=y
        raw=bytes([int(x<0)])+abs(x).to_bytes(max(1,(abs(x).bit_length()+7)//8),'little')
        encoded=canonical_gzip(raw);path=out/(name+'.bin.gz');path.write_bytes(encoded)
        payloads.append(dict(name=name,file=str(path.relative_to(ROOT)),magnitude_bit_length=abs(x).bit_length(),raw_bytes=len(raw),gzip_bytes=len(encoded),raw_sha256=sha(raw),gzip_sha256=sha(encoded),recipe=recipe))
    result=dict(source_pin='124c07c0b77a9e20e84676514d8b1ff78536ea3f',parent_source_sha256=sha((ROOT/'parent_system.json').read_bytes()),four_ports=source,live_fixed_coefficients=payloads,encoding='gzip; one sign byte (0 nonnegative, 1 negative), then minimal unsigned little-endian magnitude',base_scale_exponent=dag['base_floor_exponent'],coefficient_bound_exponent=dag['coefficient_bound_power_of_two'])
    (ROOT/'fixed_coefficients.json').write_text(json.dumps(result,indent=2)+'\n')
    print('Materialized',len(payloads),'fixed leaves;',sum(x['gzip_bytes'] for x in payloads),'compressed bytes')

if __name__=='__main__':main()
