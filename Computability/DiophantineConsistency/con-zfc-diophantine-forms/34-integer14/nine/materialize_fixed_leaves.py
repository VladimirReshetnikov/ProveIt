"""Materialize every distinct nonliteral weighted coefficient used by the circuit.
Files use gzip-compressed minimal unsigned little-endian magnitudes. Sign lives
in the manifest. No giant Jones y or floor coefficient is materialized.
"""
from pathlib import Path
from math import prod
import json,gzip,hashlib
HERE=Path(__file__).resolve().parent

def main():
 co=json.loads((HERE/'INDEX_CONSTANTS.json').read_text());binding=HERE/co['port_binding'];ba=json.loads(binding.read_text())
 ports=[]
 for n in ['beta','K','MC','MF_source']:
  raw=(binding.parent/(n+'.bin')).read_bytes();assert hashlib.sha256(raw).hexdigest()==ba['payloads'][n]['sha256'];ports.append(int.from_bytes(raw,'little'))
 recipes={r['name']:r['coefficient_polynomial_in_fixed_ports'] for r in co['coefficient_records']}
 body=json.loads((HERE/'nine31_signed_quadratic.json').read_text());names=sorted(n['name'] for n in body['nodes'] if n['kind']=='fixed' and n['name'] not in ['z_index','y_index'])
 out=HERE/'fixed_leaf_payloads';out.mkdir(exist_ok=True);records=[]
 for n in names:
  value=sum(t['coefficient']*prod(v**e for v,e in zip(ports,t['powers'])) for t in recipes[n]);mag=abs(value)
  raw=mag.to_bytes(max(1,(mag.bit_length()+7)//8),'little');gz=gzip.compress(raw,mtime=0);fn=n+'.magnitude.bin.gz';(out/fn).write_bytes(gz)
  assert int.from_bytes(gzip.decompress(gz),'little')*(-1 if value<0 else 1)==value
  records.append({'name':n,'negative':value<0,'bit_length':mag.bit_length(),'raw_bytes':len(raw),'raw_sha256':hashlib.sha256(raw).hexdigest(),'gzip_bytes':len(gz),'gzip_sha256':hashlib.sha256(gz).hexdigest(),'path':'fixed_leaf_payloads/'+fn})
 result={'status':'PASS','encoding':'gzip(minimal unsigned little-endian magnitude); separate negative flag','coefficient_binding':co['port_binding'],'index_constants_sha256':hashlib.sha256((HERE/'INDEX_CONSTANTS.json').read_bytes()).hexdigest(),'distinct_weighted_coefficients':len(records),'raw_bytes':sum(r['raw_bytes'] for r in records),'gzip_bytes':sum(r['gzip_bytes'] for r in records),'records':records,'not_materialized':'y_index remains explicit bounded recipe; z_index is separately materialized.'}
 (HERE/'FIXED_LEAF_PAYLOADS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='records'},indent=2))
if __name__=='__main__':main()
