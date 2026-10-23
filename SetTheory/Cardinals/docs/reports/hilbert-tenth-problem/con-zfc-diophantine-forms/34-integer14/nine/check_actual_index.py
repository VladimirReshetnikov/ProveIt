"""Read-only checks of the actual tuple, bounded index, and fixed-circuit residues."""
from pathlib import Path
import json,hashlib,gzip
from check_signed_nine import fixed_values,direct_digit
from circuit_support import evaluate
HERE=Path(__file__).resolve().parent

def actual_fixed(co,ports,p):
 z=pow(2,co['index_exponent'],p);f=fixed_values(co,ports,z,0,p)
 f['y_index']=direct_digit(co,2*z%p,f,p)
 return f

def main():
 co=json.loads((HERE/'INDEX_CONSTANTS.json').read_text());binding=HERE/co['port_binding'];ba=json.loads(binding.read_text());ports=[]
 for name in ['beta','K','MC','MF_source']:
  r=ba['payloads'][name];raw=(binding.parent/(name+'.bin')).read_bytes()
  assert hashlib.sha256(raw).hexdigest()==r['sha256'] and len(raw)==r['bytes']
  n=int.from_bytes(raw,'little');assert n.bit_length()==r['bits'];ports.append(n)
  assert gzip.decompress((binding.parent/(name+'.bin.gz')).read_bytes())==raw
 assert [n.bit_length() for n in ports]==co['actual_port_bit_lengths']
 z=1<<co['index_exponent'];raw=(HERE/'z_index.bin').read_bytes();assert int.from_bytes(raw,'little')==z and len(raw)==co['index_exponent']//8+1
 assert gzip.decompress((HERE/'z_index.bin.gz').read_bytes())==raw
 cert=json.loads((HERE/'INDEX_BOUND.json').read_text())
 payload_manifest=json.loads((HERE/'FIXED_LEAF_PAYLOADS.json').read_text())
 payloads={r['name']:r for r in payload_manifest['records']}
 exact_cache={};powers={(j,e):v**e for j,v in enumerate(ports) for e in range(5)}
 checked_payloads=0
 for row,br in zip(co['coefficient_records'],cert['records']):
  assert row['name']==br['name']
  recipe=row['coefficient_polynomial_in_fixed_ports'];sig=json.dumps(recipe,sort_keys=True)
  if sig not in exact_cache:exact_cache[sig]=sum(t['coefficient']*__import__('math').prod(powers[j,e] for j,e in enumerate(t['powers'])) for t in recipe)
  exact=exact_cache[sig]
  if row['name'] in payloads:
   record=payloads[row['name']];gz=(HERE/record['path']).read_bytes();mag=gzip.decompress(gz)
   assert hashlib.sha256(gz).hexdigest()==record['gzip_sha256'] and hashlib.sha256(mag).hexdigest()==record['raw_sha256']
   assert int.from_bytes(mag,'little')*(-1 if record['negative'] else 1)==exact
   checked_payloads+=1
  bound=sum(t['multiplier']<<t['exponent'] for t in br['absolute_bound_terms'])
  assert abs(exact)<=bound and bound+1<z
 out=[];body=json.loads((HERE/'nine31_signed_quadratic.json').read_text())
 for p in [101,1009,65537,1000000007]:
  fixed=actual_fixed(co,ports,p)
  for vs in [[0]*9,[1]*9,list(range(9)),[8,3,0,5,1,0,4,2,9]]:
   v=dict(zip(['epsilon','g0','h0','s0','w0','phi','i0','j0','n'],vs));values=evaluate(body,fixed,v,p)
   out.append({'prime':p,'inputs':vs,'output':values[body['output']]})
 result={'status':'PASS','coefficient_binding':co['port_binding'],'binding_sha256':hashlib.sha256(binding.read_bytes()).hexdigest(),'exact_actual_coefficient_checks':len(co['coefficient_records']),'exact_materialized_fixed_leaf_checks':checked_payloads,'index_exponent':co['index_exponent'],'raw_z_sha256':hashlib.sha256(raw).hexdigest(),'outputs':out}
 (HERE/'ACTUAL_INDEX_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='outputs'},indent=2))
if __name__=='__main__':main()
