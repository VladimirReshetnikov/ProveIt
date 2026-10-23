"""Bound all quartic31 Jones coefficients using four complete-tuple bit lengths."""
from pathlib import Path
from collections import defaultdict
import hashlib,gzip,json
HERE=Path(__file__).resolve().parent
BITS=[1064921,1065043,1064921,1064922]
def main():
 co=json.loads((HERE/'quartic_coefficients.json').read_text());co.pop('previous_index_bound',None);rows=[];s=0
 for row in co['coefficient_records']:
  powers=defaultdict(int)
  for term in row['coefficient_polynomial_in_fixed_ports']:
   powers[sum(a*b for a,b in zip(term['powers'],BITS))]+=abs(term['coefficient'])
  bound=sum(v<<e for e,v in powers.items());k=(bound+1).bit_length()
  assert bound+1<1<<k
  s=max(s,k);rows.append({'name':row['name'],'bound_exponent':k,'absolute_bound_terms':[{'multiplier':v,'exponent':e} for e,v in sorted(powers.items())]})
 co.update(index_exponent=s,z_index=f'2^{s}',actual_port_bit_lengths=BITS,port_binding='../coefficients/payloads/COEFFICIENT_BINDING.json',index_bound_proof='Absolute coefficient bound plus1 strictly less than2^index_exponent; see INDEX_BOUND.json',nu_caution='nu31 is the parent-quartic unknown count and has no relation to the native radix exponent.')
 raw=(1<<s).to_bytes(s//8+1,'little');comp=gzip.compress(raw,mtime=0)
 (HERE/'z_index.bin').write_bytes(raw);(HERE/'z_index.bin.gz').write_bytes(comp)
 (HERE/'INDEX_CONSTANTS.json').write_text(json.dumps(co,separators=(',',':'))+'\n')
 cert={'status':'PASS','port_bit_lengths':BITS,'index_exponent':s,'nu':co['nu'],'L':co['L'],'records':rows,'materialization':{'raw_sha256':hashlib.sha256(raw).hexdigest(),'raw_bytes':len(raw),'gzip_sha256':hashlib.sha256(comp).hexdigest(),'gzip_bytes':len(comp)}}
 (HERE/'INDEX_BOUND.json').write_text(json.dumps(cert,indent=2)+'\n');print(json.dumps({k:v for k,v in cert.items() if k!='records'},indent=2))
if __name__=='__main__':main()
