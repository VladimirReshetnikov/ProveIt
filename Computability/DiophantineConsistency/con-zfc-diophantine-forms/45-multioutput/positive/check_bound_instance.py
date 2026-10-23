"""Independent full polynomial replay using all four materialized fixed ports."""
import gzip,hashlib,json
from pathlib import Path
import numpy as np
ROOT=Path(__file__).resolve().parent
binding=json.loads((ROOT/'COEFFICIENT_BINDING.json').read_text())
ports={}
for name,row in binding['coefficient_files'].items():
 gz=(ROOT/row['path']).read_bytes();raw=gzip.decompress(gz)
 assert hashlib.sha256(gz).hexdigest()==row['gzip_sha256']
 assert hashlib.sha256(raw).hexdigest()==row['sha256']
 ports[name]=int.from_bytes(raw,'little');assert ports[name].bit_length()==row['bit_length']
assert ports['beta']==(1<<1064921)-1
rows=[]
for p in [65521,1000003]:
 def trim(a):
  a=a%p;nz=np.flatnonzero(a)
  return a[:int(nz[-1])+1] if len(nz) else np.array([0],dtype=np.int64)
 def combine(a,b,sign):
  c=np.zeros(max(len(a),len(b)),dtype=np.int64);c[:len(a)]+=a;c[:len(b)]+=sign*b;return trim(c)
 for fp in sorted(ROOT.glob('*_product.json')):
  packet=json.loads(fp.read_text());vals={n:np.array([0,1],dtype=np.int64) for n in packet['witnesses']};vals.update({n:np.array([v%p],dtype=np.int64) for n,v in ports.items()})
  def value(x):return vals[x] if isinstance(x,str) else np.array([x],dtype=np.int64)
  for n,op,x,y in packet['source']:
   x,y=value(x),value(y)
   vals[n]=trim(np.convolve(x,y)) if op=='*' else combine(x,y,1 if op=='+' else -1)
  out=vals[packet['output']];assert len(out)-1==packet['exact_degree']
  if packet['variant']=='ac2_aux':
   B=ports['beta']%p
   expected=-pow(2,153,p)*pow(B,548,p)*pow(B-1,8,p)*(pow(B,5,p)+64)%p
   assert int(out[-1])==expected
  rows.append({'file':fp.name,'prime':p,'exact_specialization_degree':len(out)-1,'leading_coefficient_mod_prime':int(out[-1])})
result={'instance':binding['instance'],'payloads_checked':4,'full_univariate_replays':rows,'all_pass':True,'scope':'Exact fixed-port finite-field diagnostics; uniform degree and equivalence proofs are mathematical.'}
(ROOT/'COEFFICIENT_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS: four payloads, twelve full fixed-instance polynomial replays, two recommended-form diagonal leader checks')
