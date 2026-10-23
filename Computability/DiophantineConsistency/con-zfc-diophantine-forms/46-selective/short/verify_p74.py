#!/usr/bin/env python3
"""Finite gate and exact-degree audit for the 74-operation local equation."""
import gzip, hashlib, json
from pathlib import Path
from collections import Counter
ROOT=Path(__file__).resolve().parent
def require(x,msg):
 if not x:raise ValueError(msg)
def main():
 obj=json.loads((ROOT/'p74_norm_minima.json').read_text());base=json.loads((ROOT/'upstream_p75.json').read_text())
 receipt=json.loads((ROOT/'SOURCES.json').read_text())
 require(receipt['pinned_commit']=='124c07c0b77a9e20e84676514d8b1ff78536ea3f','wrong source snapshot')
 for entry in receipt['sources']:
  raw=(ROOT/entry['local_file']).read_bytes()
  require(len(raw)==entry['bytes'],'source byte length')
  require(hashlib.sha256(raw).hexdigest()==entry['sha256'],'source SHA256')
  blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
  require(blob==entry['git_blob_sha1'],'pinned source Git blob SHA1')
 binding_path=ROOT/obj['coefficient_binding']['file']
 binding=json.loads(binding_path.read_text());actual={};payload_records=[]
 require(binding['instance']==receipt['coefficient_instance'],'coefficient instance mismatch')
 for entry in binding['materialization']['files']:
  packed=(binding_path.parent/entry['file']).read_bytes();raw=gzip.decompress(packed)
  require(len(packed)==entry['gzip_bytes'] and len(raw)==entry['raw_bytes'],'payload lengths')
  require(hashlib.sha256(packed).hexdigest()==entry['gzip_sha256'],'compressed payload SHA256')
  require(hashlib.sha256(raw).hexdigest()==entry['sha256'],'raw payload SHA256')
  value=int.from_bytes(raw,'little');require(value.bit_length()==entry['bits'],'port bit length')
  actual[entry['port']]=value
  payload_records.append({'port':entry['port'],'bits':entry['bits'],'raw_sha256':entry['sha256'],'gzip_sha256':entry['gzip_sha256']})
 aliases=obj['coefficient_binding']['aliases']
 require(aliases==receipt['port_aliases'],'port aliases differ')
 ports={name:actual[alias] for name,alias in aliases.items()}
 require(ports['beta']>0 and ports['beta']==(1<<binding['d'])-1,'actual positive beta/base binding')
 require(0<ports['MC']<ports['beta'],'native low mask range')
 native_high=ports['MF']-ports['beta']
 require(0<native_high<ports['beta'],'shifted MF range')
 require(ports['MC']%4==2 and native_high%8==4,'native mask residues')
 require(ports['MC'].bit_count()+native_high.bit_count()==binding['d'],'complementary native masks')
 require(obj['source'][:62]==base['source'][:62],'producer source changed')
 require(len(obj['source'])==74,'wrong gate count')
 require(obj['witnesses']==base['witnesses'] and obj['fixed_numerals']==base['fixed_numerals'],'input change')
 deg={n:1 for n in obj['witnesses']};lead={n:1 for n in obj['witnesses']}
 prime=1000000007
 for n in obj['fixed_numerals']:deg[n]=0;lead[n]=ports[n]%prime
 def get(v):return (0,v) if isinstance(v,int) else (deg[v],lead[v])
 deps={};counts=Counter()
 for name,op,a,b in obj['source']:
  da,ca=get(a);db,cb=get(b)
  if op=='*':d,c=da+db,ca*cb
  else:
   d=max(da,db);aa=ca if da==d else 0;bb=cb if db==d else 0;c=aa+bb if op=='+' else aa-bb
  deg[name]=d;lead[name]=c%prime;deps[name]=[v for v in [a,b] if isinstance(v,str)];counts[op]+=1
 used=set();todo=[obj['output']]
 while todo:
  name=todo.pop()
  if name in used:continue
  used.add(name);todo.extend(deps.get(name,[]))
 require(all(n in used for n,_,_,_ in obj['source']),'unused gate')
 require(all(n in used for n in obj['witnesses']+obj['fixed_numerals']),'unused input')
 require(deg[obj['output']]==68,'wrong degree upper bound')
 expected=(2**8*pow(ports['beta'],40,prime))%prime
 require(expected!=0 and lead[obj['output']]==expected,'actual-tuple degree leader is zero or wrong')
 report={'status':'PASS','gates':74,'counts':dict(counts),'variables':15,'degree':68,
  'coefficient_instance':binding['instance'],'native_base_exponent':binding['d'],
  'pinned_source_files_verified':len(receipt['sources']),'actual_positive_beta_verified':True,
  'coherent_port_payloads':payload_records,
  'actual_tuple_degree_certificate':{'prime':prime,'beta_mod_prime':ports['beta']%prime,'nonzero_diagonal_coefficient_mod_prime':lead[obj['output']],'diagonal_leading_coefficient_formula':'2^8 * beta^40'},
  'uniform_leading_form':'i^4*w^4*s^12*(eta+zeta)^8*(beta*J)^40',
  'uniform_local_theorem':'For any fixed integer ports with beta>0, the new circuit has the complete positive zero set of the inherited P75; actual coefficients use the whole pinned package-36 tuple.',
  'proof_boundary':'Finite circuit audit; complete local zero-equivalence proof is RESULT.md. Native compiler semantics are inherited.'}
 (ROOT/'p74_audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
if __name__=='__main__':main()
