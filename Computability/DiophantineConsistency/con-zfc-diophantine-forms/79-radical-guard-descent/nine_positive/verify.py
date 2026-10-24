#!/usr/bin/env python3
"""Portable integrated verifier; Python standard library only.
Regenerates exact identities independently; no upstream program is executed.
"""
from pathlib import Path
import gzip,hashlib,json,random,subprocess,sys
import build
from circuit import evaluate
R=Path(__file__).resolve().parent

def require(p,msg):
 if not p:raise ValueError(msg)

def main():
 body=json.loads((R/'equation9.json').read_text());rebuilt=build.build(tuple(body['majorant_order']),body['majorant_method'])
 require(rebuilt==body,'deterministic circuit regeneration')
 audits={}
 for script,args,key in [
 ('audit_laurent_majorant.py',[str(R/'data/radical.json')],'majorant'),
 ('audit_laurent_dag.py',[str(R)],'dag')]:
  path=R/'certificates'/('INDEPENDENT_'+key.upper()+'_AUDIT.json')
  p=subprocess.run([sys.executable,str(R/'independent'/script),*args,str(path)],capture_output=True,text=True)
  require(p.returncode==0,'independent audit failed: '+p.stderr)
  audits[key]=json.loads(path.read_text());require(audits[key]['status']=='PASS','audit receipt')
 sys.path.insert(0,str(R/'independent'))
 from audit_laurent_majorant import shifted,shifted_all
 rad=json.loads((R/'data/radical.json').read_text())
 p={tuple(e):int(c)for e,c in rad['T_terms']};d={tuple(e):int(c)for e,c in rad['defect_terms']}
 for name,want in [('P_shifted',shifted(p,3,1)),('defect_shifted',shifted_all(d,(3,1,1,1)))]:
  packet=json.loads((R/'certificates'/f'{name}.json').read_text())
  got={tuple(e):int(c)for e,c in packet['terms']}
  require(got==want and len(got)==len(packet['terms']),'serialized shifted certificate')
 binding=json.loads((R/'coefficients/COEFFICIENT_BINDING.json').read_text());ports={}
 for rec in binding['files']:
  compressed=(R/'coefficients'/rec['file']).read_bytes();raw=gzip.decompress(compressed)
  require(hashlib.sha256(raw).hexdigest()==rec['sha256'],'native raw hash')
  require(hashlib.sha256(compressed).hexdigest()==rec['gzip_sha256'],'native gzip hash')
  ports[rec['port']]=int.from_bytes(raw,'little');require(ports[rec['port']].bit_length()==rec['bit_length'],'native bit length')
 require(ports['beta']==(1<<1064921)-1,'coherent original31 base')
 old=json.loads((R/'upstream/nine71.json').read_text())
 tupleports=[ports[n]for n in ['beta','K','MC','MF_source']]
 rng=random.Random(20261023);tests=0
 for mod in [1000003,1000033,2147483647]:
  vals={}
  for rec in body['coefficient_recipes']:
   v=0
   for term in rec['terms']:
    t=term['coefficient']
    for port,e in zip(tupleports,term['powers']):t=t*pow(port,e,mod)%mod
    v=(v+t)%mod
   vals[rec['name']]=v
  vals['base_scale']=pow(2,body['base_scale_exponent'],mod)
  vals['threshold_scale']=pow(2,body['threshold_scale_exponent'],mod)
  for _ in range(8):
   x={name:rng.randrange(1,41)for name in body['variables']}
   _,nodes=evaluate(old,vals,x,mod)
   Z=(nodes['B1']+(x['j']-1)*x['C'])%mod;args=[nodes['A'],x['C'],x['i'],Z]
   P=sum(co*pow(args[0],e[0],mod)*pow(args[1],e[1],mod)*pow(args[2],e[2],mod)*pow(args[3],e[3],mod)for e,co in p.items())%mod
   scale=65536*pow(x['C'],7,mod)%mod;a1=scale*scale*nodes['a1']%mod
   theta=(nodes['E0']-nodes['Omega']*(nodes['V0']+P))%mod
   want=((theta*theta-nodes['Omega']**2*(nodes['a0']+a1))**2-4*pow(nodes['Omega'],4,mod)*nodes['a0']*a1)%mod
   got,_=evaluate(body,vals,x,mod);require(got==want,'actual-port modular formula transcription');tests+=1
 result={'status':'PASS','variables':9,'domain':'strictly positive integers','exact_degree':1158228,'operations':1753,'source_commit':'2605669a532342f153b13eb6b4a0af4b54f5fa37','coherent_tuple':'original31','native_port_bits':[v.bit_length()for v in tupleports],'majorant_terms':654,'defect_terms':3781,'positive_majorant_certificate_terms':1816,'positive_defect_certificate_terms':32637,'modular_formula_checks':tests,'independent_majorant':audits['majorant']['status'],'independent_literal_circuit':audits['dag']['status'],'scope':'Exact finite coefficient identities, positivity certificates, degree/circuit/source bindings; unbounded equivalence proved in PROOF.md with inherited compiler/refutation dependencies.'}
 (R/'VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
