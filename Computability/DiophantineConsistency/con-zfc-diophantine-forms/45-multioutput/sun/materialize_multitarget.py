#!/usr/bin/env python3
"""Materialize every nonliteral fixed leaf of the primary Sun10 circuit."""
from pathlib import Path
import json,gzip,hashlib
R=Path(__file__).resolve().parent
C=json.loads((R/'generated/multitarget_sun10.json').read_text());rr=json.loads((R/'generated/quadratic_coefficients.json').read_text())['records'];ports=[];portmanifest={}
for name,f in [('beta','beta.bin.gz'),('K0','K.bin.gz'),('MC','MC.bin.gz'),('MF','MF_source.bin.gz')]:
 p=R/'upstream/signed10/data'/f;raw=gzip.decompress(p.read_bytes());ports.append(int.from_bytes(raw,'little'));portmanifest[name]={'path':str(p.relative_to(R)),'raw_sha256':hashlib.sha256(raw).hexdigest(),'raw_bytes':len(raw)}
fixed={}
for r in rr:
 if r['name'] is None:continue
 value=0
 for t in r['coefficient_polynomial_in_fixed_ports']:
  v=t['coefficient']
  for x,e in zip(ports,t['powers']):v*=x**e
  value+=v
 if r['name'] in fixed:assert fixed[r['name']]==value
 fixed[r['name']]=value
fixed['beta_sun']=1<<C['beta_sun_exponent'];folder=R/'data/fixed';folder.mkdir(exist_ok=True)
leaves={}
for name,value in fixed.items():
 raw=bytes([int(value<0)])+abs(value).to_bytes(max(1,(abs(value).bit_length()+7)//8),'little');payload=gzip.compress(raw,mtime=0);p=folder/(name+'.bin.gz');p.write_bytes(payload)
 leaves[name]={'path':str(p.relative_to(R)),'encoding':'gzip of sign byte (0 positive/zero, 1 negative), then unsigned little-endian magnitude','raw_sha256':hashlib.sha256(raw).hexdigest(),'gzip_sha256':hashlib.sha256(payload).hexdigest(),'raw_bytes':len(raw),'compressed_bytes':len(payload),'absolute_bit_length':abs(value).bit_length()}
assert set(fixed)=={n['name'] for n in C['nodes'] if n['kind']=='fixed'}
instance={'name':'simultaneous22-B2-Sun10','source_pin':'22e75dd6b87b1b199bb08c778d7cf075ae5aae08','equation':'generated/multitarget_sun10.json','domain':'ten unrestricted integers','variables':C['variables'],'parent':'data/parent_system60.json','parent_raw_sha256':hashlib.sha256((R/'data/parent_system60.json').read_bytes()).hexdigest(),'parent_transport_convention':'z_old=z+1 as in package31 quartic31_system60, followed by all positive variables n+1','source_coefficient_recipes':'generated/quadratic_coefficients.json','fixed_port_tuple':portmanifest,'fixed_leaves':leaves,'source_proof':'MULTITARGET_SOURCE_PROOF.md','tail_proof':'upstream/SIGNED10_PROOF.md, Sections 4–8','certificate':'../quartic/B2_CERTIFICATE.json','exact_degree':C['degree_upper_bound'],'operations':C['total_operations'],'beta_sun_formula':'2^'+str(C['beta_sun_exponent']),'kernel_checked':False,'scope':'Mathematical equivalence to absence of a ZFC contradiction; neither consistency nor inconsistency is proved.'}
(R/'MULTITARGET_INSTANCE.json').write_text(json.dumps(instance,indent=2)+'\n');print(json.dumps({'fixed_leaves':len(leaves),'raw_bytes':sum(x['raw_bytes'] for x in leaves.values()),'compressed_bytes':sum(x['compressed_bytes'] for x in leaves.values())}))
