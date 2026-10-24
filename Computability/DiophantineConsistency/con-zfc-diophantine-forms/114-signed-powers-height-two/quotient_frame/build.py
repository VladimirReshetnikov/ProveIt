#!/usr/bin/env python3
"""Build the signed-frame range-quotient deletion, over unrestricted integers."""
import json,sys
from copy import deepcopy
from hashlib import sha256
from pathlib import Path
import importlib.util

HERE=Path(__file__).resolve().parent
S=HERE/'source'
CHECK='--check' in sys.argv
REMOVED=[548,575,584,592,600,609,618,627,636]
SIGNED=[546,573,583,591,599,607,617,625,635]
def load(p):return json.loads(p.read_bytes())
def dump(p,x):
 data=(json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
 if CHECK:
  if p.read_bytes()!=data:raise ValueError('deterministic rebuild mismatch: '+str(p))
 else:
  p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
def module(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def build_parent():
 for rel,info in load(HERE/'SOURCE_PINS.json')['files'].items():
  if sha256((HERE/rel).read_bytes()).hexdigest()!=info['sha256']:raise ValueError('frozen input: '+rel)
 old=load(S/'parent75.json');domain=load(S/'domain75.json');sgn=load(S/'sign_certificate.json')
 n=domain['baseline_body_variables'];nr=domain['baseline_body_rows']
 if (n,nr)!=(1259,1177):raise ValueError('source dimensions')
 eq=dict(schema='quadratic_sum_squares_v1',domain='unrestricted integers',variant='quotient_frame_66_guards',variables=deepcopy(old['variables'][:n]),residuals=deepcopy(old['residuals'][:nr]))
 terms=[[-5,[]],[1,[643]]]+[[-1,[v]] for v in sgn['frame_arguments'] if v not in SIGNED]+[[-1,[v,v]] for v in REMOVED]
 eq['residuals'][1176]={'label':'signed.frame_definition','terms':terms}
 guards=[]
 for g in domain['guards']:
  pred=g['predicate']
  if pred['kind']=='retained_scalar' and pred['raw_variables'][0] in REMOVED:continue
  a,b,c=range(len(eq['variables']),len(eq['variables'])+3)
  idx=len(guards)
  eq['variables'].extend({'kind':'nonnegative_guard','name':f'signed_frame_guard.{idx}.{s}'} for s in ['a','b','c'])
  eq['residuals'].append({'label':f'signed_frame_guard.{idx}','terms':deepcopy(pred['terms'])+[[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]})
  guards.append({'predicate':pred,'auxiliary':[a,b,c]})
 if len(guards)!=66:raise ValueError('guard census')
 return eq,{'baseline_body_variables':n,'baseline_body_rows':nr,'guards':guards,'removed_quotient_guards':REMOVED,'signed_power_outputs':SIGNED,'old_frame_arguments':sgn['frame_arguments'],'changed_original_rows':[1176],'square_frame_coordinates':REMOVED,'constant_frame_offset':5}

def main():
 eq,domain=build_parent();dump(HERE/'parent.json',eq);dump(HERE/'domain.json',domain)
 engine=module('engine',S/'terminal_elimination.py')
 configs=[('support8',8,None),('support16_affine2',16,2)]
 census={}
 for label,cap,affine in configs:
  out,cert,metrics=engine.optimize(eq,max_support=cap,affine_support=affine)
  if cert['unconstrained_removed']:raise ValueError('unconstrained variables')
  engine.verify(eq,out,cert)
  dump(HERE/label/'equation.json',out);dump(HERE/label/'projection.json',cert);dump(HERE/label/'polynomial.json',engine.expand(out))
  census[label]=out['metrics'];print(label,census[label],flush=True)
 dump(HERE/'CENSUS.json',census)

if __name__=='__main__':main()
