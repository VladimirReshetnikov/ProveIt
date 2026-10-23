#!/usr/bin/env python3
"""Exact fixed-port/leaf audit. No upstream code is imported or executed."""
from check_complete_equations import ROOT,PORTS,load,req,evaluate
import gzip,hashlib,json,math,random

def exact(ts):
 return sum(t['coefficient']*math.prod(PORTS[k]**e for k,e in zip(PORTS,t['powers'])) for t in ts)
def main():
 instance=load('sun/MULTITARGET_INSTANCE.json'); report={}
 for key,meta in instance['fixed_port_tuple'].items():
  raw=gzip.decompress((ROOT/'sun'/meta['path']).read_bytes())
  req(hashlib.sha256(raw).hexdigest()==meta['raw_sha256'],'port hash '+key)
  req(int.from_bytes(raw,'little')==PORTS[key],'port binding '+key)
 req(hashlib.sha256((ROOT/'sun'/instance['parent']).read_bytes()).hexdigest()==instance['parent_raw_sha256'],'parent hash')
 records=load('sun/generated/quadratic_coefficients.json')['records']; vals=[exact(r['coefficient_polynomial_in_fixed_ports']) for r in records]
 circuit=load('sun/generated/multitarget_sun10.json'); weights=circuit['weights']; W=max(weights)
 for r in records:
  alpha=r['alpha']; position=circuit['targets'].index(r['target'])
  req(1+position*(2*W+1)+(2-sum(alpha))*W+sum(e*(W-w) for e,w in zip(alpha,weights))==r['exponent'],'homogeneous/Horner exact monomial exponent')
 req(max(abs(x).bit_length() for x in vals)<=2140018,'Sun bound')
 named={r['name']:v for r,v in zip(records,vals) if r['name']}; named['beta_sun']=2**load('sun/generated/multitarget_sun10.json')['beta_sun_exponent']
 req(named['beta_sun']>4*max(abs(v) for v in vals)*32**2,'exact Sun radix bound')
 req(load('sun/generated/multitarget_sun10.json')['beta_sun_exponent']%2==0,'even radix exponent')
 for k,meta in instance['fixed_leaves'].items():
  raw=gzip.decompress((ROOT/'sun'/meta['path']).read_bytes())
  req(hashlib.sha256(raw).hexdigest()==meta['raw_sha256'],'leaf hash '+k)
  req((-1 if raw[0] else 1)*int.from_bytes(raw[1:],'little')==named[k],'exact fixed leaf '+k)
 report['sun']={'coefficient_records':len(vals),'maximum_absolute_bit_length':max(abs(x).bit_length() for x in vals),'materialized_leaves':len(named),'all_exact_bindings':'pass'}
 d=load('nine/generated/multitarget_nine_positive.json'); nr=[exact(r['terms']) for r in d['coefficient_recipes']]
 req(max(abs(x).bit_length() for x in nr)<=2134927,'Nine bound')
 dn=load('nine/generated/multitarget_nine_natural.json');rng=random.Random(53)
 for p in [101,1009,1000003]:
  fix={r['name']:v%p for r,v in zip(d['coefficient_recipes'],nr)};fix['base_floor']=pow(2,d['base_floor_exponent'],p)
  for _ in range(20):
   x={v:rng.randrange(p) for v in d['variables']}; xp={v:a+1 for v,a in x.items()}
   req(evaluate(d,xp,fix,p)[0]==evaluate(dn,x,fix,p)[0],'positive/natural translation')
 report['nine']={'coefficient_records':len(nr),'maximum_absolute_bit_length':max(abs(x).bit_length() for x in nr),'domain_translation_cases':60,'bound':'pass'}
 print(json.dumps(report,indent=2))
if __name__=='__main__':main()
