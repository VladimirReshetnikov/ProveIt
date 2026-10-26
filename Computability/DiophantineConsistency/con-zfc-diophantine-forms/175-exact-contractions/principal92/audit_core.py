#!/usr/bin/env python3
"""Independent checker of finite acyclic ordinary-polynomial projections.

Does not import the discovery program. Nonzero leading residues are rigorous
integer nonvanishing witnesses, not probabilistic acceptance criteria.
"""
from pathlib import Path
import argparse,copy,hashlib,json,random

MOD=1000003
def req(ok,msg):
 if not ok:raise ValueError(msg)
def terms(ts,n):
 p={}
 for c,mon in ts:
  req(type(c)is int and c!=0,'coefficient');req(type(mon)is list,'monomial')
  req(all(type(v)is int and 0<=v<n for v in mon),'coordinate')
  m=tuple(mon);req(m==tuple(sorted(m)) and m not in p,'canonical terms');p[m]=c
 return p
def check(source,cert,source_bytes,*,need_witness=True):
 req(hashlib.sha256(source_bytes).hexdigest()==cert['source_sha256'],'source checksum')
 n=len(source['variables']);rr=[terms(r['terms'],n) for r in source['residuals']];defs={};deleted=set()
 for step in cert['steps']:
  i,v,a=step['row'],step['variable'],step['coefficient']
  req(type(i)is int and 0<=i<len(rr) and i not in deleted,'distinct source row')
  req(type(v)is int and 0<=v<n and v not in defs,'distinct source coordinate')
  req(a in (-1,1) and rr[i].get((v,))==a,'unit pivot')
  req(all(v not in mon for mon in rr[i] if mon!=(v,)),'raw pivot occurs elsewhere')
  f=terms(step['restoration_source_terms'],n)
  req(f=={mon:-a*c for mon,c in rr[i].items() if mon!=(v,)},'restoration identity')
  # At this step earlier eliminated symbols are abbreviations. The following
  # exact recursive support check rules out any hidden occurrence of v.
  def contains(u,seen):
   if u==v:return True
   if u in seen:return False
   seen.add(u)
   return any(contains(w,seen) for mon in defs.get(u,{}) for w in mon)
  req(not any(contains(u,set()) for mon in f for u in mon),'cyclic monic restoration')
  defs[v]=f;deleted.add(i)
 free=[i for i in range(n) if i not in defs];ret=[i for i in range(len(rr)) if i not in deleted]
 req(cert['free_source_variables']==free and cert['retained_source_rows']==ret,'projection domain')
 req(cert['variables_remaining']==len(free) and cert['residuals_remaining']==len(ret),'counts')
 memo={};gray=set()
 def vd(v):
  if v in memo:return memo[v]
  if v not in defs:return 1
  req(v not in gray,'cycle');gray.add(v)
  out=max((sum(vd(w) for w in mon) for mon in defs[v]),default=0)
  gray.remove(v);memo[v]=out;return out
 degrees={i:max((sum(vd(v) for v in mon) for mon in rr[i]),default=0) for i in ret};degree=max(degrees.values())
 req(degree==cert['residual_degree_upper_bound'] and cert['polynomial_degree_upper_bound']==2*degree,'degree upper bound')
 req([[i,degrees[i]] for i in ret]==cert['retained_row_degree_bounds'],'row degrees')
 def leading(ray):
  vals=dict(zip(free,ray))
  def lc(v):
   if v in vals:return vals[v]
   total=0
   for mon,c in defs[v].items():
    if sum(vd(u) for u in mon)!=vd(v):continue
    for u in mon:c=c*lc(u)%MOD
    total=(total+c)%MOD
   vals[v]=total;return total
  out={}
  for i in ret:
   if degrees[i]!=degree:continue
   total=0
   for mon,c in rr[i].items():
    if sum(vd(u) for u in mon)!=degree:continue
    for u in mon:c=c*lc(u)%MOD
    total=(total+c)%MOD
   out[i]=total
  return out
 witness=None
 for seed in range(32):
  rng=random.Random(seed);ray=[1]*len(free) if seed==0 else [rng.randrange(1,101) for _ in free]
  values=leading(ray);nz=next(((i,c) for i,c in values.items() if c),None)
  if nz:
   witness={'modulus':MOD,'source_row':nz[0],'leading_coefficient_modulus':nz[1],'free_coordinate_ray':ray};break
 if need_witness:req(witness is not None,'no nonzero leading witness; only upper bound established')
 return {'variables':len(free),'residuals':len(ret),'exact_degree':2*degree if witness else None,'degree_upper_bound':2*degree,'unit_projections':len(defs),'leading_witness':witness,'integer_zero_set_bijection_checked':True}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('certificate',type=Path);ap.add_argument('--source',type=Path);ap.add_argument('--out',type=Path);args=ap.parse_args();cert=json.loads(args.certificate.read_text());sp=args.source or Path(cert['source']);raw=sp.read_bytes();source=json.loads(raw);report=check(source,cert,raw)
 cases=[]
 for name,change in [('wrong_restoration',lambda c:c['steps'][0]['restoration_source_terms'][0].__setitem__(0,2*c['steps'][0]['restoration_source_terms'][0][0])),('missing_residual',lambda c:c['retained_source_rows'].pop()),('wrong_unit',lambda c:c['steps'][0].__setitem__('coefficient',2))]:
  c=copy.deepcopy(cert);change(c)
  try:check(source,c,raw)
  except ValueError:cases.append(name)
  else:raise ValueError('corruption accepted: '+name)
 report['negative_controls_rejected']=cases
 if args.out:args.out.write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:v for k,v in report.items() if k!='leading_witness'},sort_keys=True))
 if report['leading_witness']:print(json.dumps({'leading_row':report['leading_witness']['source_row'],'residue':report['leading_witness']['leading_coefficient_modulus'],'ray_length':len(report['leading_witness']['free_coordinate_ray'])}))
if __name__=='__main__':main()
