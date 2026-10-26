#!/usr/bin/env python3
"""Rebuild selected literal projections and complete coefficient arrays offline."""
import argparse,hashlib,json,tempfile
from pathlib import Path
import joint_pell as J
from polynomial_kernel import raw,poly,ser,add,mul,degree
ROOT=Path(__file__).resolve().parent
PROFILES=[('integer138_degree8','source/pell209_affine.json',True),('integer114_degree16','seeds/plain_22/equation.json',True),('integer113_degree16','seeds/joint_13_frame/equation.json',True),('control114_degree16','seeds/plain_13/equation.json',False)]
def put(p,x):p.parent.mkdir(exist_ok=True,parents=True);p.write_bytes(raw(x))
def need(b,msg):
 if not b:raise ValueError(msg)
def substitute(p,v,f):
 out={};powers={0:{():1}}
 for m,c in p.items():
  exponent=m.count(v)
  while exponent not in powers:powers[len(powers)]=mul(powers[len(powers)-1],f)
  base=tuple(i for i in m if i!=v);term={tuple(sorted(base+t)):c*a for t,a in powers[exponent].items()};out=add(out,term)
 return out

def project(source,certificate):
 rows={i:poly(r['terms'])for i,r in enumerate(source['residuals'])};active=set(range(len(source['variables'])));ledger=[];maxdegree=0
 for step in certificate['steps']:
  v,r=step['variable'],step['deleted_row'];need(v in active and r in rows,'live pivot');p=rows[r];epsilon=p.get((v,),0);need(epsilon in[-1,1]and all(v not in m or m==(v,)for m in p),'monic pivot');f={m:-epsilon*c for m,c in p.items()if m!=(v,)};need(ser(f)==step['definition'],'literal pivot definition');ledger.append({'ordinal':len(ledger),'variable':v,'row':r,'unit_coefficient':epsilon,'definition':step['definition']});del rows[r]
  rows={j:substitute(p,v,f)for j,p in rows.items()};active.remove(v);maxdegree=max(maxdegree,max(degree(p)for p in rows.values()))
 keep=sorted(active);need(keep==certificate['retained_original_indices']and sorted(rows)==certificate['retained_row_indices'],'retained maps');rename={v:i for i,v in enumerate(keep)};d=2*max(degree(p)for p in rows.values())
 eq={'schema':'conzfc-degree-bounded-elimination-v1','domain':'unrestricted integers','polynomial':'sum(square(row) for row in residuals)','variant':f'polynomial_projection_{len(keep)}_degree{d}','variables':[source['variables'][v]for v in keep],'residuals':[{'label':source['residuals'][r]['label'],'terms':ser({tuple(rename[i]for i in m):c for m,c in p.items()})}for r,p in sorted(rows.items())]}
 return eq,ledger,maxdegree

def run(out):
 source=ROOT/'source/pell209_affine.json';binding=json.loads((ROOT/'SOURCE_BINDING.json').read_text());need(hashlib.sha256(source.read_bytes()).hexdigest()==binding['sha256'],'exact affine209 source');J.SOURCE=source
 for name,partition,fuse,shift in [('joint_13_frame',((0,),(1,2,3)),0,1),('plain_13',((0,),(1,2,3)),None,0),('plain_22',((0,1),(2,3)),None,0)]:
  eq,cert=J.build(partition,fuse,shift);put(out/'seeds'/name/'equation.json',eq);put(out/'seeds'/name/'certificate.json',cert)
 for name,src,deliver in PROFILES:
  sp=source if src.startswith('source/')else out/src;srcdata=json.loads(sp.read_text());certificate=json.loads((ROOT/'equations'/name/'certificate.json').read_text());need(hashlib.sha256(sp.read_bytes()).hexdigest()==certificate['source_sha256'],'projection source');eq,ledger,maxdegree=project(srcdata,certificate);dest=out/'equations'/name;put(dest/'equation.json',eq)
  # Independently collect from the producer-side convolution; verify_monic uses
  # a separate triangular square implementation and imports neither producer.
  p={}
  for row in eq['residuals']:
   z=poly(row['terms']);p=add(p,mul(z,z))
  metrics={'variables':len(eq['variables']),'residuals':len(eq['residuals']),'degree':degree(p),'collected_terms':len(p),'coefficient_height':max(map(abs,p.values())),'residual_terms':sum(len(r['terms'])for r in eq['residuals']),'maximum_residual_degree':max(len(m)for r in eq['residuals']for c,m in r['terms']),'maximum_intermediate_residual_degree':maxdegree,'deleted_unit_definitions':len(ledger),'all_coordinates_used':set(i for m in p for i in m)==set(range(len(eq['variables'])))};put(dest/'metrics.json',metrics)
  if deliver:
   ts=ser(p)
   if name=='integer113_degree16':
    chunks=[]
    for start in range(0,len(ts),300000):
     part=ts[start:start+300000];rel=f'expanded/part{len(chunks):03d}.json';put(dest/rel,{'schema':'sparse-polynomial-chunk-v1','terms':part});chunks.append({'path':rel,'terms':len(part),'sha256':hashlib.sha256((dest/rel).read_bytes()).hexdigest(),'first_monomial':part[0][1],'last_monomial':part[-1][1]})
    put(dest/'expanded_polynomial.json',{'schema':'chunked-sparse-polynomial-v1','variables':len(eq['variables']),'total_terms':len(ts),'ordering':'strict lexicographic ascending monomial tuple','chunks':chunks})
   else:put(dest/'expanded_polynomial.json',{'schema':'sparse-polynomial-v1','variables':len(eq['variables']),'terms':ts})
  native={'schema':'literal-unit-substitution-ledger-v1','domain':'unrestricted integers','source_sha256':certificate['source_sha256'],'source_coordinates':len(srcdata['variables']),'source_rows':len(srcdata['residuals']),'step_semantics':'Start from all source rows. At each literal step delete the recorded row and substitute the recorded integer polynomial for its recorded coordinate everywhere else. The printed unit coefficient is the pivot coefficient before that substitution. No coefficient search is implicit.','steps':ledger,'retained_original_indices':certificate['retained_original_indices'],'retained_row_indices':certificate['retained_row_indices'],'equation':'sum(square(final substituted source row) for the retained rows)=0','metrics':metrics};put(dest/'NATIVE_DEFINITION.json',native)
 return [p for p in out.rglob('*.json')]
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);ap.add_argument('--check',action='store_true');a=ap.parse_args()
 if a.check:
  with tempfile.TemporaryDirectory(prefix='reciprocal23-rebuild-')as td:
   out=Path(td);paths=run(out)
   for p in paths:need(p.read_bytes()==(ROOT/p.relative_to(out)).read_bytes(),'byte reconstruction '+str(p.relative_to(out)))
   print(json.dumps({'status':'PASS','byte_reconstructed_files':len(paths),'profiles':[p[0]for p in PROFILES]}))
 else:
  need(a.output is not None,'--output or --check required');run(a.output)
