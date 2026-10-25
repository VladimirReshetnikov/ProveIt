#!/usr/bin/env python3
"""Exact nonunit affine projections with surviving integral companion rows."""
from pathlib import Path
from fractions import Fraction
from collections import defaultdict
import hashlib, json, math

ROOT=Path(__file__).resolve().parent
OUT=ROOT
ORIGINAL_PATHS={
 'shared240_balanced':'conzfc_shared_factorial_error_20261025/equations/equation241_affine_balanced/equation.json',
 'shared240_lowheight':'conzfc_shared_factorial_error_20261025/equations/equation241_affine/equation.json',
 'factorialfree241':'ConZFC_Factorial_Free_Binomial_CRT_2026-10-25/direct/principal/equation.json',
}
PROFILES=[
 ('shared240_balanced',ROOT/'shared240_balanced/source_equation.json',88,39,23),
 ('shared240_lowheight',ROOT/'shared240_lowheight/source_equation.json',88,39,23),
 ('factorialfree241',ROOT/'factorialfree241/source_equation.json',88,67,52),
]

def need(q,msg):
 if not q: raise ValueError(msg)
def compact(p):return {m:c for m,c in p.items() if c}
def plus(out,p):
 for m,c in p.items():out[m]+=c

def times(f,g):
 out=defaultdict(Fraction)
 for m,c in f.items():
  for n,d in g.items():out[tuple(sorted(m+n))]+=c*d
 return compact(out)
def substitute(f,v,g):
 out=defaultdict(Fraction)
 for m,c in f.items():
  k=m.count(v);w=tuple(i for i in m if i!=v)
  part={w:c}
  for _ in range(k):part=times(part,g)
  plus(out,part)
 return compact(out)
def primitive(f):
 need(f,'unexpected identically-zero residual')
 den=math.lcm(*(c.denominator for c in f.values()))
 scaled={m:int(c*den) for m,c in f.items()}
 divisor=math.gcd(*scaled.values())
 return {m:c//divisor for m,c in scaled.items()},Fraction(den,divisor)
def terms(f):return [[int(c),list(m)] for m,c in sorted(f.items()) if c]
def write(p,obj):p.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
def degree(f):return max(map(len,f),default=0)

OUT.mkdir(exist_ok=True)
profiles=[]
for name,source,pivot_row,v,integrity_row in PROFILES:
 out=OUT/name;out.mkdir(exist_ok=True)
 raw=source.read_bytes()
 old=json.loads(raw); rows=[{tuple(m):Fraction(c) for c,m in r['terms']} for r in old['residuals']]
 pivot=rows[pivot_row];c=pivot[(v,)]
 need(abs(c)>1,'pivot must be nonunit')
 need(all(v not in m or m==(v,) for m in pivot),'pivot not linear in target')
 recovery={m:-a/c for m,a in pivot.items() if m!=(v,)}
 need(degree(recovery)<=1,'not affine recovery')
 integrity=rows[integrity_row]
 need(abs(integrity.get((v,),0))==1,'integrity row must be monic linear here')
 need(all(v not in m or m==(v,) for m in integrity),'integrity coefficient not constant')
 mapping=[i for i in range(len(old['variables'])) if i!=v]
 back={oldi:newi for newi,oldi in enumerate(mapping)}
 newrows=[]; certrows=[]; symbolic=[]
 for ri,row in enumerate(rows):
  if ri==pivot_row:continue
  replaced=substitute(row,v,recovery)
  p,mult=primitive(replaced)
  need(degree(p)<=2,'degree rose')
  ren={tuple(back[i] for i in m):c for m,c in p.items()}
  symbolic.append(ren)
  newrows.append({'label':'projected.'+str(ri).zfill(3),'source_row':ri,'terms':terms(ren)})
  certrows.append({'source_row':ri,'new_row':len(newrows)-1,'multiplier_numerator':mult.numerator,'multiplier_denominator':mult.denominator})
 new={'schema':'finite_quadratic_residuals_v1','domain':'unrestricted integers','polynomial':'sum(square(row) for row in residuals)','variant':name,'variables':[old['variables'][i] for i in mapping],'residuals':newrows}
 expanded=defaultdict(int)
 for row in symbolic:
  plus(expanded,times(row,row))
 expanded=compact(expanded)
 live=sorted({j for m in expanded for j in m})
 need(live==list(range(len(mapping))),'dead variable')
 need(degree(expanded)==4,'degree not four')
 metrics={'variables':len(mapping),'residuals':len(newrows),'degree':degree(expanded),'monomials':len(expanded),'coefficient_height':int(max(abs(c) for c in expanded.values())),'sum_residual_monomials':sum(map(len,symbolic)),'maximum_residual_coefficient':max(abs(c) for row in symbolic for c in row.values())}
 certificate={'source_sha256':hashlib.sha256(raw).hexdigest(),'source_path':ORIGINAL_PATHS[name],'comparison_commit':'7a8da414376a80b90ecf799f37ceb26fb9ac674e','eliminated_old_variable':v,'pivot_source_row':pivot_row,'pivot_coefficient':int(c),'integrity_source_row':integrity_row,'new_to_old_variables':mapping,'affine_recovery_old_indices':[[a.numerator,a.denominator,list(m)] for m,a in sorted(recovery.items())],'rows':certrows,'integrality_reason':'The surviving monic linear source row forces the rationally recovered coordinate to equal an integer polynomial in retained coordinates.'}
 write(out/'equation.json',new);write(out/'expanded_polynomial.json',{'schema':'collected_integer_polynomial_v1','variables':len(mapping),'terms':terms(expanded)})
 write(out/'METRICS.json',metrics);write(out/'projection_certificate.json',certificate)
 profiles.append({'profile':name,**metrics})
 print(name,json.dumps(metrics))
write(OUT/'ENDPOINTS.json',profiles)
