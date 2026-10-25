#!/usr/bin/env python3
"""Independent finite-field rank audit of all affine-polynomial multipliers.

For m quadratic residuals in n variables, columns are R_i and x_j R_i.
Rows retain only coefficients of monomials of degrees 2 and 3. A full
column-rank reduction modulo a prime proves that no nonzero affine-coefficient
combination of the residuals has degree at most one, over Q or any extension.
Only standard library; no builder imports and no floating-point arithmetic.
"""
import argparse,collections,copy,hashlib,json,math
from pathlib import Path
P=1000003

def require(ok,message):
 if not ok:raise ValueError(message)
def rank_data(equation):
 n=len(equation['variables']);res=equation['residuals'];count=len(res)*(n+1)
 require(all(P%d for d in range(2,math.isqrt(P)+1)),'prime modulus')
 # Directly accumulate the truncation of every x_j*R_i and every R_i.
 constraints=collections.defaultdict(dict)
 for row,r in enumerate(res):
  for coeff,monomial in r['terms']:
   require(type(coeff) is int and len(monomial)<=2,'quadratic integer input')
   monomial=tuple(monomial)
   for multiplier in range(n+1):
    term=monomial if multiplier==n else tuple(sorted(monomial+(multiplier,)))
    if len(term)<2:continue
    col=row*(n+1)+multiplier;v=(constraints[term].get(col,0)+coeff)%P
    if v:constraints[term][col]=v
    else:constraints[term].pop(col,None)
 original_rows=sum(bool(r) for r in constraints.values())
 incidence=[set() for _ in range(count)]
 for monomial,row in constraints.items():
  for col in row:incidence[col].add(monomial)
 queue=collections.deque(m for m,row in constraints.items() if len(row)==1);forced=set()
 while queue:
  monomial=queue.popleft();row=constraints[monomial]
  if len(row)!=1:continue
  col=next(iter(row));forced.add(col)
  for other in incidence[col]:
   constraints[other].pop(col,None)
   if len(constraints[other])==1:queue.append(other)
 active=[row for row in constraints.values() if row];pivot={}
 for row in sorted(active,key=lambda r:(len(r),tuple(sorted(r)))):
  v=row.copy()
  while v:
   col=min(v)
   if col not in pivot:
    inverse=pow(v[col],-1,P);pivot[col]={j:inverse*c%P for j,c in v.items()};break
   multiple=v[col]
   for j,c in pivot[col].items():
    value=(v.get(j,0)-multiple*c)%P
    if value:v[j]=value
    else:v.pop(j,None)
 rank=len(forced)+len(pivot)
 return {'variables':n,'residuals':len(res),'matrix_columns':count,'matrix_rows':original_rows,'residual_matrix_rows':sum(bool(r) for r in constraints.values()),'prime':P,'singleton_pivots':len(forced),'remaining_pivots':len(pivot),'rank':rank,'nullity':count-rank}

def main():
 a=argparse.ArgumentParser();a.add_argument('--equation',type=Path);a.add_argument('--output',type=Path);a.add_argument('--controls',action='store_true');args=a.parse_args();path=args.equation or Path(__file__).resolve().parent/'integer246/equation.json';raw=path.read_bytes();s=json.loads(raw);result=rank_data(s);require(result['nullity']==0,'not full column rank');result.update({'status':'pass','equation_sha256':hashlib.sha256(raw).hexdigest(),'optimized_python':not __debug__,'scope':'No nonzero affine-polynomial multiplier combination of these residuals can have degree <=1. Not a global quartic lower bound.'})
 if args.controls:
  bad=copy.deepcopy(s);bad['residuals'][-1]=bad['residuals'][0]
  require(rank_data(bad)['nullity']>0,'duplicate row did not trigger rank failure');result['duplicate_residual_control_rejected']=True
 text=json.dumps(result,indent=2)+'\n'
 if args.output:args.output.write_text(text)
 print(text,end='')
if __name__=='__main__':main()
