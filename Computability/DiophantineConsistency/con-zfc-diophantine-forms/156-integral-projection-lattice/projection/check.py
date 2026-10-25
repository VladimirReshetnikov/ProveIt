#!/usr/bin/env python3
"""Independent exponent-vector validation of integral affine projections.

This program does not import the producer. It checks the exact change of
coordinates, the surviving monic integrality equation, every coefficient,
and a finite-field full-rank certificate for the quadratic row parts.
"""
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
from copy import deepcopy
import hashlib,json,math,sys

ROOT=Path(__file__).resolve().parent

def require(condition,message):
 if not condition:raise ValueError(message)
def purge(p):return {e:c for e,c in p.items() if c}
def addto(p,q,a=1):
 for e,c in q.items():p[e]+=a*c

def multiply(p,q):
 out=defaultdict(Fraction)
 for e,a in p.items():
  for f,b in q.items():out[tuple(x+y for x,y in zip(e,f))]+=a*b
 return purge(out)
def parse(terms,n):
 out=defaultdict(Fraction)
 for c,indices in terms:
  require(isinstance(c,int),'noninteger literal coefficient')
  e=[0]*n
  for i in indices:
   require(isinstance(i,int) and 0<=i<n,'bad variable index');e[i]+=1
  out[tuple(e)]+=c
 return purge(out)
def fromindices(indices,n):
 e=[0]*n
 for i in indices:e[i]+=1
 return tuple(e)
def affine_substitute(source_row,old_n,target,new_to_old,recovery):
 n=len(new_to_old);zero=(0,)*n
 old_to_new={j:i for i,j in enumerate(new_to_old)}
 out=defaultdict(Fraction)
 for coeff,monomial in source_row['terms']:
  term={zero:Fraction(coeff)}
  for var in monomial:
   if var==target:term=multiply(term,recovery)
   else:term=multiply(term,{fromindices([old_to_new[var]],n):Fraction(1)})
  addto(out,term)
 return purge(out)
def monic_integrality(source,row,target):
 f=parse(source['residuals'][row]['terms'],len(source['variables']))
 k=max((e[target] for e in f),default=0)
 require(k>=1,'integrality row does not involve removed variable')
 lead={tuple(v if i!=target else 0 for i,v in enumerate(e)):c for e,c in f.items() if e[target]==k}
 zero=(0,)*len(source['variables'])
 require(len(lead)==1 and lead.get(zero,0) in (-1,1),'integrality equation is not monic with constant leading coefficient')
 return k

def rank(rows,n,p=1000003):
 bas={};piv=[]
 for ri,row in enumerate(rows):
  r={tuple(mm):cc%p for cc,mm in row['terms'] if len(mm)==2 and cc%p}
  while r:
   m=min(r);a=r[m]
   if m not in bas:
    inv=pow(a,-1,p);bas[m]={e:c*inv%p for e,c in r.items()};piv.append({'row':ri,'monomial':list(m),'pivot_value':a});break
   for e,c in bas[m].items():
    r[e]=(r.get(e,0)-a*c)%p
    if not r[e]:del r[e]
 return len(bas),piv

def check_objects(source,new,cert,exp,metrics):
 n=len(new['variables']); old_n=len(source['variables']);v=cert['eliminated_old_variable'];r0=cert['pivot_source_row'];r1=cert['integrity_source_row']
 require(old_n==n+1,'wrong dimension change')
 require(r1!=r0,'integrality row deleted')
 require(0<=v<old_n and 0<=r0<len(source['residuals']) and 0<=r1<len(source['residuals']),'bad indices')
 mapping=cert['new_to_old_variables'];require(mapping==[i for i in range(old_n) if i!=v],'wrong coordinate map')
 require(new['variables']==[source['variables'][i] for i in mapping],'metadata map mismatch')
 require(new['domain']=='unrestricted integers','wrong domain')
 monic_degree=monic_integrality(source,r1,v)
 pivot=parse(source['residuals'][r0]['terms'],old_n)
 e=[0]*old_n;e[v]=1;e=tuple(e)
 c=pivot.get(e,0);require(c==cert['pivot_coefficient'] and abs(c)>1,'wrong nonunit pivot')
 require(all(f==e or not f[v] for f in pivot),'nonlinear target in pivot')
 require(max((sum(f) for f in pivot),default=0)<=1,'pivot is not affine')
 invmap={old:newi for newi,old in enumerate(mapping)}
 recovery=defaultdict(Fraction)
 for num,den,indices in cert['affine_recovery_old_indices']:
  require(den>0 and v not in indices,'invalid recovery')
  recovery[fromindices([invmap[j] for j in indices],n)]+=Fraction(num,den)
 recovery=purge(recovery)
 require(max((sum(e) for e in recovery),default=0)<=1,'recovery not affine')
 require(not affine_substitute(source['residuals'][r0],old_n,v,mapping,recovery),'pivot is not an identity')
 require(len(new['residuals'])==len(source['residuals'])-1,'row count mismatch')
 expected=[i for i in range(len(source['residuals'])) if i!=r0]
 require([item['source_row'] for item in cert['rows']]==expected,'incomplete source coverage')
 parsed=[]
 for j,item in enumerate(cert['rows']):
  require(item['new_row']==j,'wrong target row index')
  oldi=item['source_row'];q=affine_substitute(source['residuals'][oldi],old_n,v,mapping,recovery)
  scale=Fraction(item['multiplier_numerator'],item['multiplier_denominator'])
  require(scale>0,'nonpositive row scale')
  q={e:a*scale for e,a in q.items()};require(all(a.denominator==1 for a in q.values()),'denominator remains')
  row=parse(new['residuals'][j]['terms'],n)
  require(row==q,'substitution identity mismatch at row '+str(j))
  require(math.gcd(*(int(a) for a in row.values()))==1,'row not primitive')
  require(max(map(sum,row),default=0)<=2,'residual degree exceeds two')
  parsed.append(row)
 allterms=defaultdict(Fraction)
 for row in parsed:addto(allterms,multiply(row,row))
 allterms=purge(allterms)
 require(allterms==parse(exp['terms'],n),'collected polynomial mismatch')
 require(all(a.denominator==1 for a in allterms.values()),'polynomial not integral')
 live={i for e in allterms for i,a in enumerate(e) if a}
 require(live==set(range(n)),'a declared variable is absent')
 observed={'variables':n,'residuals':len(parsed),'degree':max(map(sum,allterms),default=0),'monomials':len(allterms),'coefficient_height':int(max(map(abs,allterms.values()))),'sum_residual_monomials':sum(len(r) for r in parsed),'maximum_residual_coefficient':int(max(abs(a) for r in parsed for a in r.values()))}
 require(observed==metrics,'metric mismatch')
 require(observed['degree']==4,'degree not exactly four')
 return {'metrics':observed,'integrality_equation_degree':monic_degree,'source_rows_checked':len(source['residuals']),'all_coefficients_checked':True}

def load(p):return json.loads(p.read_text())
def main():
 receipt={}
 for folder in sorted(p for p in ROOT.iterdir() if p.is_dir() and (p/'equation.json').exists()):
  raw=(folder/'source_equation.json').read_bytes();source=json.loads(raw)
  new=load(folder/'equation.json');cert=load(folder/'projection_certificate.json');exp=load(folder/'expanded_polynomial.json');metrics=load(folder/'METRICS.json')
  require(hashlib.sha256(raw).hexdigest()==cert['source_sha256'],'source hash mismatch')
  r=check_objects(source,new,cert,exp,metrics)
  got,piv=rank(new['residuals'],len(new['variables']))
  expected=load(folder/'QUADRATIC_RANK.json')
  require(expected['prime']==1000003 and got==expected['quadratic_rank_mod_prime']==len(new['residuals']),'rank not full')
  require(piv==expected['pivots'],'rank certificate mismatch')
  r['quadratic_row_rank']=got
  bad=deepcopy(cert);bad['integrity_source_row']=bad['pivot_source_row']
  try:check_objects(source,new,bad,exp,metrics)
  except ValueError:pass
  else:raise ValueError('deleted-integrality mutation accepted')
  bad=deepcopy(new);bad['residuals'][0]['terms'][0][0]+=1
  try:check_objects(source,bad,cert,exp,metrics)
  except ValueError:pass
  else:raise ValueError('coefficient mutation accepted')
  bad=deepcopy(cert);bad['affine_recovery_old_indices'][0][0]+=1
  try:check_objects(source,new,bad,exp,metrics)
  except ValueError:pass
  else:raise ValueError('recovery mutation accepted')
  r['rejected_mutations']=3
  receipt[folder.name]=r
 print(json.dumps({'ok':True,'profiles':receipt},indent=2))
if __name__=='__main__':main()
