#!/usr/bin/env python3
"""Independent finite audit of the oriented pool constructions.

This file imports no builder. It checks integer polynomial identities and
literal data. The unbounded theorem and inherited calibration are mathematical
dependencies, not established by this finite audit.
"""
import copy,hashlib,json
from collections import defaultdict
from pathlib import Path
HERE=Path(__file__).resolve().parent
PACKAGE=HERE.parent
SOURCE=PACKAGE/'sources/parent225.json'
PIN='fee84c408828aba3e7ceebe9a37f58509327063aa7fd078fd49c80adf3af4e56'

class AuditFailure(Exception):pass
def require(p,msg):
 if not p:raise AuditFailure(msg)
def encode(j):return (json.dumps(j,sort_keys=True,separators=(',',':'))+'\n').encode()
def hashj(j):return hashlib.sha256(encode(j)).hexdigest()
def parsed(terms,n=None):
 require(isinstance(terms,list),'Bad polynomial container')
 ans={}
 for term in terms:
  require(isinstance(term,list) and len(term)==2,'Bad term')
  c,k=term
  require(type(c) is int and c!=0 and isinstance(k,list),'Bad coefficient')
  require(all(type(i) is int and i>=0 and (n is None or i<n) for i in k),'Bad index')
  require(k==sorted(k) and tuple(k) not in ans,'Noncanonical monomial')
  ans[tuple(k)]=c
 return ans
def lin(*items):
 d=defaultdict(int)
 for c,i in items:d[() if i is None else (i,)]+=c
 return {m:c for m,c in d.items() if c}
def summation(*ps):
 d=defaultdict(int)
 for p in ps:
  for k,v in p.items():d[k]+=v
 return {k:v for k,v in d.items() if v}
def times(*ps):
 a={():1}
 for b in ps:
  c=defaultdict(int)
  for k,v in a.items():
   for l,w in b.items():c[tuple(sorted(k+l))]+=v*w
  a={k:v for k,v in c.items() if v}
 return a
def negative(p):return {k:-v for k,v in p.items()}
def scalar(c,p):return {k:c*v for k,v in p.items() if c*v}
def difference(a,b):return summation(a,negative(b))
def square(p):return times(p,p)
def subzero(p,s):return {k:v for k,v in p.items() if not(set(k)&set(s))}
def coefficient(p,i):
 result={}
 for m,c in p.items():
  if i in m:
   require(m.count(i)==1,'Nonlinear special coordinate')
   mm=list(m);mm.remove(i);result[tuple(mm)]=c
 return result

def audit(parent,e,c,metrics):
 count=0
 def check(p,msg):
  nonlocal count
  require(p,msg);count+=1
 check(hashj(parent)==PIN,'Wrong parent literal system')
 check(c['parent_canonical_sha256']==PIN,'Certificate parent hash')
 check(c['parent_byte_sha256']==hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'Certificate byte hash')
 check(e['parent_equation_sha256']==PIN,'Equation parent hash')
 check(c['equation_sha256']==hashj(e),'Equation hash')
 n=len(parent['variables']);nn=len(e['variables'])
 check(n==225 and e['domain']=='unrestricted integers','Domain or arity')
 rows=[parsed(r['terms'],n) for r in parent['residuals']]
 allowed=[]
 check(c['restoring_row_operations']==allowed,'Unexpected restoring operation')
 for a,b,s in allowed:
  before=rows[a];rows[a]=summation(rows[a],scalar(s,rows[b]));check(difference(rows[a],scalar(s,rows[b]))==before,'Row shear inverse')
 gone=[149,150,151,152,153,154,221,222,223,224]
 gone_rows=[105,106,107,108,109,110,158,159,160,161]
 check(c['removed_variables']==gone and c['removed_rows']==gone_rows,'Deletion list')
 keep=[i for i in range(n) if i not in gone]
 check(c['retained_old_indices']==keep,'Coordinate inclusion')
 rename={i:j for j,i in enumerate(keep)}
 def mapold(p):return {tuple(rename[i] for i in k):v for k,v in p.items()}
 def getpoly(g,key):return parsed(g[key],nn)
 for i,p in enumerate(rows):
  if i not in gone_rows:check(not any(set(k)&set(gone) for k in p),'Removed coordinate not private')
 kept=[(i,p) for i,p in enumerate(rows) if i not in gone_rows]
 check(len(e['residuals'])==len(kept)+len(c['blocks']),'Residual count')
 check(e['variables'][:len(keep)]==[parent['variables'][i] for i in keep],'Coordinate names')
 for j,(old,p) in enumerate(kept):
  check(e['residuals'][j]['label']==parent['residuals'][old]['label'],'Retained label')
  check(parsed(e['residuals'][j]['terms'],nn)==mapold(p),'Retained residual coefficient')
 A=lin((1,142),(1,None));check(getpoly(c,'A')==mapold(A),'Pell A offset')
 singles=[(149,150,105,106,lin((1,3),(1,None)),lin((1,5)),lin((1,146)),lin((1,147)),lin((1,148))),
          (151,152,107,108,lin((1,4)),lin((1,18)),lin((1,182)),lin((1,183)),lin((1,184),(1,None))),
          (153,154,109,110,lin((1,194)),lin((1,102),(-1,None)),lin((1,182)),lin((1,183)),lin((1,184),(1,None)))]
 for j,(tv,qv,rt,rq,b,m,D,Y,Z) in enumerate(singles):
  T=summation(scalar(2,times(A,b)),negative(square(b)),lin((-1,None)))
  d=summation(m,negative(D),negative(times(b,Y)))
  E=summation(square(difference(m,D)),negative(square(Y)),scalar(-2,times(b,Y,summation(m,negative(D),negative(Z)))))
  g=c['groups'][j]
  for field,p in [('base',b),('T',T),('delta',d),('m',m),('D',D),('Y',Y),('Z',Z),('E',E),('Y_square_sum',square(Y))]:check(getpoly(g,field)==mapold(p),'Singleton '+str(j)+' '+field)
  target=difference(lin((1,tv)),T);check(rows[rt] in [target,negative(target)],'Singleton modulus identity')
  check(rows[rq]==summation(d,times(lin((1,tv)),lin((1,qv)))),'Singleton power identity')
  # The exact forward witness is h=T*q^2+Y^2. The following identity
  # is the local proof that a parent zero supplies the new integer h.
  h=summation(times(T,square(lin((1,qv)))),square(Y))
  error=difference(E,times(T,h))
  factors=summation(times(summation(d,times(T,lin((1,qv)))),difference(d,times(T,lin((1,qv))))),scalar(2,times(b,Y,difference(Z,times(A,Y)))))
  check(error==factors,'Singleton forward polynomial identity')
 # Explicit member lists independently identified in the protected source.
 members=[[(97,139,140,141,0,0),(114,166,167,168,0,0),(121,175,176,177,0,1)],
 [(96,148,149,150,0,0),(101,151,152,153,-1,0),(104,154,155,156,0,0),(107,157,158,159,0,0),(110,160,161,162,0,0),(113,163,164,165,0,0),(117,169,170,171,0,0),(120,172,173,174,0,0),(125,178,179,180,0,0),(128,181,182,183,0,0),(131,184,185,186,0,0)]]
 norms={139:(96,97),148:(104,105),151:(106,107),154:(108,109),157:(110,111),160:(112,113),163:(114,115),166:(116,117),169:(118,119),172:(120,121),175:(122,123),178:(124,125),181:(126,127),184:(128,129)}
 members=[[tuple(v+7 if k<4 else v for k,v in enumerate(row)) for row in group] for group in members]
 norms={key+7:tuple(v+7 for v in value) for key,value in norms.items()}
 for j,idxs in enumerate([(223,224,160,161),(221,222,158,159)],3):
  K,L,ia,ib=idxs;ar,br=rows[ia],rows[ib]
  b=negative(coefficient(br,K));a=coefficient(ar,L)
  E=summation(subzero(br,[K,L]),times(b,subzero(ar,[K,L])))
  T=summation(lin((-1,None)),negative(times(b,a)))
  g=c['groups'][j]
  check(getpoly(g,'base')==mapold(b) and getpoly(g,'T')==mapold(T) and getpoly(g,'E')==mapold(E),'Existing pool decomposition')
  check(T==summation(scalar(2,times(A,b)),negative(square(b)),lin((-1,None))),'Existing pool denominator')
  check(difference(E,times(T,lin((1,L))))==summation(br,times(b,ar)),'Existing pool elimination identity')
  natural_E={}
  for mi,di,yi,zi,yoff,zoff in members[j-3]:
   m=lin((1,mi));D=lin((1,di));Y=lin((1,yi),(yoff,None));Z=lin((1,zi),(zoff,None))
   natural_E=summation(natural_E,square(difference(m,D)),negative(square(Y)),scalar(-2,times(b,Y,summation(m,negative(D),negative(Z)))))
   gr,nr=norms[di]
   check(rows[gr]==difference(Z,times(A,Y)),'Retained AY gate')
   check(rows[nr]==summation(square(D),scalar(2,times(D,Z)),square(Y),lin((-1,None))),'Retained Pell norm')
  check(E==natural_E,'Pooled sum of errors exact')
 # Final polynomial residual is recovered with only finite products.
 for j,block in enumerate(c['blocks']):
  ids=block['groups'];z=block['quotient_index'];check(z==len(keep)+j,'Pool variable slot')
  gs=[c['groups'][i] for i in ids];Ts=[getpoly(g,'T') for g in gs]
  if block['weights']=='direct':
   check(ids==[0],'Direct singleton selection')
   result=summation(getpoly(gs[0],'delta'),times(lin((1,z)),Ts[0]))
  else:
   result=negative(times(lin((1,z)),*Ts))
   for k,g in enumerate(gs):
    w=getpoly(g,'base') if block['weights']=='base' else lin((1,None))
    result=summation(result,times(w,getpoly(g,'E'),*[T for at,T in enumerate(Ts) if at!=k]))
  check(parsed(e['residuals'][len(kept)+j]['terms'],nn)==result,'Literal pool expansion')
 pols=[parsed(r['terms'],nn) for r in e['residuals']]
 degree=max(len(k) for p in pols for k in p)
 check(metrics['degree']==2*degree and metrics['maximum_residual_degree']==degree,'Exact sum-of-squares degree')
 check(metrics['variables']==nn and metrics['residuals']==len(pols),'Metrics arity')
 check(metrics['literal_residual_terms']==sum(map(len,pols)),'Literal residual support')
 check(metrics['residual_coefficient_height']==max(abs(v) for p in pols for v in p.values()),'Residual coefficient height')
 check(set(i for p in pols for k in p for i in k)==set(range(nn)),'All coordinates used')
 check(metrics['collected_polynomial_terms'] is None and metrics['collected_polynomial_height'] is None,'No expanded polynomial metrics claimed')
 return count

def main():
 require(hashj(json.loads(SOURCE.read_text()))==PIN,'Parent mathematical bytes changed')
 parent=json.loads(SOURCE.read_text());results={}
 for variant in ('all5','staged','paired'):
  d=PACKAGE/'sources'/variant
  e=json.loads((d/'equation.json').read_text());c=json.loads((d/'certificate.json').read_text());m=json.loads((d/'metrics.json').read_text())
  checks=audit(parent,e,c,m);rejected=[]
  for mutation in ('coefficient','AY_offset','base_denominator','retained_row'):
   ec,cc=copy.deepcopy(e),copy.deepcopy(c)
   if mutation=='coefficient':ec['residuals'][-1]['terms'][0][0]+=1
   elif mutation=='AY_offset':cc['groups'][1]['Z'][0][0]+=1
   elif mutation=='base_denominator':cc['groups'][2]['T'][0][0]+=1
   else:ec['residuals'][0]['terms'][0][0]+=1
   cc['equation_sha256']=hashj(ec)
   try:audit(parent,ec,cc,m)
   except (AuditFailure,KeyError,ValueError):rejected.append(mutation)
   else:raise AuditFailure('Corruption accepted: '+mutation)
  results[variant]={'status':'passed','checks':checks,'deliberate_corruptions_rejected':rejected,'equation_sha256':hashj(e),'metrics':m}
 receipt={'status':'passed','independent_checker':True,'parent_sha256':PIN,'variants':results,'scope':'Finite exact identities and literal coefficients; unbounded arithmetic and logical calibration are separate proof dependencies.'}
 print(json.dumps(receipt,sort_keys=True))
if __name__=='__main__':main()
