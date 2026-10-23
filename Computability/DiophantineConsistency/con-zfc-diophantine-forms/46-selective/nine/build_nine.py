#!/usr/bin/env python3
"""Support-selective nine-variable polynomial.

Adapted from ProveIt package45 build_multitarget_nine.py, pinned
124c07c0b77a9e20e84676514d8b1ff78536ea3f. The Jones ratio/finalizer tail
is retained; the source uses unshifted quadratic records and positive digits.
"""
from pathlib import Path
import json, hashlib, gzip
from collections import Counter
from functools import lru_cache
from circuit import Circuit
ROOT=Path(__file__).resolve().parent
BASE_EXPONENT=2140030
PORTS=['beta','K0','MC','MF']
PORT_FILES=['beta','K','MC','MF_source']

def quadratic_form(d,terms,coordinates):
 @lru_cache(None)
 def go(items):
  if not items:return d.c(0)
  counts=[sum(ex[j]>0 for ex,co in items) for j in range(len(coordinates))]
  if not max(counts):return d.add(*(co for ex,co in items))
  j=max(range(len(coordinates)),key=lambda j:(counts[j],sum(ex[j] for ex,co in items),j))
  yes=[];no=[]
  for ex,co in items:
   if ex[j]:
    e=list(ex);e[j]-=1;yes.append((tuple(e),co))
   else:no.append((ex,co))
  return d.add(go(tuple(no)),d.mul(coordinates[j],go(tuple(yes))))
 return go(tuple(terms))

def source(d,positive):
 data=json.loads((ROOT/'data/raw_recipes.json').read_text())
 layout=json.loads((ROOT/'data/layout.json').read_text())
 weights=layout['weights'];W=max(weights);targets=layout['targets'];perm=layout['row_permutation']
 Hmax=targets[-1];Kcode=Hmax+2*W
 c=d.c;add=d.add;mul=d.mul;sub=d.sub;pw=d.pow;save=d.save
 variables=['epsilon','g','h','s','w','phi','i','j','n'];v={n:d.node('variable',n) for n in variables}
 if positive:
  for x in ['epsilon','phi','n']:v[x]=sub(v[x],c(1))
 else:
  for x in ['g','h','s','w','i','j']:v[x]=add(v[x],c(1))
 b=save('b',add(d.node('fixed','base_floor'),v['epsilon']))
 B=save('B',pw(b,3))
 terms=[]
 for target,j in zip(targets,perm):
  for term in data['rows'][j]:
   exponent=target-sum(a*w for a,w in zip(term['alpha'],weights[1:]))
   leaf=c(term['leaf']) if isinstance(term['leaf'],int) else d.node('fixed',term['leaf'])
   sign=term['sign']
   if isinstance(term['leaf'],int) and term['leaf']<0:
    leaf=c(-term['leaf']);sign=-sign
   terms.append((exponent,leaf,sign))
 terms.sort(reverse=True)
 dc=terms[0][1] if terms[0][2]==1 else sub(c(0),terms[0][1]);previous=terms[0][0]
 for exponent,leaf,sign in terms[1:]:
  scaled=mul(pw(B,previous-exponent),dc)
  dc=add(scaled,leaf) if sign==1 else sub(scaled,leaf)
  previous=exponent
 Dcode=save('Dcode',mul(pw(B,previous),dc))
 sw=sorted(weights[1:],reverse=True);ell=c(1);previous=sw[0]
 for exponent in sw[1:]:
  ell=add(mul(pw(B,previous-exponent),ell),c(1));previous=exponent
 ell=save('ell',mul(pw(B,previous),ell))
 N0=save('N0',pw(B,W+1))
 N1=save('N1',mul(c(4),pw(B,Kcode+1)))
 N=save('N',mul(N0,N1))
 mask=save('mask',sub(sub(N0,c(1)),mul(sub(b,c(1)),ell)))
 target=c(1)
 for j in reversed(range(len(targets)-1)):
  target=add(c(1),mul(pw(B,targets[j+1]-targets[j]),target))
 target=save('targets',mul(pw(B,targets[0]),target))
 Tc=save('Tcode',add(mask,mul(sub(B,c(2)),target,N0)))
 Jc=save('Jcode',add(mul(c(2),pw(add(c(1),ell,v['g']),2),Dcode),mul(B,d.geom(B,Kcode+1))))
 Sc=save('Scode',add(v['g'],mul(Jc,N0)))
 R=save('R',mul(sub(N,c(1)),add(mul(add(Sc,Tc,c(1)),N),Tc,c(1))))
 cap=save('Gcap',mul(c(32),b,pw(B,W)))
 meta={'variables':variables,'W':W,'weights':weights,'target_maximum':Hmax,'targets':targets,
       'Kcode':Kcode,'source_degree':2,'base_floor_exponent':BASE_EXPONENT,
       'coefficient_bound_power_of_two':2140017,'positive_digits_offset':1,
       'coefficient_recipes':data['recipes'],'row_permutation':perm,
       'row_order_one_based':data['row_order_one_based'],
       'source_layout_sha256':hashlib.sha256((ROOT/'data/layout.json').read_bytes()).hexdigest(),
       'source_recipes_sha256':hashlib.sha256((ROOT/'data/raw_recipes.json').read_bytes()).hexdigest()}
 return v,b,B,N,R,cap,meta

def build(positive,certificate):
 d=Circuit();c=d.c;add=d.add;mul=d.mul;sub=d.sub;pw=d.pow;save=d.save
 v,b,B,N,R,cap,meta=source(d,positive)
 U=save('U',mul(pw(N,2),v['w']));Y=save('Y',mul(pw(N,2),v['s']));M=save('M',mul(R,Y))
 P=save('P',mul(c(2),pw(M,2),U));K=save('K',add(R,c(1),mul(v['h'],sub(P,c(1)))))
 A=save('A',mul(M,add(U,c(1))));B1=add(mul(c(2),R),c(1));W1=mul(b,v['w']);C=save('C',add(B1,W1,v['phi']));J=save('J',sub(mul(c(4),A),c(5)))
 Q=save('Q',sub(mul(c(3),W1,C),mul(c(2),sub(pw(W1,2),c(1)))))
 Am1=sub(pw(A,2),c(1));D=save('D',add(mul(Am1,pw(C,2)),c(1)));E=save('E',mul(v['i'],J,D,pw(C,2)));F=save('F',add(mul(Am1,pw(E,2)),c(1)))
 G=save('G',add(A,mul(F,sub(add(mul(C,D),c(1)),A))));H=save('H',add(B1,mul(v['j'],C)));I=save('I',add(mul(sub(pw(G,2),c(1)),pw(H,2)),c(1)))
 a0=save('a0',add(sub(pw(mul(P,K),2),pw(K,2)),c(1)));a1=save('a1',mul(D,F,I));u=save('u',mul(J,F));vc=save('v',add(mul(Q,F),mul(J,sub(H,C))))
 m=save('m',sub(mul(sub(pw(K,2),mul(c(4),pw(sub(C,mul(K,Y)),2))),cap),mul(c(8),v['g'],pw(K,2))))
 V0=save('V0',mul(P,K));MD=mul(A,C);MF=mul(A,E);MI=mul(G,H);V1=save('V1',mul(MD,MF,MI))
 Md=save('Mdiv',add(Q,H));Om=save('Omega',mul(u,m))
 E0=save('E0',sub(add(mul(u,add(v['n'],Md)),vc),mul(c(2),Om,Md)));Th=save('Theta',sub(E0,mul(Om,V0,V1)))
 if certificate:
  delta=save('deltaV',add(mul(sub(pw(C,2),c(1)),pw(MF,2),pw(MI,2)),mul(D,sub(pw(E,2),c(1)),pw(MI,2)),mul(D,F,sub(pw(H,2),c(1)))))
  inn=save('inner',sub(add(sub(pw(E0,2),mul(c(2),E0,Om,V0,V1)),mul(pw(Om,2),pw(V0,2),delta)),mul(pw(Om,2),a0)))
 else:inn=save('inner',sub(pw(Th,2),mul(pw(Om,2),add(a0,mul(pw(V0,2),a1)))))
 out=sub(pw(inn,2),mul(c(4),pw(Om,4),pw(V0,2),a0,a1));ns,out,names=d.export(out);counts=dict(Counter(n['kind'] for n in ns if 'left'in n))
 meta.update(schema='proveit-selective-nine-v1',domain='positive integers' if positive else 'nonnegative integers',nodes=ns,output=out,named_nodes=names,operation_counts=counts,total_operations=sum(counts.values()),degree=1152*(3*(meta['target_maximum']+3*meta['W']+2))+12*meta['W']+280,diagonal_leading_coefficient='2^2050',certificate_form=certificate,coefficient_binding='data/raw_recipes.json',proof='PROOF.md')
 return meta


def main():
 (ROOT/'generated').mkdir(exist_ok=True)
 for positive in [True,False]:
  for cert in [False,True]:
   out=build(positive,cert)
   name='selective_nine_'+('positive' if positive else 'natural')+('_degree_certificate' if cert else '')+'.json'
   (ROOT/'generated'/name).write_text(json.dumps(out,separators=(',',':'))+'\n')
   print(name,out['degree'],out['total_operations'],out['base_floor_exponent'])
if __name__=='__main__':main()
