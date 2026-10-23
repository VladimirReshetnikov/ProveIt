#!/usr/bin/env python3
"""New authored multi-target quadratic nine-variable circuit builder."""
from pathlib import Path
import json,hashlib
from collections import Counter
import sympy as s
from circuit import Circuit
ROOT=Path(__file__).resolve().parent

def source(d,positive):
 data=json.loads((ROOT.parent/'quartic/QUADRATIC_TARGETS.json').read_text());weights=data['weights'];W=max(weights);Hmax=data['target_maximum'];Kcode=Hmax+2*W
 c=d.c;add=d.add;mul=d.mul;sub=d.sub;pw=d.pow;save=d.save
 variables=['epsilon','g','h','s','w','phi','i','j','n'];v={n:d.node('variable',n) for n in variables}
 if positive:
  for x in ['epsilon','phi','n']:v[x]=sub(v[x],c(1))
 else:
  for x in ['g','h','s','w','i','j']:v[x]=add(v[x],c(1))
 pp=s.symbols('beta K0 MC MF');bits=[1064921,1070004,1064921,1064922];recipes={};aliases=[];maxbound=0
 for row in data['rows']:
  for term in row['terms']:
   poly=s.Poly(s.sympify(term['weighted_coefficient'],locals=dict(zip(data['ports'],pp))),*pp)
   rec=[{'powers':list(es),'coefficient':int(co)} for es,co in sorted(poly.terms())]
   key=json.dumps(rec,sort_keys=True)
   if key not in recipes:recipes[key]=(f'a{len(recipes):03d}',rec)
   term['recipe_name']=recipes[key][0]
   bound=sum(abs(t['coefficient'])*(1<<sum(a*b for a,b in zip(t['powers'],bits))) for t in rec);maxbound=max(maxbound,bound)
 Mexp=maxbound.bit_length();floor_exp=Mexp+12
 b=save('b',add(d.node('fixed','base_floor'),v['epsilon']));B=save('B',pw(b,3));hom=[pw(B,W)]+[pw(B,W-w) for w in weights]
 coefnodes={}
 for name,rec in recipes.values():
  if len(rec)==1 and rec[0]['powers']==[0]*4:coefnodes[name]=c(rec[0]['coefficient'])
  else:coefnodes[name]=d.node('fixed',name)
 rowpoly=[]
 for row in data['rows']:
  terms=[]
  for t in row['terms']:
   a=t['alpha'];mon=mul(*(pw(hom[i],e) for i,e in enumerate([2-sum(a)]+a) if e))
   terms.append(mul(coefnodes[t['recipe_name']],mon))
  rowpoly.append(add(*terms))
 stride=pw(B,data['target_spacing']);Dhom=rowpoly[-1]
 for row in reversed(rowpoly[:-1]):Dhom=add(mul(Dhom,stride),row)
 Dcode=save('Dcode',mul(B,Dhom));ell=save('ell',add(*(pw(B,w) for w in weights)))
 N0=save('N0',pw(B,W+1));N1=save('N1',mul(c(4),pw(B,Kcode+1)));N=save('N',mul(N0,N1))
 mask=save('mask',sub(sub(N0,c(1)),mul(sub(b,c(1)),ell)))
 targets=save('targets',mul(stride,d.geom(stride,len(rowpoly))))
 Tc=save('Tcode',add(mask,mul(sub(B,c(2)),targets,N0)))
 Jc=save('Jcode',add(mul(c(2),pw(add(c(1),v['g']),2),Dcode),mul(B,d.geom(B,Kcode+1))))
 Sc=save('Scode',add(v['g'],mul(Jc,N0)))
 R=save('R',mul(sub(N,c(1)),add(mul(add(Sc,Tc,c(1)),N),Tc,c(1))))
 cap=save('Gcap',mul(c(32),b,pw(B,W)))
 meta={'variables':variables,'W':W,'weights':weights,'target_maximum':Hmax,'Kcode':Kcode,'source_degree':2,'base_floor_exponent':floor_exp,'coefficient_bound_power_of_two':Mexp,'port_bit_lengths':bits,'coefficient_recipes':[{'name':name,'terms':r} for name,r in recipes.values()],'row_order':data['row_order_one_based'],'target_records_sha256':hashlib.sha256((ROOT.parent/'quartic/QUADRATIC_TARGETS.json').read_bytes()).hexdigest()}
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
 meta.update(schema='proveit-multitarget-nine-v1',domain='positive integers' if positive else 'nonnegative integers',nodes=ns,output=out,named_nodes=names,operation_counts=counts,total_operations=sum(counts.values()),degree=162444*meta['W']+83224,diagonal_leading_coefficient='2^2050',certificate_form=certificate,coefficient_binding='../MULTITARGET_INSTANCE.json',proof='MULTITARGET_NINE_PROOF.md')
 return meta

def main():
 (ROOT/'generated').mkdir(exist_ok=True)
 for positive in [True,False]:
  for cert in [False,True]:
   out=build(positive,cert);name='multitarget_nine_'+('positive' if positive else 'natural')+('_degree_certificate' if cert else '')+'.json';(ROOT/'generated'/name).write_text(json.dumps(out,separators=(',',':'))+'\n');print(name,out['degree'],out['total_operations'],out['base_floor_exponent'])
if __name__=='__main__':main()

