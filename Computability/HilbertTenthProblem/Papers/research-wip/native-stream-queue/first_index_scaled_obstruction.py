#!/usr/bin/env python3
"""Scaled first/main Pell obstruction; exact bounded tests, no ancestor execution."""
import argparse,hashlib,json
from pathlib import Path
from collections import Counter
PINS={'first_index_quotient_deletion_scout.py': '3c35b2c0003ce0a844569da40e7da0ca3943bdd13a4d8ccd8186742c9ac48e70', 'first_index_quotient_deletion_scout.json': '0004189e84fdc34e1ae7cbffa30a0e904ec6a0f15be18bcabebe242a303163f8', 'first_index_quotient_deletion_scout.md': '7dafa6f20f3ae0c7ee7e44e6fa436b8dae7c6137ea9487ac1a50810c15bc1a32', 'complete85_auxiliary_bezout_projection.py': '3f619205a670b420312ba31d52b89cd8c87c169763ddf6c317c2db44ef0698f0', 'complete85_auxiliary_bezout_projection.json': 'e7ddc113f96cde37efc9d1973daffa5e4cef221db2c1d1c6ad1cf1772cd59edc', 'complete85_auxiliary_bezout_projection.md': 'd8f91555bed114470ee5dfb742175079f2df25e9c04d75abbf16752e70a91a4b', 'complete86_ordinary_auxiliary_projection.py': '130c8a09570866f3b510f4092aef3ab7fd61154f6c8776fcdba870d80a59019d', 'complete86_ordinary_auxiliary_projection.json': 'f46dd919a038b6dd646489e64585331de30b8c91a380cf9611afbf288122a9a6', 'complete86_ordinary_auxiliary_projection.md': 'cc3230f10c193d35df2820dad73b71f03b09493dfeca52618b1b23e9e0e59570'}
def need(v,s):
 if not v:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def stable(d):return json.dumps(d,sort_keys=True,separators=(',',':')).encode()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b

def pell(A,n):
 d=A*A-1;x,y=1,0;u,v=A,1
 while n:
  if n&1:x,y=x*u+d*y*v,x*v+y*u
  u,v=u*u+d*v*v,2*u*v;n//=2
 return x,y

def recurrence(A,n):
 x,y=1,0
 for _ in range(n):x,y=A*x+(A*A-1)*y,x+A*y
 return x,y

def fixture(p,n,Y):
 X=1<<p;q=16;need(X%q==0 and Y%(q**3)==0,'positive exact asymmetric scales')
 a=Y*(X+1);A=a+2;P=2*X*Y*Y+1;D,c=pell(A,p);tau,khalf=pell(P,n);k=2*khalf
 need((D,c)==recurrence(A,p)and(tau,khalf)==recurrence(P,n),'independent matrix power and recurrence Pell values')
 eta=c-k*Y;zeta=k*(Y+1)-c;need(eta>0 and zeta>0 and eta+zeta==k,'strict actual ratio')
 need(D*D-(A*A-1)*c*c==1 and tau*tau-X*Y*Y*(X*Y*Y+1)*k*k==1,'both exact norm equations')
 gamma,rem=divmod(D-a*c-X,4*a+3);need(rem==0 and gamma>1,'positive integral main projection')
 E=X*Y;need((k-p-1)%E==2*n-p-1 and 0<2*n-p-1<E,'failed index restoration at target p')
 need(c>A*(A*A-1)**2 and c>2*p and p>n,'large main-rank margins independently met')
 values=dict(q=q,X=X,Y=Y,w=X//q,s=Y//(q**3),p=p,n=n,a=a,A=A,P=P,D=D,c=c,tau=tau,k=k,eta=eta,zeta=zeta,gamma=gamma,rho=1,sigma=gamma-1)
 return values

def ledger(f):
 known=set(f['free']);defs={};counts=Counter()
 for n,o,a,b in f['source']:
  need(n not in known and o in ('+','-','*'),'actual topological candidate row')
  need(all(type(t)is int or type(t)is str and t in known for t in (a,b)),'actual closed candidate')
  known.add(n);defs[n]=(a,b);counts['M'if o=='*'else'A']+=1
 live=set();todo=[f['output']]
 while todo:
  t=todo.pop()
  if type(t)is int or t in live:continue
  live.add(t)
  if t in defs:todo.extend(defs[t])
 need(live==known,'every retained candidate gate and coordinate live')
 result=dict(total=len(defs),M=counts['M'],A=counts['A']);need(result==f['ledger'],'literal retained paid count')
 return result

def run(rows,values):
 e=dict(values)
 for n,op,a,b in rows:
  x=a if type(a)is int else e[a];y=b if type(b)is int else e[b]
  e[n]=x*y if op=='*'else x+y if op=='+'else x-y
 return e

def source_fixture(f,v):
 values={n:1 for n in f['free']};values.update(Bm1=15,Jrep=1,MC=14,MF=19,twice_cell_bits=8,inner_bits=3,Kconstant=12,F=5,Z=1,alpha=1,x=1,w=v['w'],s=v['s'],tau_root=v['tau'],eta=v['eta'],zeta=v['zeta'],rho=1,sigma=v['gamma']-1)
 values['transport_quotient']=(12+v['w']+10)//15
 need(15*values['transport_quotient']==12+v['w']+10 and all(z>0 for z in values.values()),'all supplied arithmetic fixture values positive')
 e=run(f['source'],values)
 need(e['q']==v['q']and e['wn2']==v['X']and e['sn2']==v['Y'],'actual paid scale ports')
 need(e['R10a']==v['c']and e['R10b']==v['k']and e['R12']==v['a']and e['R14']==v['D'],'actual paid first/main ports')
 need(e['norm_first']==e['norm_main']==e['norm_transport']==1,'actual retained first/main/transport factors')
 need(e['r_lhs']==44943 and e['marked_rhs']==1 and e['W']==0,'actual mask/transport fixture ports')
 need(e['norm_input']!=1 and e['norm_strong']!=1 and e[f['output']]!=0,'explicitly not a whole candidate zero')
 need(e['r_lhs']!=v['p'],'small full-row fixture does not claim actual packed target p')
 factors={n:dict(value_is_one=e[n]==1,sign=(e[n]>0)-(e[n]<0),bits=abs(e[n]).bit_length(),hex_sha256=sha(hex(e[n]).encode()))for n in ('norm_first','norm_main','norm_input','norm_aux','norm_transport','norm_strong')}
 return dict(parent=f['parent'],gates=len(f['source']),first_main_transport_one=True,actual_packed_R=44943,main_index_is_actual_packed_R=False,input_and_strong_fail=True,whole_candidate_zero=False,factors=factors,output_hex_sha256=sha(hex(e[f['output']]).encode()),output_bits=abs(e[f['output']]).bit_length())

def parametric_checks():
 packing=[]
 for t,F,Z in [(127,12,1),(177,8,5),(211,5,1)]:
  p=t*(t+2);n=t*(t+1);r=t+1;X=1<<p;Y=1<<r;q=16
  need(t>=11 and t%2==1 and p%4==3 and p>n,'actual family parameters')
  need(p-n==t and 2*n-p==t*t,'symbolic exponent balances specialized')
  # Baseline identity is compared by exact powers-of-two exponents.
  need((p-1)*(1+p+r)==1+(n-1)*(2+p+2*r)+r,'exact baseline power balance')
  need(p<=1<<t and 2*(p-1)*(Y+1)<X,'strict upper-ratio margin')
  need(X%q==0 and Y%(q**3)==0 and 0<t*t-1<X*Y,'scale and nonzero congruence remainder')
  G=q*q-q*F-Z;R=G*(q*q-1)+14+q*19
  need(R==p and F>0 and Z>0 and F+Z<q,'actual paid shifted-mask packing R=p')
  need(14<15 and 4<15 and 14%4==2 and 4%8==4 and (14).bit_count()+(4).bit_count()==4,'stated necessary native-mask conditions')
  need((2*q-1)*(q*q-1)<R<q**4-q**3,'retained coarse packing bounds')
  packing.append(dict(t=t,p=p,n=n,X_exponent=p,Y_exponent=r,q=q,w_exponent=p-4,s_exponent=r-12,F=F,Z=Z,G=G,Jrep=1,Bm1=15,MC=14,native_MF=4,paid_MF=19,R=R,restoration_remainder=t*t-1,exact_Pell_values_materialized=False))
 # The general exponent cancellation is proved algebraically in the note;
 # these three checks verify its explicit packing instances only.
 return packing

def verify(root):
 blobs={}
 for name,h in PINS.items():
  b=(root/name).read_bytes();need(sha(b)==h,'pinned context '+name);blobs[name]=b
 old=json.loads(blobs['first_index_quotient_deletion_scout.json']);need(old['source_sha256']==PINS['first_index_quotient_deletion_scout.py'],'scout source receipt pin')
 need(len(old['forms'])==2,'exact two candidates')
 ls=[]
 for f in old['forms']:
  need(f['parent_sha256']==PINS[f['parent']],'actual parent receipt binding');ls.append(ledger(f))
 cases=[];gates=0
 for p,n,Y in [(55,40,1<<32),(143,132,1<<12)]:
  v=fixture(p,n,Y);checks=[source_fixture(f,v)for f in old['forms']];gates+=sum(c['gates']for c in checks)
  cases.append(dict(p=p,n=n,Y_exponent=Y.bit_length()-1,first_index_remainder=2*n-p-1,exact_values_hex={k:hex(x)for k,x in v.items()},full_retained_source_evaluations=checks))
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),context_pins=PINS.copy(),candidate_ledgers=ls,exact_scaled_first_main_fixtures=cases,parametric_packing_instances=parametric_checks(),counts=dict(exact_small_Pell_fixtures=2,independent_Pell_evaluations=4,complete_retained_candidate_evaluations=4,paid_rows_evaluated=gates,parametric_packing_instances=3),scope='Scaling and literal necessary-mask/packing arithmetic do not force the deleted index congruence in the first/main subsystem. The small complete-source evaluations explicitly fail input/strong and are not zeros; the three large instances use the written parametric proof without materialized Pell values. No full zero, valid compiled history, sound deletion or universal cost improvement is claimed.')

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'type-exact receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status='PASS',**r['counts']),sort_keys=True))
if __name__=='__main__':main()
