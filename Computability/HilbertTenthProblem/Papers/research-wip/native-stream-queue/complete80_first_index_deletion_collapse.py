#!/usr/bin/env python3
"""Pinned-data current84 first-index deletion and Report41 counterfamily transfer.
No predecessor or archived program is imported or executed. This rejected
candidate is not a universal operation bound. See the companion proof.
"""
import argparse
import copy
from fractions import Fraction
import hashlib
import io
import json
import math
from pathlib import Path
import random
import subprocess
import zipfile

REV = 'c5612efa171fa62470285049ee45d1d06ee25578'
ARCHIVE_PATH = 'docs/incoming/Failure_of_First_Index_Deletion_Package.zip'
ARCHIVE_BLOB = '0717dc5ae5cf5f44afbee2b7fe14aa8da4a2f186'
ARCHIVE_SHA = '1ace5ba39dd17fa53972420ba4db4171174def1244f1c377f31089f97921f2fd'
PINS = {
 'complete84_scaled_strong_output.py':'8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
 'complete85_auxiliary_bezout_projection.json':'e7ddc113f96cde37efc9d1973daffa5e4cef221db2c1d1c6ad1cf1772cd59edc',
 'first_index_quotient_deletion_scout.py':'3c35b2c0003ce0a844569da40e7da0ca3943bdd13a4d8ccd8186742c9ac48e70',
 'first_index_quotient_deletion_scout.json':'0004189e84fdc34e1ae7cbffa30a0e904ec6a0f15be18bcabebe242a303163f8',
 'first_index_quotient_deletion_scout.md':'7dafa6f20f3ae0c7ee7e44e6fa436b8dae7c6137ea9487ac1a50810c15bc1a32',
 'first_index_scaled_obstruction.md':'b67d208d4c18e45145cf91f272d72e2852c09d79be631da8f0a0ce5f377ba1fd',
 'complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
 'complete75_coupled_index_linear88.md':'1533ef2411347335704f46a8a1020d8d46dea1147b03e9c9d35684a687172e39',
}
MEMBERS = {
 'FULL_COUNTERFAMILY.md':'dc886e8991e32c331b9135b4ea6b3f73733656be3df6c2aa01576e1732fb83e1',
 'SOURCE_CORRESPONDENCE.md':'2316807268e48196f21371671ce43c68ccf106ab1e6a03db55ef39ff1ef1bbe0',
 'scout.json':PINS['first_index_quotient_deletion_scout.json'],
 'complete85_auxiliary_bezout_projection.json':PINS['complete85_auxiliary_bezout_projection.json'],
 'provenance/complete75_half_binomial_compiler.md':PINS['complete75_half_binomial_compiler.md'],
 'provenance/complete75_coupled_index_linear88.md':PINS['complete75_coupled_index_linear88.md'],
 'provenance/FIXED_RAW_UNIVERSAL_76_PROOF.md':'75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87',
}
REMOVED = ['hpm1','index_difference','norm_index','norm_product']
FACTORS = ['norm_first','norm_main','norm_input','norm_aux','norm_transport','norm_strong']

def require(ok, message):
 if not ok: raise ValueError(message)
def sha(data): return hashlib.sha256(data).hexdigest()
def pairs(items):
 out={}
 for k,v in items:
  require(k not in out, 'duplicate JSON key '+k);out[k]=v
 return out
def bad_number(s): raise ValueError('noninteger/nonfinite JSON number '+s)
def read_json(data): return json.loads(data,object_pairs_hook=pairs,parse_float=bad_number,parse_constant=bad_number)
def exact(a,b):
 if type(a) is not type(b): return False
 if isinstance(a,dict): return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def authenticate(root, archive):
 data={}
 for n,h in PINS.items():
  b=(root/n).read_bytes();require(sha(b)==h,'pin '+n);data[n]=b
 if archive is None:
  zbytes=subprocess.check_output(['git','-C',str(root),'show',REV+':'+ARCHIVE_PATH])
 else: zbytes=archive.read_bytes()
 require(sha(zbytes)==ARCHIVE_SHA,'archive SHA256')
 require(hashlib.sha1(b'blob '+str(len(zbytes)).encode()+b'\0'+zbytes).hexdigest()==ARCHIVE_BLOB,'archive Git blob')
 sizes={}
 with zipfile.ZipFile(io.BytesIO(zbytes)) as z:
  require(len(z.namelist())==len(set(z.namelist())),'duplicate archive member')
  for n,h in MEMBERS.items():
   b=z.read('Research_Report41/evidence/'+n);require(sha(b)==h,'member '+n);sizes[n]=len(b)
   if n in ['scout.json','complete85_auxiliary_bezout_projection.json']:
    local='first_index_quotient_deletion_scout.json' if n=='scout.json' else n
    require(b==data[local],'archive/local source differs '+n)
 return data,sizes,len(zbytes)

def rows_map(source): return {r[0]:r for r in source}
def inspect(packet):
 source=packet['source'];free=packet['free'];require(len(free)==len(set(free)),'duplicate free port')
 known=set(free);producers={};degrees={n:(0 if n in packet['fixed_numerals'] else 1) for n in free}
 for row in source:
  require(type(row) is list and len(row)==4,'row shape');n,op,a,b=row
  require(type(n) is str and n not in known and op in ['+','-','*'],'definition')
  for v in [a,b]: require(type(v) is int or type(v) is str and v in known,'unknown operand')
  ds=[0 if type(v) is int else degrees[v] for v in [a,b]]
  degrees[n]=sum(ds) if op=='*' else max(ds);producers[n]=row;known.add(n)
 live={packet['output']};stack=[packet['output']]
 while stack:
  n=stack.pop()
  if n in producers:
   for v in producers[n][2:]:
    if type(v) is str and v not in live: live.add(v);stack.append(v)
 require(set(producers)<=live and set(free)<=live,'dead row or free port')
 M=sum(r[1]=='*' for r in source);A=len(source)-M
 return {'M':M,'A':A,'total':len(source),'core_M':M-5,'core_A':A-1,'core_total':len(source)-6,'finalizer_M':5,'finalizer_A':1,'finalizer_total':6},degrees[packet['output']]

def build(data):
 parent=read_json(data['complete84_scaled_strong_output.json']);p=parent['packet']
 require(parent['source_sha256']==PINS['complete84_scaled_strong_output.py'],'parent self hash')
 scout=read_json(data['first_index_quotient_deletion_scout.json'])
 require(scout['source_sha256']==PINS['first_index_quotient_deletion_scout.py'],'scout self hash')
 old=next(f for f in scout['forms'] if f['parent']=='complete85_auxiliary_bezout_projection.json')
 pm=rows_map(p['source'])
 expected={
  'hpm1':['hpm1','*','h','UM'],
  'index_difference':['index_difference','-','R10b','hpm1'],
  'norm_index':['norm_index','-','index_difference','r_lhs'],
  'norm_product':['norm_product','*','norm_four','norm_index'],
  'all_units':['all_units','*','norm_product','norm_transport']}
 for n,row in expected.items():require(pm[n]==row,'parent cut '+n)
 consumers={n:[r[0] for r in p['source'] if n in r[2:]] for n in ['h']+REMOVED}
 require(consumers=={'h':['hpm1'],'hpm1':['index_difference'],'index_difference':['norm_index'],'norm_index':['norm_product'],'norm_product':['all_units']},'consumer closure')
 source=[copy.deepcopy(r) for r in p['source'] if r[0] not in REMOVED]
 for r in source:
  if r[0]=='all_units':r[2]='norm_four'
 packet={'source':source,'free':[v for v in p['free'] if v!='h'],'witnesses':[v for v in p['witnesses'] if v!='h'],'fixed_numerals':copy.deepcopy(p['fixed_numerals']),'ordinary_input':'x','witness_domain':'strictly positive integers','output':'polynomial','factors':FACTORS,'factor_values_on_constructed_zeros':[1,1,1,1,1,'A'],'factor_exact_degrees':[22,18,32,60,2,46],'exact_degree':180,'scope':'Rejected first-index deletion; all positive ordinary inputs admitted for every inherited authentic fixed-program numeral tuple. Not a universal bound.'}
 packet['ledger'],packet['gate_upper_degree']=inspect(packet)
 require(packet['ledger']['total']==80 and packet['ledger']['M']==45 and packet['ledger']['A']==35,'ledger')
 require(packet['gate_upper_degree']==190 and len(packet['witnesses'])==17,'interface/upper')
 require(packet['free']==old['free'] and packet['witnesses']==old['witnesses'],'old81 interface')
 om=rows_map(old['source']);cm=rows_map(source)
 require(set(om)-set(cm)=={'ic2','ic22','strong_difference'},'old private cone')
 require(set(cm)-set(om)=={'aux_coefficient_root','scaled_f_square'},'new private cone')
 changed={'R16','norm_strong','polynomial'}
 retained=set(cm)&set(om)-changed
 for n in retained:require(cm[n]==om[n],'old81 retained row '+n)
 exact_rows={
  'ic2':['ic2','*','i','c2'],'ic22':['ic22','*','ic2','ic2'],
  'strong_difference':['strong_difference','*','A','ic22'],
  'R16':['R16','*','A','strong_difference'],
  'norm_strong':['norm_strong','-','L16','strong_difference'],
  'polynomial':['polynomial','-','seven_units',1]}
 for n,r in exact_rows.items():require(om[n]==r,'old coefficient '+n)
 for n,r in {'c2':['c2','*','R10a','R10a'],'Ac2':['Ac2','*','A','c2'],'L16':['L16','*','f','f'],'aux_coefficient_root':['aux_coefficient_root','*','i','Ac2'],'R16':['R16','*','aux_coefficient_root','aux_coefficient_root'],'scaled_f_square':['scaled_f_square','*','A','L16'],'norm_strong':['norm_strong','-','scaled_f_square','R16'],'polynomial':['polynomial','-','seven_units','A']}.items():require(cm[n]==r,'new coefficient '+n)
 require([r for r in source if r[0] in ['norm_pair','norm_triple','norm_four','all_units','seven_units','polynomial']]==[
 ['norm_pair','*','norm_first','norm_main'],['norm_triple','*','norm_pair','norm_input'],['norm_four','*','norm_triple','norm_aux'],['all_units','*','norm_four','norm_transport'],['seven_units','*','all_units','norm_strong'],['polynomial','-','seven_units','A']],'full finalizer')
 return packet,p,old,{'removed':REMOVED,'removed_private_consumers':consumers,'rows_retained_literally_from84':79,'rows_retained_literally_from81':len(retained),'identities':['F80=A*F81','F84+A=(F80+A)*norm_index'],'proof':'Literal common producer induction, authenticated squared-coefficient identity (i*A*c^2)^2=A^2*(i*c^2)^2, scaled strong identity, and entire displayed six-factor finalizer.'}

def evaluate(source,values):
 env=dict(values)
 for n,op,a,b in source:
  av=a if type(a) is int else env[a];bv=b if type(b) is int else env[b]
  env[n]=av*bv if op=='*' else av+bv if op=='+' else av-bv
 return env

def numeric(packet,parent,old):
 rng=random.Random(20261003);same=0
 retained=[n for n in rows_map(packet['source']) if n not in ['all_units','seven_units','polynomial']]
 for j in range(48):
  vals={v:Fraction(rng.randrange(-3,5),rng.randrange(1,5)) if j>=24 else rng.randrange(-3,5) for v in parent['free']}
  a=evaluate(parent['source'],vals);b=evaluate(packet['source'],vals);c=evaluate(old['source'],vals)
  require(b['polynomial']==b['A']*c['polynomial'],'whole output scale')
  require(a['polynomial']+a['A']==(b['polynomial']+b['A'])*a['norm_index'],'whole index correction')
  for n in retained:require(a[n]==b[n],'retained84 value');same+=1
 return {'complete_signed_assignments':48,'rational_assignments':24,'retained84_value_equalities':same,'scope':'Off-zero algebra diagnostics; not compiler histories or full positive counterexamples.'}

def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def padd(a,b,sgn,p):
 c=[0]*max(len(a),len(b))
 for i,x in enumerate(a):c[i]+=x
 for i,x in enumerate(b):c[i]+=sgn*x
 return trim([x%p for x in c])
def pmul(a,b,p):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%p
 return trim(c)
def poly_eval(source,ports,p):
 env=dict(ports)
 for n,op,a,b in source:
  av=[a%p] if type(a) is int else env[a];bv=[b%p] if type(b) is int else env[b]
  env[n]=pmul(av,bv,p) if op=='*' else padd(av,bv,1 if op=='+' else -1,p)
 return env

def degrees(packet,parent,old):
 out=[]
 for B,p in [(16,1000000007),(32,1000000009)]:
  nums=dict(zip(packet['fixed_numerals'],[B-1,7,8,5,2,B+3]))
  vals={v:([nums[v]] if v in nums else [0,1]) for v in parent['free']}
  a=poly_eval(parent['source'],vals,p);b=poly_eval(packet['source'],vals,p);c=poly_eval(old['source'],vals,p)
  require(b['polynomial']==pmul(b['A'],c['polynomial'],p),'dense scale identity')
  require(padd(a['polynomial'],a['A'],1,p)==pmul(padd(b['polynomial'],b['A'],1,p),a['norm_index'],p),'dense index identity')
  ds=[len(b[n])-1 for n in FACTORS];require(ds==packet['factor_exact_degrees'] and len(b['polynomial'])==181,'dense exact degrees')
  out.append({'B':B,'prime':p,'factor_degrees':ds,'output_degree':180,'leading_coefficient':b['polynomial'][-1],'all_coefficients_sha256':sha(json.dumps(b['polynomial'],separators=(',',':')).encode())})
 return {'uniform_exact_degree':180,'gate_upper_degree':190,'uniform_leader':'-32*Q^107*(rho+sigma)*delta^2*i^4*(eta+zeta)^13*w^17*s^30*Ttransport*T^2*f^2','nonzero_monomial':'Jrep^108*rho*delta^2*i^4*eta^13*w^17*s^30*transport_quotient*auxiliary_quotient^2*f^2','nonzero_coefficient':'32*Bm1^108','proof':'F84+A=(F80+A)*Nk; degree(Nk)=7 with leader -h*w*s*Q^4. Pinned uniform degree187 parent and integral-domain multiplication give degree180. A has degree12. Every supplied witness and x has degree1, fixed numerals degree0.','diagnostics':out,'diagnostic_scope':'Full coefficient executions on two noncompiler diagnostic numeral slices supplement, but do not replace, the uniform proof.'}

def pell(A,n):
 D=A*A-1
 x,y=1,0;u,v=A,1
 while n:
  if n&1:x,y=x*u+D*y*v,x*v+y*u
  u,v=u*u+D*v*v,2*u*v;n//=2
 return x,y
def hx(n):return sha(('-' if n<0 else '+').encode()+hex(abs(n)).encode())
def factor_small(n):
 out=[];p=2
 while p*p<=n:
  if n%p==0:
   e=0
   while n%p==0:n//=p;e+=1
   out.append((p,e))
  p+=1
 if n>1:out.append((n,1))
 return out

def factorial_checks():
 rows=[]
 for L in range(8,33,2):
  t=math.factorial(L);aa=(t&-t).bit_length()-1;m=t>>aa
  for r in range(3,L+1,2):
   if len(factor_small(r))==1 and factor_small(r)[0]==(r,1):
    v=0;j=r
    while j<=L:v+=L//j;j*=r
    require(t%(r**(v-1)*(r-1))==0,'factorial Euler divisor')
  require(pow(2,t,m)==1,'factorial odd modulus')
  for d in [4,5]:
   require(t%d==0,'toy d divisibility');B=2**d
   q0=pow(2,t,t*(B-1));require((q0-1)%(B-1)==0,'repunit modular quotient')
   J=(q0-1)//(B-1);q=q0%t;MC=2;MF=B+3;M=(MC+q*MF)*J%t
   e0=M%m;e=next(e0+j*m for j in range(4) if (e0+j*m)%4==3)
   Z=(e-M)%(2**aa) or 2**aa
   W=pow(2,3,t);C=W+Z;F=(7+pow(2,e,t))*C
   R=((q*q-Z-q*F)*(q*q-1)+M)%t
   require(3<=e<4*m<=t//4 and Z%4==1 and R==e%t,'factorial CRT')
   rows.append({'L':L,'d':d,'v2_factorial':aa,'e':e,'Z':Z,'R_mod_t':R})
 sums=[]
 for d in [4,5,8,10,25]:
  for N in [1100,2200,3300]:
   B=pow(2,d,55);v=1;J=0
   for _ in range(N):J=(J+v)%55;v=v*B%55
   require(v==1 and J==0,'55-period grouped sum');sums.append([d,N,v,J])
 require(all(2*t*t+2*t*2**(t//4)+4*t<2**t for t in range(64,513,4)),'margin finite diagnostics')
 return {'factorial_crt_cases':rows,'period55_cases':sums,'margin_samples':113,'scope':'Small factorial and modular component examples only; L is not claimed to satisfy the actual giant recipe lower bound. The general inequalities and divisibility are proved in the note.'}

def pell_checks():
 ratios=[]
 for u in [1,5,9]:
  p,n=55*u,40*u;X=2**p;Y=2**(33*u-1);E=X*Y;a=Y*(X+1);A=a+2;Delta=A*A-1;H=4*a+3;P=2*X*Y*Y+1
  D,c=pell(A,p);tau,z=pell(P,n);k=2*z
  require(D*D-Delta*c*c==1 and tau*tau-X*Y*Y*(X*Y*Y+1)*k*k==1,'first/main norms')
  eta=c-k*Y;zeta=k-eta;require(eta>0 and zeta>0,'strict scaled ratio')
  require((D-a*c-X)%H==0,'main projection');gamma=(D-a*c-X)//H
  require((k-p-1)%E==25*u-1 and k>p+1,'missing index remainder')
  input_rows=[]
  for I in [3,5,9]:
   mu,kappa=pell(A,I);W=2**I
   require((kappa-I)%Delta==0 and (mu-a*kappa-W)%H==0,'input quotients')
   delta=(kappa-I)//Delta;rho=(mu-a*kappa-W)//H;sigma=gamma-rho
   require(min(delta,rho,sigma)>0,'shared input positivity');input_rows.append({'I':I,'delta_bits':delta.bit_length(),'rho_bits':rho.bit_length(),'sigma_bits':sigma.bit_length()})
  ratios.append({'u':u,'p':p,'n':n,'c_bits':c.bit_length(),'c_sha256_hex':hx(c),'eta_positive':True,'zeta_positive':True,'inverse_remainder':25*u-1,'input_components':input_rows})
 aux=[]
 for A,p in [(2,3),(3,3),(2,7)]:
  Delta=A*A-1;D,c=pell(A,p);m=2*c*p;f,psi=pell(A,m)
  require(psi%(c*c)==0,'aux c-square rank');i=psi//(c*c);S=Delta*psi
  Vnum,y=pell(S,p);require(Vnum%S==0,'odd quotient');V=Vnum//S
  require((V+c)%f==0 and (V+p)%c==0,'aux minus congruences')
  o=(V+c)//f;j=(V+p)//c;require((o+p*f)%c==0,'T integrality');T=(o+p*f)//c
  require(min(i,S,V,y,o,j,T)>0 and S>c*c and V>c>p,'aux positivity')
  require(c*(T*f-1)-p*f*f==V,'actual auxiliary quotient')
  require(Delta*f*f-S*S==Delta and S*S*(V*V-y*y)+y*y==1,'scaled strong and auxiliary')
  aux.append({'A_parameter':A,'p':p,'c':c,'m_aux':m,'f_bits':f.bit_length(),'T_bits':T.bit_length(),'V_bits':V.bit_length(),'T_sha256_hex':hx(T),'strong_value':'Delta','aux_value':1})
 recurrence=0
 for A in [2,3,5,12]:
  a=A-2;H=4*a+3;g0,g1=0,0
  for j in range(2,20):
   gj=2*A*g1-g0+2**(j-2);chi,psi=pell(A,j)
   require(chi-a*psi-2**j==H*gj and gj>g1,'shared projection recurrence');g0,g1=g1,gj;recurrence+=1
 return {'ratio_and_input_components':ratios,'auxiliary_components':aux,'exact_projection_recurrence_cases':recurrence,'scope':'Exact bounded Pell subsystems, not a materialized factorial-radix full positive zero. Full all-input zero existence follows from the uniform construction in the note.'}

def run(root,archive):
 data,sizes,archive_size=authenticate(root,archive)
 packet,parent,old,structural=build(data)
 return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'parent_pins':copy.deepcopy(PINS),'archive':{'revision':REV,'path':ARCHIVE_PATH,'git_blob_oid_sha1':ARCHIVE_BLOB,'sha256':ARCHIVE_SHA,'size':archive_size,'read_member_sha256':copy.deepcopy(MEMBERS),'read_member_sizes':sizes,'code_executed':False},'packet':packet,'structural':structural,'numeric':numeric(packet,parent,old),'degree':degrees(packet,parent,old),'factorial_and_crt':factorial_checks(),'pell_components':pell_checks(),'theorem':'For every authentic inherited fixed-program numeral tuple and every x>0, this 80-operation candidate has a strictly positive integer zero. Its ordinary-input relation is all positive integers; no new universal bound.','evidence_boundary':'No enormous factorial-radix full tuple is materialized. Full source and all-value identities are checked independently of the mathematical all-input construction; finite number-theoretic tests are supplements.'}

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--archive',type=Path)
 out=ap.add_mutually_exclusive_group(required=True);out.add_argument('--output',type=Path);out.add_argument('--expect',type=Path);args=ap.parse_args()
 result=run(args.root,args.archive)
 if args.expect:require(exact(result,read_json(args.expect.read_bytes())),'receipt mismatch')
 else:args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':'PASS','gates':80,'M':45,'A':35,'positive_witnesses':17,'exact_degree':180,'claim':'rejected candidate; all-input collapse'}))
if __name__=='__main__':main()
