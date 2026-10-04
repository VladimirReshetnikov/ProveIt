#!/usr/bin/env python3
"""Fresh bounded evidence for the input-witness power gap; data-only parents."""
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

PINS={
 'complete83_input_quotient_dichotomy.py':'e8d6867d4f0a56ed0e60b01d3c1ab00913f13ac3db4ae351aa97a2ff710c5a04',
 'complete83_input_quotient_dichotomy.json':'d0173078b9ff772b7b05ab8b8b1ed543cfb698358ad88c85c1bf6dd6caffb89a',
 'complete83_input_quotient_dichotomy.md':'46d6457d10d1847cd4241aa1ed6705bf520216fc32cf97891c1f439f6c2c2505',
 'complete83_independent_gamma_scout.json':'ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20',
 'complete83_independent_gamma_scout.md':'bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41',
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf'}

def ck(ok,message):
 if not ok:raise ValueError(message)
def sha(data):return hashlib.sha256(data).hexdigest()
def enc(value):return json.dumps(value,sort_keys=True,separators=(',',':')).encode()
def read(path):
 def pairs(items):
  out={}
  for k,v in items:ck(k not in out,'duplicate JSON key');out[k]=v
  return out
 def bad(value):raise ValueError('nonfinite JSON '+value)
 return json.loads(path.read_text(),object_pairs_hook=pairs,parse_constant=bad)
def fingerprint(n):return {'bits':n.bit_length(),'hex_sha256':sha(hex(n).encode())}

def pell(A,n):
 """Independent binary multiplication in Z[sqrt(A*A-1)]."""
 D=A*A-1;x,y=1,0;b,c=A,1
 while n:
  if n&1:x,y=x*b+D*y*c,x*c+y*b
  b,c=b*b+D*c*c,2*b*c;n//=2
 return x,y

def source_audit(root):
 child=read(root/'complete83_independent_gamma_scout.json')['packet']
 parent=read(root/'complete84_scaled_strong_output.json')['packet']
 expected=[]
 for row in parent['source']:
  if row[0]=='gamma_sum':ck(row==['gamma_sum','+','rho','sigma'],'parent private addition');continue
  n,op,l,r=row;expected.append([n,op,'sigma' if l=='gamma_sum' else l,'sigma' if r=='gamma_sum' else r])
 ck(expected==child['source'],'complete 84 to 83 literal reconstruction')
 known=set(child['free']);deps={};counts=Counter()
 for n,op,l,r in child['source']:
  ck(n not in known and op in ['+','-','*'],'distinct valid row')
  ck(all(type(v)is int or v in known for v in [l,r]),'topology')
  known.add(n);deps[n]=(l,r);counts[op]+=1
 live=set();todo=[child['output']]
 while todo:
  x=todo.pop()
  if type(x)is str and x not in live:live.add(x);todo.extend(deps.get(x,()))
 ck(live==known,'full row and port liveness')
 cuts=[['R10a','+','ksn2','eta'],['R12','+','UM','sn2'],
       ['a4','*',4,'R12'],['a4m5','+','a4',3],['a_square','*','R12','R12'],
       ['A','+','a_square','a4m5'],['gam','*','sigma','a4m5'],
       ['R14','+','D1','gam'],['W','-','marked_rhs','Z'],
       ['odd_index','+','scaled_t','inner_bits'],['index_product','*','delta','A'],
       ['index_rhs','+','odd_index','index_product'],['difference_multiple','*','index_rhs','R12'],
       ['exponent_partial','+','W','difference_multiple'],['modulus_multiple','*','rho','a4m5'],
       ['exponent_rhs','+','exponent_partial','modulus_multiple'],
       ['mu2','*','exponent_rhs','exponent_rhs'],['kappa2','*','index_rhs','index_rhs'],
       ['scaled_kappa2','*','A','kappa2'],['norm_input','-','mu2','scaled_kappa2']]
 actual={r[0]:r for r in child['source']}
 for row in cuts:ck(actual[row[0]]==row,'literal boundary '+row[0])
 ck((len(child['source']),counts['*'],counts['+']+counts['-'],len(child['witnesses']))==(83,47,36,18),'unchanged complete ledger')
 return {'canonical_packet_sha256':sha(enc(child)),'literal_cuts':cuts,'complete_rows':83,
         'free_ports':len(child['free']),'witnesses':18,'M':47,'A':36,'all_live':True,'source_changed':False}

def components():
 out=[];comparisons=0
 for R in [7,11]:
  for offset in [2,8,14]:
   A=2**R+offset;Delta=A*A-1;H=4*A-5;D,c=pell(A,R);ER=D-(A-2)*c
   D3,c3=pell(A,3*R);E3=D3-(A-2)*c3
   ck(c3==4*Delta*c**3+3*c and E3==(4*Delta*c*c+3)*ER-2*D,'exact triple-angle identities')
   for u in [3,5]:
    q=2**u+1;m=A*u//R;bound=c**(m-1)
    ck(R>=7 and A>2**R and 3<=u<R and u%2 and q<A,'component inequalities')
    ck(c>max(Delta,H+q,u) and m>=55 and 2*Delta>A*u,'native consequences in relaxed component')
    Du,cu=pell(A,u);Eu=Du-(A-2)*cu
    ck((cu-u)%Delta==0 and (Eu-2**u)%H==0 and (ER-2**R)%H==0,'canonical component congruences')
    delta=(cu-u)//Delta;rho=(Eu-2**u)//H;gamma=(ER-2**R)//H
    ck(delta>0 and Delta*delta<c and 0<rho<gamma<c,'canonical small box')
    _,cm=pell(A,m*R);ck(cm>c**m,'Pell block growth')
    rows=[]
    for v in [A*u,A*u+2,A*u+2*R]:
     Dv,cv=pell(A,v);Ev=Dv-(A-2)*cv
     ck(cv>=cm and Ev>cv,'monotone coefficient and E')
     ck(cv-u>Delta*bound,'delta lower bound without division')
     numerators=[]
     for W in [1-q,0,q-1]:
      ck(Ev-W>H*bound,'rho lower bound without division');comparisons+=1
      numerators.append(fingerprint(Ev-W))
     rows.append({'v':v,'psi':fingerprint(cv),'rho_numerators':numerators})
    out.append({'A':A,'R':R,'u':u,'q':q,'m':m,'c':fingerprint(c),
                'canonical_delta':fingerprint(delta),'canonical_rho':fingerprint(rho),
                'power_bound':fingerprint(bound),'large_index_checks':rows})
 return {'scope':'Relaxed Pell components, not half-binomial histories or full compiler zeros. Large-index comparisons are numerator inequalities and do not assert H-integrality.',
         'models':out,'rho_numerator_comparisons':comparisons,'delta_numerator_comparisons':3*len(out)}

def run(root):
 for n,h in PINS.items():ck(sha((root/n).read_bytes())==h,'pin '+n)
 floor_checks=[]
 for R in range(7,81):
  A=2**R+1;m=3*A//R
  ck(m>=55 and (R-1)*2**R-1>0,'uniform monotone floor')
  floor_checks.append([R,m])
 return {'schema':'complete83-input-witness-power-gap-v1','source_sha256':sha(Path(__file__).read_bytes()),
         'pins':PINS,'source_audit':source_audit(root),'components':components(),'floor_checks':floor_checks,
         'theorem':{'canonical':'0<delta<c/Delta and 0<rho<gamma<c',
                    'noncanonical':'delta>c^(floor(A*u/R)-1) and rho>c^(floor(A*u/R)-1), floor(A*u/R)>=55',
                    'language_status':'unresolved','new_circuit':False,'power_is_paid_operation':False},
         'full_compiler_zeros_materialized':False,'predecessor_code_executed':False}

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True)
 group=ap.add_mutually_exclusive_group(required=True);group.add_argument('--output',type=Path);group.add_argument('--expect',type=Path)
 args=ap.parse_args();result=run(args.root)
 if args.output:args.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else:ck(enc(result)==enc(read(args.expect)),'exact type-sensitive receipt')
 print('PASS: unchanged complete83; twelve relaxed Pell models; uniform54th-power separation')
