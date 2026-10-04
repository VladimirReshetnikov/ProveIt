#!/usr/bin/env python3
"""Fresh independent congruence and inert-source review; never runs parent code."""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from math import gcd
from pathlib import Path

ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs')
STEM='complete83_nondyadic_outer_family'
AUTHOR_PINS={'py':'b877f02e65bd0f033cec01c46cab8a356c08829c4e5f54e8b322ce3feae8111f','json':'8041d3661c0cfc9c29ca25c99d08567e45a2ceed3dbca29caf22b792a8c97dd1','md':'42281ee2c1cf99851d4fe67fcfe6f61322fd721d8ebd8ec539983a6edcc44d23'}
WIP=Path('Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
SOURCE=WIP/'complete83_shared_projection_scout.json'

def ck(b,s):
 if not b:raise RuntimeError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def vp(x,p):
 ck(x>0,'positive valuation input');n=0
 while x%p==0:x//=p;n+=1
 return n

def source_check(packet):
 src=packet['source'];defs={r[0]:r for r in src}
 ck(len(src)==len(defs)==83,'source length/uniqueness')
 ck(Counter(r[1] for r in src)==Counter({'*':46,'+':20,'-':17}),'literal ledger')
 expected=[
 ['repunit','*','Bm1','Jrep'],['q','+','repunit',1],['Lbig','*','q','q'],['n2','*','Lbig','q'],
 ['wn2','*','w','q'],['sn2','*','s','n2'],['UM','*','wn2','sn2'],
 ['R10b','+','eta','zeta'],['ksn2','*','R10b','sn2'],['R10a','+','ksn2','eta'],['R12','+','UM','sn2'],
 ['cam2','*','R10a','R12'],['D1','+','wn2','cam2'],['a4','*',4,'R12'],['a4m5','+','a4',3],
 ['gam','*','sigma','a4m5'],['shared_main_partial','+','D1','shared_projection'],['R14','+','shared_main_partial','gam'],
 ['q_minus_F','-','q','F'],['q_minus_FZ','-','q_minus_F','Z'],['C_after_alpha','-','q_minus_FZ','alpha'],
 ['scaled_t','*','twice_cell_bits','x'],['marked_rhs','-','C_after_alpha','scaled_t'],['W','-','marked_rhs','Z'],
 ['odd_index','+','scaled_t','inner_bits'],['index_product','*','delta','A'],['index_rhs','+','odd_index','index_product'],
 ['difference_multiple','*','index_rhs','R12'],['exponent_partial','+','W','difference_multiple'],['exponent_rhs','+','exponent_partial','shared_projection'],
 ['hpm1','*','h','UM'],['index_difference','-','R10b','hpm1'],['gap_product','*','repunit','q_minus_F'],
 ['gap','+','gap_product','q_minus_FZ'],['Lm1','-','Lbig',1],['rproduct','*','gap','Lm1'],
 ['qMF','*','q','MF'],['mask_factor','+','MC','qMF'],['mask','*','mask_factor','Jrep'],['r_lhs','+','rproduct','mask'],
 ['norm_index','-','index_difference','r_lhs'],['kinner','+','Kconstant','w'],['innerC','*','kinner','marked_rhs'],
 ['transport_partial','+','innerC','q_minus_F'],['local_rhs','*','transport_quotient','repunit'],['norm_transport','-','transport_partial','local_rhs'],
 ['L16','*','f','f'],['auxiliary_Tf','*','auxiliary_quotient','f'],['auxiliary_Tf_minus_one','-','auxiliary_Tf',1],
 ['auxiliary_c_Tf','*','R10a','auxiliary_Tf_minus_one'],['auxiliary_R_f2','*','r_lhs','L16'],['aux_u_rhs','-','auxiliary_c_Tf','auxiliary_R_f2'],
 ['H2','*','aux_u_rhs','aux_u_rhs'],['aux_square_gap','-','H2','aux_y2'],['aux_coefficient_root','*','i','Ac2'],
 ['R16','*','aux_coefficient_root','aux_coefficient_root'],['scaled_f_square','*','A','L16'],['norm_strong','-','scaled_f_square','R16'],
 ['L17','*','R16','aux_square_gap'],['norm_aux','+','L17','aux_y2'],
 ['norm_four','*','norm_triple','norm_aux'],['norm_product','*','norm_four','norm_index'],
 ['all_units','*','norm_product','norm_transport'],['seven_units','*','all_units','norm_strong'],['polynomial','-','seven_units','A']]
 for row in expected:ck(defs[row[0]]==row,'literal source boundary '+row[0])
 witnesses=['Jrep','F','alpha','transport_quotient','f','h','i','auxiliary_quotient','s','w','tau_root','eta','zeta','y_aux','Z','delta','shared_projection','sigma']
 ck(packet['witnesses']==witnesses,'18 witnesses')
 fixed=['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF'];ck(packet['fixed_numerals']==fixed,'six fixed ports')
 ck(packet['free']==witnesses+['x']+fixed,'all free ports')
 available=set(packet['free'])
 for name,op,a,b in src:
  ck(all(not isinstance(t,str) or t in available for t in (a,b)),'topology');available.add(name)
 live=set()
 def visit(x):
  if not isinstance(x,str) or x not in defs or x in live:return
  live.add(x)
  for y in defs[x][2:]:visit(y)
 visit(packet['output']);ck(len(live)==83,'all source producers live')
 return {'literal_rows':expected,'guarded_rows':len(expected),'source_rows':83,'witnesses':witnesses,'fixed_numerals':fixed,'all_live':True,'source_executed':False}

def verify_case(d,b,n,K,MC,MF0,expected=None):
 B=2**d;D=d*n;Q=2**D
 ck(d in (25,125) and b in (5,25) and n%4==1,'synthetic domain')
 shape='minus' if K%5==3 else 'plus'
 q=Q*(2*Q-1) if shape=='minus' else Q*(Q+1)//2
 J,rem=divmod(q-1,B-1);ck(rem==0,'repunit exact')
 ck(J==((Q-1)//(B-1))*(2*Q+1 if shape=='minus' else Q//2+1),'repunit factorization')
 T=n*(D+1 if shape=='minus' else D-1)
 mf=MF0+B-1
 A=q*q*(q*q-1)+(MC+q*mf)*J;G=(1+q*K)*(q*q-1)
 if shape=='minus':ck([vp(J,5),vp(q*q-1,5),vp(G,5)]==[1,1,1] and A%5==b%5==0,'five-adic minus branch')
 else:ck(G%5!=0,'five-adic plus unit')
 candidates=[z for z in range(1,4*d+1,4) if (A-G*z-b)%(2*d)==0]
 ck(len(candidates)==(5 if shape=='minus' else 1),'CRT solution multiplicity')
 z=min(candidates);R=A-G*z
 # Independently scan the finite specified input interval, avoiding author inverse/CRT code.
 choices=[x for x in range(n,n+T) if (R-(2*d*x+b))%(2*d*T)==0]
 ck(len(choices)==1,'unique interval input');x=choices[0];u=2*d*x+b
 F=K*z;alpha=q-F-2*z-2*d*x
 ck(z%4==1 and z<=4*d and (shape!='minus' or z<=4*d//5),'small z')
 ck(q%4==0 and J%4==1 and R%4==3,'literal parity')
 ck(vp(q,2)==D-(shape=='plus') and q&(q-1),'radix shape valuation')
 ck(4*alpha>q and n<=x<n+T and x<=n*(D+2),'positive slack/input')
 ck(0<u<2*q<R and 3*q+1<R and R+2<q**4,'completion bounds')
 ck(R<q**4-q**3 and q*q-z-q*F>3*q,'stronger index bounds')
 ck(q-F-z-alpha-2*d*x==z,'source C and W')
 ck((q-1)*(q-F)+(q-F-z)==q*q-z-q*F,'literal source gap identity')
 if shape=='plus':factors=[Q+1,Q-1,Q//2+1];orders=[2*D,D,2*(D-1)]
 else:factors=[2*Q-1,Q-1,2*Q+1];orders=[D+1,D,2*(D+1)]
 for j in range(3):
  ck(factors[j]%2==1 and pow(2,orders[j],factors[j])==1,'factor period')
  ck(2*d*T%orders[j]==0,'global period multiple')
  for k in range(j):ck(gcd(factors[j],factors[k])==1,'pairwise coprimality')
 odd_product=factors[0]*factors[1]*factors[2]
 ck(q*(q-1)==(1<<vp(q,2))*odd_product,'entire modulus decomposition')
 modulus=q*(q-1)
 ck((pow(2,R,modulus)-pow(2,u,modulus))%modulus==0,'X divisibility')
 ck(u>=2*D+b and u>vp(q,2),'X two-part')
 signature=sha(json.dumps([str(v) for v in [q,J,z,F,alpha,R,u]],separators=(',',':')).encode())
 if expected:
  ck(expected['shape']==shape and expected['z']==z and expected['x']==x and expected['u']==u,'saved scalar fields')
  ck(expected['outer_signature_sha256']==signature,'all saved outer scalars')
  ck([expected['q_bits'],expected['R_bits'],expected['alpha_bits'],expected['v2_q']]==[q.bit_length(),R.bit_length(),alpha.bit_length(),vp(q,2)],'saved size fields')
 return {'d':d,'b':b,'n':n,'K':str(K),'MC':MC,'MF0':MF0,'shape':shape,'z':z,'x':x,'u':u,'signature_sha256':signature,'synthetic_only':True}

def build(root,author_dir):
 pins=[]
 for ext,expected in AUTHOR_PINS.items():
  path=author_dir/(STEM+'.'+ext);b=path.read_bytes();ck(sha(b)==expected,'author pin')
  pins.append({'name':path.name,'bytes':len(b),'sha256':expected})
 author=json.loads((author_dir/(STEM+'.json')).read_text())
 ck(author['source_sha256']==AUTHOR_PINS['py'] and author['proof_sha256']==AUTHOR_PINS['md'],'author self binding')
 deps=[]
 for r in author['dependencies']:
  b=(root/r['logical_path']).read_bytes();ck(sha(b)==r['sha256'] and len(b)==r['bytes'],'dependency authentication')
  deps.append({'path':r['logical_path'],'bytes':len(b),'sha256':sha(b)})
 source=json.loads((root/SOURCE).read_text())['packet'];binding=source_check(source)
 cases=[]
 for case in author['finite_evidence']['cases']:
  cases.append(verify_case(case['d'],case['b'],case['n'],int(case['K']),case['MC'],case['native_MF'],case))
 ck(len(cases)==120,'saved case count')
 extras=[]
 for d,b,n in [(25,25,1),(25,5,13),(125,25,5)]:
  B=1<<d
  for residue in range(5):
   K=(B*(1<<(d//4))+B-3)//5*5+residue
   ck(K>0 and K+2<3*B*(1<<(d//4)),'near-bound synthetic K')
   extras.append(verify_case(d,b,n,K,2, B-2))
 margins=[]
 for d in range(25,501):
  ck((64*d)**4 < 2**(3*d) and 24*d*d<2**(2*d),'finite margins')
  margins.append(d)
 # Base cases and exact ratios establish the displayed integer induction tests.
 ck(26**4<8*25**4 and 26**2<4*25**2,'monotone ratio checks')
 # Symbolic layout coefficient vectors in M,a,const order.
 H=(51,3,1);T1=(105,4,2);T2=(159,4,3);g=(186,4,4);lower=(213,4,4)
 ck(tuple(T1[i]+(54,0,1)[i] for i in range(3))==T2,'T2 expansion')
 ck(tuple(T2[i]+(27,0,1)[i] for i in range(3))==g,'high monomial expansion')
 ck(tuple(g[i]+(27,0,0)[i] for i in range(3))==lower,'L bound expansion')
 ck(tuple(lower[i]-4*H[i] for i in range(3))==(9,-8,0),'quarter layout margin')
 return {'schema':'independent nondyadic actual-compiler outer-family review v1','source_sha256':sha(Path(__file__).read_bytes()),'author_pins':pins,'dependencies':deps,'source_binding':binding,'reconstructed_author_cases':cases,'additional_synthetic_cases':extras,'uniform_margins_tested':len(margins),'layout_vectors':{'H':H,'T1':T1,'T2':T2,'g':g,'L_lower':lower},'status':'PASS','scope':{'compiler_instances_materialized':False,'source_dag_executed':False,'cube_divisibility_tested':False,'full_Pell_zero_materialized':False,'conditional_completion_only':True,'predecessor_executed':False,'ordinary_input_arbitrarily_prescribed':False,'universal83_claim':False}}

def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=ROOT);p.add_argument('--author-dir',type=Path,default=Path('/tmp'));p.add_argument('--expect',type=Path);p.add_argument('--output',type=Path,default=Path('/tmp/review_complete83_nondyadic_outer_family.json'));a=p.parse_args()
 r=build(a.root,a.author_dir);raw=(json.dumps(r,sort_keys=True,indent=2)+'\n').encode()
 if a.expect:ck(raw==a.expect.read_bytes(),'exact replay')
 else:a.output.write_bytes(raw)
 print(json.dumps({'status':'PASS','saved_cases':len(r['reconstructed_author_cases']),'extra_cases':len(r['additional_synthetic_cases']),'guarded_source_rows':r['source_binding']['guarded_rows'],'receipt_sha256':sha(raw)}))
if __name__=='__main__':main()
