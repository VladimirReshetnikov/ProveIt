#!/usr/bin/env python3
"""Standalone inert-data compiler audit; no predecessor imports or execution."""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path

PINS = {
 'group_projective_general_separate_range.py':'7da26e02d657f53fc6f27977d92065f15a5769533e27489d73ecd810c327f49c',
 'group_projective_general_separate_range.json':'23c18690cb114bfc4a0290b89383a4922ac3d32f55aa4b8dc60d05db5840ae2f',
 'group_projective_general_separate_range.md':'2e0744fd1aad96cc3a1e94ad47237e3c81f2d73705dca72998daf422cf2c3614',
 'group_projective_tail_quotient_shift.md':'a1e1e67df618f6f809c2e85a409509b288337f62cd1af35cfc6ca950e0efa92a',
 'group_projective_unit_top_mask.md':'e0898d1fc20f2f4c1abff21d33f90382aeac4f6b24c648624f0e54d59a3619b2',
 'group_range_projective_compiler.md':'2c71f229f791a12c63d701adcfe56dcfe44601e124566562fc67aeb8a2398f2f',
 'group_regular_macro_controller.md':'91d8932360bdc998811c5727c983602d37edc9943fab0114f00532a6bba49ec5',
 'matrix193_synchronized_rows.md':'ab768aa392841add5dc6dfcd8ed62564ca17fae2fe80e5ec39f1f4ceb36559d2',
 'matrix193_synchronized_rows.json':'9ce8537fc12bff3a2d3d91297d65a47ee6a7af193ff4bb08f474216260ef4233',
 'matrix193_context_absorption.md':'d7492809ba00a011c8280172bb016f96f3f6c240de6a823ed717d82bda5e4f4b',
 'matrix193_context_absorption.json':'73f8cae212c6c1917e73cc76c7bf3c43b8c587748bbf4327eddf4c82e726a436',
 'matrix193_gamma1_recode.md':'6349644283548af96f4a9582ee32d959a123c81bf1c2f902c45874ae45c96742',
 'u15_unary_block_interface.md':'cdc686700af3545609796034e0a2c906bd0438b6bcabc0c0b267954cc9d20452',
}
CUTS=['selection__q','selection__padded_A','selection__padded_B','selection__F3','selection__Zglobal','controller__geometry_power']
NATIVE=['selection__f','selection__h','selection__i','selection__j','selection__o','selection__w','selection__tau_gap','selection__eta','selection__zeta','selection__ga','selection__y_aux','selection__odd_half']
EDGES=[{'source':0,'target':0,'label':8,'role':'LOAD'}, {'source':0,'target':1,'label':0,'role':'SWITCH'}, {'source':1,'target':1,'label':4,'role':'TILE'}, {'source':1,'target':1,'label':0,'role':'IDLE'}]

def need(b,s):
 if not b: raise ValueError(s)
def sha(b): return hashlib.sha256(b).hexdigest()
def obj(pairs):
 d={}
 for k,v in pairs:
  need(k not in d,'duplicate JSON key: '+k); d[k]=v
 return d
def loads(b): return json.loads(b,object_pairs_hook=obj)
def exact(a,b):
 if type(a) is not type(b): return False
 if isinstance(a,dict): return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def native_rows(parent):
 rows=parent['source']; by={r[0]:r for r in rows}; used=set()
 def walk(x):
  if not isinstance(x,str) or x in CUTS or x not in by or x in used:return
  used.add(x)
  for y in by[x][2:]:walk(y)
 walk('eight_units')
 ret=[r for r in rows if r[0] in used]
 need(len(ret)==63,'native cone changed')
 boundary=set(x for r in ret for x in r[2:] if isinstance(x,str) and x not in used)
 need(boundary==set(CUTS+NATIVE),'native boundary')
 return ret

class Build:
 def __init__(self):self.rows=[];self.memo={}
 def gate(self,op,a,b,name=None):
  if type(a) is int and type(b) is int:return a+b if op=='+' else a-b if op=='-' else a*b
  if op=='+' and a==0:return b
  if op=='+' and b==0:return a
  if op=='-' and b==0:return a
  if op=='*' and (a==0 or b==0):return 0
  if op=='*' and a==1:return b
  if op=='*' and b==1:return a
  key=(op,a,b)
  if key in self.memo:return self.memo[key]
  n=name or 'g'+str(len(self.rows));self.rows.append([n,op,a,b]);self.memo[key]=n;return n
 def add(self,a,b,name=None):return self.gate('+',a,b,name)
 def sub(self,a,b,name=None):return self.gate('-',a,b,name)
 def mul(self,a,b,name=None):return self.gate('*',a,b,name)
 def sum(self,vs):
  t=0
  for v in vs:t=self.add(t,v)
  return t
 def horner(self,vs,p):
  t=0
  for v in reversed(vs):t=self.add(v,self.mul(p,t))
  return t

def emit(nr):
 b=Build(); ports={}; stage={}
 free=['x','height_slack']+['H'+str(i) for i in range(4)]+['Zhat3','Zhat7','bound_global']+['edge_hat'+str(i) for i in range(4)]+['F_even','F_odd','population_quotient']+NATIVE
 D=b.add(b.add('x',8),'height_slack','D');c=b.sub(D,1,'c0');B=b.mul(16,D,'B');bm=b.sub(B,1,'Bminus')
 E=[b.sub('edge_hat'+str(i),1) for i in range(4)]
 J=b.sum(E);P=b.add(b.mul(bm,J),1,'P')
 P2=b.mul(P,P);P4=b.mul(P2,P2);P8=b.mul(P4,P4)
 R8=b.mul(b.mul(b.add(P,1),b.add(P2,1)),b.add(P4,1));O=b.mul(J,R8)
 C=b.horner(E,P);P3=b.mul(P2,P);P7=b.mul(P3,P4)
 S=b.add(b.mul(E[2],P3),b.mul(E[0],P7))
 Z3=b.sub('Zhat3',1);Z7=b.sub('Zhat7',1)
 Zb=b.add(b.mul(Z3,P3),b.mul(Z7,P7))
 Hb=b.mul(b.add(P,1),b.horner(['H1','H0','H3','H2'],P2))
 Mb=b.mul(bm,S);T=b.mul(P8,P8);T2=b.mul(T,P8)
 M8=b.mul(b.add(D,c),O);Cs=b.mul(P8,C);Hs=b.mul(T,Hb)
 H=b.add(b.add(b.add(Hb,Cs),Hs),b.mul(B,T2))
 M=b.add(b.add(b.add(Mb,b.mul(P8,O)),b.mul(T,M8)),T2)
 Z=b.add(b.add(Zb,Cs),Hs)
 q=b.mul(32,b.mul(B,T2))
 padA=b.add(b.mul(16,H),13);padB=b.add(b.mul(16,M),10);F3=b.add(b.mul(16,Z),8)
 glob=b.add(b.add(b.sum(['H0','H1','H2','H3','Zhat3','Zhat7']),6),'bound_global')
 cuts=dict(zip(CUTS,[q,padA,padB,F3,glob,P]))
 ports.update(D=D,c0=c,B=B,bminus=bm,J=J,P=P,P2=P2,P4=P4,P8=P8,R8=R8,O=O,C=C,S=S,Zb=Zb,Hb=Hb,Mb=Mb,T=T,T2=T2,M8=M8,H=H,M=M,Z=Z,q=q,padA=padA,padB=padB,F3=F3,global_bound_sum=glob)
 ports['edge_values']=E
 stage['packing']=len(b.rows)
 # Every native instruction is preserved, with only the declared cut names redirected.
 for name,op,a,d in nr:
  b.rows.append([name,op,cuts.get(a,a),cuts.get(d,d)])
 stage['native']=len(b.rows)-stage['packing']
 residuals=[]
 rhsbase=[b.sub(b.mul('F_even',P),D),b.sub(b.mul('F_odd',P),c)]
 deltas=[0,b.sub(b.mul(c,E[2]),Z3),0,b.sub(b.mul(c,E[0]),Z7)]
 for i in range(4):
  lhs=b.mul(B,b.add('H'+str(i),deltas[i]));rhs=b.add('H'+str(i),rhsbase[i%2]);residuals.append([lhs,rhs])
 flowA=b.add(E[2],E[3]);flowT=b.add(E[1],flowA)
 residuals.append([b.add(flowA,P),b.mul(B,flowT)])
 countR=b.sub(b.sub(b.add('edge_hat0',bm),'x'),1)
 residuals.append([b.mul(bm,'population_quotient'),countR])
 stage['outer_producers']=len(b.rows)-stage['packing']-stage['native']
 squares=[]
 for a,d in residuals:
  r=b.sub(a,d);squares.append(b.mul(r,r))
 out=b.sub(b.mul('eight_units',b.add(1,b.sum(squares))),1,'output')
 stage['finalizer']=len(b.rows)-sum(stage.values())
 return {'free':free,'witnesses':[x for x in free if x!='x'],'ordinary_input':'x','ordinary_domain':'nonnegative integers (positive-input restriction also valid)','witness_domain':'strictly positive integers','source':b.rows,'output':out,'ports':ports,'native_cut_bindings':cuts,'outer_comparisons':residuals,'stage_counts':stage,'controller_edges':EDGES,'m':8,'initial_signed_coordinates':[1,0,1,0],'Hfix':8}

def audit(packet):
 known=set(packet['free']);by={};degree={x:1 for x in known}
 for n,op,a,b in packet['source']:
  need(n not in known and op in ('+','-','*'),'invalid/repeated row')
  for x in (a,b):need(type(x) is int or isinstance(x,str) and x in known,'unclosed row '+n)
  da=degree.get(a,0);db=degree.get(b,0);degree[n]=da+db if op=='*' else max(da,db)
  by[n]=[a,b];known.add(n)
 live=set()
 def visit(x):
  if not isinstance(x,str) or x in live:return
  live.add(x)
  for y in by.get(x,[]):visit(y)
 visit(packet['output']);need(set(by)<=live,'dead paid row');need(set(packet['free'])<=live,'dead free port')
 ops=Counter(r[1] for r in packet['source'])
 return {'gates':len(by),'M':ops['*'],'A':ops['+']+ops['-'],'positive_witnesses':len(packet['witnesses']),'all_paid_rows_live':True,'all_free_ports_live':True,'naive_degree_upper_bound':degree[packet['output']]}

def evaluate(rows,v,mod=None):
 e=dict(v)
 def g(x):return x if type(x) is int else e[x]
 for n,op,a,b in rows:
  a=g(a);b=g(b);z=a+b if op=='+' else a-b if op=='-' else a*b;e[n]=z if mod is None else z%mod
 return e

def direct(v):
 x=v['x'];D=x+8+v['height_slack'];c=D-1;B=16*D;bm=B-1
 E=[v['edge_hat'+str(i)]-1 for i in range(4)];J=sum(E);P=bm*J+1
 Hs=[v['H'+str(i)] for i in range(4)];Zh=[v['Zhat3']-1,v['Zhat7']-1]
 C=sum(E[i]*P**i for i in range(4));R8=sum(P**i for i in range(8));O=J*R8
 S=E[2]*P**3+E[0]*P**7;Zb=Zh[0]*P**3+Zh[1]*P**7
 Hb=sum(Hs[j]*P**i for i,j in enumerate([1,1,0,0,3,3,2,2]));Mb=bm*S;T=P**16;T2=P**24;M8=(2*D-1)*O
 H=Hb+P**8*C+T*Hb+B*T2;M=Mb+P**8*O+T*M8+T2;Z=Zb+P**8*C+T*Hb;q=32*B*T2
 glob=sum(Hs)+v['Zhat3']+v['Zhat7']+6+v['bound_global']
 eta=v['selection__eta'];k=eta+v['selection__zeta'];odd=2*v['selection__odd_half']+1;Y=odd*q
 cc=k*Y+eta;f=v['selection__f'];ii=v['selection__i'];root=v['selection__o']*f-cc
 packed=(q-1)*((16*H+13)+(q+1)*((16*M+10)+(q-1)*(16*Z+8)))
 X=(v['selection__w']+(q-1)*(16*Z+8))*q;a=X*Y+Y;delta=a*a+4*a+3;index=k-v['selection__h']*X*Y
 first=v['selection__tau_gap']**2+4*X*Y*k*Y*(v['selection__tau_gap']-k)
 main=(X+a*cc+v['selection__ga']*(4*a+3))**2-delta*cc*cc
 aux=ii*ii*cc**4*(root*root-v['selection__y_aux']**2)+v['selection__y_aux']**2
 linear=root-v['selection__j']*cc+2*index
 strong=ii*ii*cc**4-delta*(f*f-1)+1
 factors=[first,main,aux,index-packed,linear,strong,glob-P]
 native=1
 for z in factors:native*=z
 ds=[0,c*E[2]-Zh[0],0,c*E[0]-Zh[1]];F=[v['F_even'],v['F_odd'],v['F_even'],v['F_odd']];I=[D,c,D,c]
 res=[B*(Hs[i]+ds[i])-Hs[i]-F[i]*P+I[i] for i in range(4)]
 res += [E[2]+E[3]+P-B*(E[1]+E[2]+E[3]),bm*v['population_quotient']-(E[0]+bm-x)]
 out=native*(1+sum(r*r for r in res))-1
 vals=dict(D=D,c0=c,B=B,bminus=bm,J=J,P=P,P2=P**2,P4=P**4,P8=P**8,R8=R8,O=O,C=C,S=S,Zb=Zb,Hb=Hb,Mb=Mb,T=T,T2=T2,M8=M8,H=H,M=M,Z=Z,q=q,padA=16*H+13,padB=16*M+10,F3=16*Z+8,global_bound_sum=glob)
 return vals,factors,res,out

# Exact univariate coefficient evaluation is independent of the gate degree ledger.
def padd(a,b,sign=1):
 c=[0]*max(len(a),len(b))
 for i,x in enumerate(a):c[i]+=x
 for i,x in enumerate(b):c[i]+=sign*x
 while len(c)>1 and c[-1]==0:c.pop()
 return c
def pmul(a,b,mod):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  if x:
   for j,y in enumerate(b):
    if y:c[i+j]=(c[i+j]+x*y)%mod
 while len(c)>1 and not c[-1]:c.pop()
 return c

def degree_line(packet):
 mod=1000000007;e={n:[(i+3)%mod,(i*i+7*i+11)%mod] for i,n in enumerate(packet['free'])}
 def g(x):return [x%mod] if type(x) is int else e[x]
 for n,op,a,b in packet['source']:
  aa=g(a);bb=g(b)
  if op=='*':cc=pmul(aa,bb,mod)
  else:
   cc=[z%mod for z in padd(aa,bb,1 if op=='+' else -1)]
   while len(cc)>1 and not cc[-1]:cc.pop()
  e[n]=cc
 p=e[packet['output']];need(len(p)-1==1789 and p[-1]!=0,'exact degree line')
 return {'modulus':mod,'free_line_recipe':'port i -> (i+3)+(i*i+7*i+11)*t, zero-indexed','degree':len(p)-1,'leading_coefficient':p[-1],'coefficient_sha256':sha(json.dumps(p,separators=(',',':')).encode()),'guarded_degree_upper_bound':1789}

def outer_fixture(packet,x,idles):
 # Explicit outer histories only; native Pell auxiliaries are not materialized.
 seq=[0]*x+[1]+[2]*x+[3]*idles;t=len(seq);D=1
 while D<=x+9:D*=2
 B=16*D;c=D-1;state=[1,0,1,0];states=[];E=[0]*4;H=[0]*4;ZZ=[0,0];place=1;code=0
 for ei in seq:
  edge=EDGES[ei];need(edge['source']==code,'fixture controller');code=edge['target'];states.append(list(state));E[ei]+=place
  for j in range(4):need(0<=state[j]+c<2*D,'fixture range');H[j]+=(state[j]+c)*place
  if ei==0:ZZ[1]+=(state[2]+c)*place;state[3]-=state[2]
  if ei==2:ZZ[0]+=(state[0]+c)*place;state[1]-=state[0]
  place*=B
 need(code==1 and state[:2]==state[2:],'fixture endpoint')
 P=B**t;v={'x':x,'height_slack':D-x-8,**{'H'+str(i):H[i] for i in range(4)},'Zhat3':ZZ[0]+1,'Zhat7':ZZ[1]+1,'F_even':state[0]+c,'F_odd':state[1]+c,'population_quotient':1+(E[0]-x)//(B-1)}
 v.update({'edge_hat'+str(i):E[i]+1 for i in range(4)})
 v['bound_global']=P+1-sum(H)-sum(ZZ)-8
 need(all(v[k]>0 for k in v if k!='x'),'positive outer fixture')
 # Evaluate only the literal producer prefix and outer producers; native values are cuts.
 nr=set(r[0] for r in packet['source'][packet['stage_counts']['packing']:packet['stage_counts']['packing']+63])
 evalrows=[r for r in packet['source'][:sum(packet['stage_counts'][s] for s in ['packing','native','outer_producers'])] if r[0] not in nr]
 e=evaluate(evalrows,v)
 get=lambda a:a if type(a) is int else e[a]
 need(all(get(a)==get(b) for a,b in packet['outer_comparisons']),'outer comparisons')
 pp=packet['ports'];hv=get(pp['H']);mv=get(pp['M']);zv=get(pp['Z']);q=get(pp['q'])
 need((hv&mv)==zv,'joined AND');truth=[q-16*hv-16*mv+16*zv-15,16*(hv-zv)+4,16*(mv-zv)+2,16*zv+8]
 need(all(a>0 for a in truth) and sum(truth)==q-1,'truth prefix')
 bad=dict(v);bad['x']=x+1;bad['height_slack']-=1
 # Hold D and every packed field fixed; only the marked count residual changes.
 eb=evaluate(evalrows,bad);getb=lambda a:a if type(a) is int else eb[a]
 need(getb(packet['outer_comparisons'][-1][0])-getb(packet['outer_comparisons'][-1][1])==1,'wrong population')
 return {'x':x,'idles':idles,'duration':t,'edge_word':seq,'state_path':states+[state],'D':D,'B':B,'P_bits':P.bit_length(),'all_six_outer_comparisons_zero':True,'joined_AND_and_positive_truth_fields':True,'native_Pell_tuple_materialized':False}

def make(root):
 data={}
 for n,pin in PINS.items():
  raw=(root/n).read_bytes();need(sha(raw)==pin,'pin mismatch '+n);data[n]=raw
 parent=loads(data['group_projective_general_separate_range.json'])['packets']['m8_private'];nr=native_rows(parent);packet=emit(nr);packet['ledger']=audit(packet)
 need([packet['ledger'][k] for k in ['gates','M','A','positive_witnesses']]==[187,86,101,27],'complete ledger')
 need(packet['stage_counts']['native']==63 and packet['stage_counts']['finalizer']==20,'stage ledger')
 # Compare all literal outputs against independent direct formulas, including rationals.
 checks=0;scalar=0
 for k in range(16):
  if k<12:v={n:((i+3)*(k+5)%13)-6 for i,n in enumerate(packet['free'])}
  else:v={n:Fraction(((i+7)*(k+3)%11)-5,(i+k)%3+1) for i,n in enumerate(packet['free'])}
  e=evaluate(packet['source'],v);vals,factors,res,out=direct(v)
  for n,z in vals.items():need(e[packet['ports'][n]]==z,'scalar '+n);scalar+=1
  need(e['eight_units']==__import__('functools').reduce(lambda a,b:a*b,factors,1),'native manual factors')
  for (a,b),r in zip(packet['outer_comparisons'],res):need(e[a]-e[b]==r,'direct residual')
  need(e[packet['output']]==out,'whole output');checks+=1
 degree=degree_line(packet)
 fixtures=[outer_fixture(packet,x,j) for x in range(4) for j in [0,1,3]]
 # All words of length <=7 independently exercise weighted open-end flow and LOAD count.
 import itertools
 flowtests=0
 for t in range(1,8):
  B=256;P=B**t
  for word in itertools.product(range(4),repeat=t):
   E=[sum(B**j for j,e in enumerate(word) if e==i) for i in range(4)]
   actual=0;legal=True
   for ei in word:
    edge=EDGES[ei]
    if edge['source']!=actual:legal=False
    actual=edge['target']
   legal=legal and actual==1
   formal=E[2]+E[3]+P==B*(E[1]+E[2]+E[3])
   need(formal==legal,'finite flow language');flowtests+=1
 ctx=loads(data['matrix193_context_absorption.json']);B=ctx['block']['B'];need(B==[-52109,29036,-94920,52891],'actual loader')
 inv=[B[3],-B[1],-B[2],B[0]];need(B[0]*B[3]-B[1]*B[2]==1 and sum([B[0],B[3]])==782,'loader determinant/trace')
 row=[1,0];growth=[];prev=None;prevprev=None
 for k in range(33):
  need(row[0]>=k+1,'actual loader lower bound')
  if k>=2:need(row[0]==782*prev-prevprev,'actual loader recurrence')
  growth.append({'k':k,'first_coordinate':str(row[0]),'bit_length':row[0].bit_length()});prevprev=prev;prev=row[0]
  row=[row[0]*inv[0]+row[1]*inv[2],row[0]*inv[1]+row[1]*inv[3]]
 return {'status':'PASS','scope':'Complete fixed-arity diagnostic source plus explicit generic marked-loader transfer; no numerical universal count claimed','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'predecessor_code_executed':False,'packet':packet,'native_source_contract':{'parent':'m8_private','rows':nr,'rows_retained':63,'cut_ports':CUTS,'independent_native_ports':NATIVE,'full_native_positive_converse':'inherited pinned tail/range proofs, not a finite Pell-zero test'},'degree_certificate':degree,'evidence':{'whole_outputs':checks,'rational_outputs':4,'scalar_equalities':scalar,'outer_fixtures':fixtures,'finite_controller_words':flowtests,'actual_loader_growth':growth},'generic_interface':{'macro_actions':97,'tile_actions':96,'identity_switch_and_idle':True,'physical_labels':'0 identity; 1..8 signed unit shears','positive_witness_bound':'n+29 for n explicit edges with eight selected hats (before lossless specialization)','input_prefix':'D=x+Hfix+height_slack, B=16D','Hfix':'fixed positive integer > each absolute initial coordinate, and >= padded lane count m','marked_equation':'(B-1)*Q=Ehat_load+(B-1)-x-1','duration':'unbounded existential, not a supplied horizon','ordinary_input':'natural x (or restrict to positive x)','numerical_universal_controller_materialized':False}}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',required=True,type=Path);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--expect',type=Path);g.add_argument('--output',type=Path);a=ap.parse_args();receipt=make(a.root)
 if a.expect:need(exact(receipt,loads(a.expect.read_bytes())),'receipt mismatch')
 else:a.output.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':'PASS','ledger':receipt['packet']['ledger'],'stages':receipt['packet']['stage_counts'],'exact_degree':receipt['degree_certificate']['degree'],'whole_outputs':receipt['evidence']['whole_outputs'],'outer_fixtures':len(receipt['evidence']['outer_fixtures']),'controller_words':receipt['evidence']['finite_controller_words']}))
if __name__=='__main__':main()
