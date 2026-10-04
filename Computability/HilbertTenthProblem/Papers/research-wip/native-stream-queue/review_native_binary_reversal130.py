#!/usr/bin/env python3
"""Independent exact review. Read predecessor bytes only; never import them."""
import argparse,copy,hashlib,json
from pathlib import Path
WIP=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
AUTHOR_PINS={'py':'ed6e355f365f78015e5326d087047923b47967936a95712e1c8372b0481ef0ca','json':'1ef05ab68b9de6030d71abcdb2a3caeb2932d53b531192d99937b018d7c17197','md':'d5af03d5d30cb3e0a851d2c2a29bf17beb6a3373657a6ca295d2a9a1804a8c73'}
def check(c,m):
 if not c: raise ValueError(m)
def digest(b):return hashlib.sha256(b).hexdigest()
def unique(items):
 d={}
 for k,v in items:
  check(k not in d,'duplicate JSON key');d[k]=v
 return d
def read(p):return json.loads(p.read_text(),object_pairs_hook=unique)
def equal(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(equal(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(equal(x,y) for x,y in zip(a,b))
 return a==b
def add(a,b,s=1):
 d=dict(a)
 for k,v in b.items():d[k]=d.get(k,0)+s*v
 return {k:v for k,v in d.items() if v}
def mul(a,b):
 d={}
 for x,c in a.items():
  for y,e in b.items():
   k=tuple(sorted(x+y));d[k]=d.get(k,0)+c*e
 return {k:v for k,v in d.items() if v}
class P:
 def __init__(self,d):self.d=d if isinstance(d,dict) else {():d} if d else {}
 def __add__(a,b):return P(add(a.d,toP(b).d))
 __radd__=__add__
 def __sub__(a,b):return P(add(a.d,toP(b).d,-1))
 def __rsub__(a,b):return toP(b)-a
 def __mul__(a,b):return P(mul(a.d,toP(b).d))
 __rmul__=__mul__
 def __pow__(a,n):
  z=P(1)
  for _ in range(n):z=z*a
  return z
 def __eq__(a,b):return a.d==toP(b).d
 def degree(a):return max(map(len,a.d),default=-1)
def toP(x):return x if isinstance(x,P) else P(x)
def variable(s):return P({(s,):1})
def evaluate(rows,e):
 e=dict(e)
 for name,op,a,b in rows:
  a=a if type(a)is int else e[a];b=b if type(b)is int else e[b]
  e[name]=a+b if op=='+' else a-b if op=='-' else a*b
 return e
def norm_residuals(v,prefix,index,scale):
 g=lambda s:v[prefix+s]
 X=g('w')*scale;Y=g('s')*scale;E=X*Y;a=g('a');c=g('c');d=g('d');k=g('k');tau=g('tau');delta=(a+2)**2-1;U=g('j')*c-(2*index+1);ic=g('i')*c*c;y=g('y_aux')
 return [(E*E+X)*(k*Y)**2-tau*(tau+1),c-k*Y-g('eta'),k-g('eta')-g('zeta'),k-index-1-g('h')*E,a-Y*(X+1),d-X-a*c-g('ga')*(4*a+3),d*d-1-delta*c*c,ic*ic-delta*(g('f')**2-1),ic*ic*(U*U-y*y)-1+y*y,U-g('o')*g('f')+c]
def direct_residuals(v):
 x,q,z=(v[k] for k in ['x','q','z']);J,K,Pv,Ahat=(v[k] for k in ['J','K','P','Ahat']);B=2*q;S=q*Pv
 r=[(B-1)*J+1-Pv,(2*B-1)*K+1-S,x+v['input_slack']-q,Ahat-1-q*((q-1)*(v['quotient_hat']-1)+z),z+v['output_slack']-q]
 r+=norm_residuals(v,'geo__',J,q)
 r +=[v['geo__s']-2*v['geo__odd_half']-1,J+v['geo__bound_beta']-v['geo__w']*q,B+v['geo__index_beta']-J]
 N=16*S;F0,F1,F2=(v['and__'+s] for s in ['F0','F1','F2']);F3=16*Ahat-8
 r +=[v['and__r']-(F0+N*(F1+N*(F2+N*F3))),F0+F1+F2+F3+1-N,v['and__s']-2*v['and__odd_half']-1,v['and__r']+v['and__bound_beta']-v['and__w']*N]
 r+=norm_residuals(v,'and__',v['and__r'],N)
 r +=[F1+F3-32*x*K-12,F2+F3-16*q*J-10]
 check(len(r)==34,'34 independently specified residuals');return r
def ledger(rows,ports,outs):
 seen=set(ports);d={}
 for name,op,a,b in rows:
  check(name not in seen and op in ['+','-','*'],'unique producer');check(all(type(t)is int or t in seen for t in (a,b)),'topological row');seen.add(name);d[name]=(a,b)
 live=set();todo=list(outs)
 while todo:
  x=todo.pop()
  if type(x)is int or x in live:continue
  live.add(x)
  if x in d:todo.extend(d[x])
 check(set(d)|set(ports)<=live,'all rows and supplied ports live')
 m=sum(r[1]=='*' for r in rows);return {'total':len(rows),'M':m,'A':len(rows)-m}
def source_review(packet,old):
 original=copy.deepcopy(old);src=old['certificate']['source'];oc=old['certificate']
 outer=[['B','+','q','q'],['scale','*','q','P'],['Bm1','-','B',1],['repunit_product','*','Bm1','J'],['repunit_P','+','repunit_product',1],['twiceB','+','B','B'],['twiceBm1','-','twiceB',1],['mask_product','*','twiceBm1','K'],['mask_scale','+','mask_product',1],['copies','*','x','K'],['reverse_mask','*','q','J'],['input_bound','+','x','input_slack'],['modulus','-','q',1],['quotient_minus_one','-','quotient_hat',1],['quotient_product','*','modulus','quotient_minus_one'],['congruence_right0','+','quotient_product','z'],['scaled_reverse_sum','*','q','congruence_right0'],['congruence_right','+','scaled_reverse_sum',1],['output_bound','+','z','output_slack']]
 expected=outer+copy.deepcopy(src[18:]);next(r for r in expected if r[0]=='and__scaled_A')[2]=32;next(r for r in expected if r[0]=='and__scaled_B')[3]='reverse_mask'
 check(expected==packet['source'],'complete independent literal source reconstruction')
 eq=copy.deepcopy(oc['comparisons']);eq[3]=['Ahat','congruence_right'];eq[4]=['output_bound','q'];check(eq==packet['comparisons'],'complete comparisons')
 check(packet['parameters_positive']==['x','q','z'],'external positive domain');check(packet['positive_witnesses']==[v for v in oc['auxiliaries'] if v!='q'],'all 48 witness names retained')
 full=copy.deepcopy(expected)+[[f'residual_{i}','-',a,b] for i,(a,b) in enumerate(eq)]+[[f'square_{i}','*',f'residual_{i}',f'residual_{i}'] for i in range(34)]
 prev='square_0'
 for i in range(1,34):full.append([f'sum_{i}','+',prev,f'square_{i}']);prev=f'sum_{i}'
 check(full==packet['full_source'] and prev==packet['output'],'entire literal finalizer')
 ports=packet['parameters_positive']+packet['positive_witnesses'];co=ledger(expected,ports,[s for e in eq for s in e]);fo=ledger(full,ports,[prev]);check(co=={'total':130,'M':66,'A':64} and fo=={'total':231,'M':100,'A':131},'complete ledgers')
 v={s:variable(s) for s in ports};e=evaluate(full,v);manual=direct_residuals(v)
 for i,p in enumerate(manual):check(p==e[f'residual_{i}'],'full formal residual '+str(i))
 total=sum((x*x for x in manual),P(0));check(total==e[prev],'whole polynomial independently specified SOS')
 deg=total.degree();lead={m:c for m,c in total.d.items() if len(m)==deg};mon=tuple(sorted(['and__w']*4+['and__s']*8+['and__k']*4+['q']*12+['P']*12));check(deg==40 and lead=={mon:2**48},'exact degree and entire leading form')
 check(packet['certificate_cost']==co and packet['polynomial_cost']==fo and packet['equations']==34 and packet['witnesses']==48,'author metadata agrees with fresh count');check(old==original,'predecessor object immutability')
 return {'producer_ledger':co,'full_polynomial_ledger':fo,'positive_witnesses':len(packet['positive_witnesses']),'comparisons':34,'residual_terms':[len(x.d) for x in manual],'residual_degrees':[x.degree() for x in manual],'full_polynomial_terms':len(total.d),'degree':deg,'highest_coefficient':2**48,'highest_monomial':{'and__w':4,'and__s':8,'and__k':4,'q':12,'P':12},'parent_immutable':True,'all_130_rows_and_51_ports_live':True}
def pell(A,n):
 # Independently multiply (A+sqrt(A^2-1)) n times.
 c,s=1,0;delta=A*A-1
 for _ in range(n):c,s=A*c+delta*s,c+A*s
 return c,s
def partial_geometry():
 rows=[]
 for r in [5,7,9,11,13]:
  q=2**r.bit_count();X=2**(2*r+1)
  from math import comb
  Y=sum(comb(2*r,r+j)*X**j for j in range(r+1));a=Y*(X+1);A=a+2;D=A*A-1;P0=2*X*Y*Y+1
  d,c=pell(A,2*r+1);t,k=pell(P0,r+1);eta=c-k*Y;zeta=k-eta
  check(c>A*D*D and c>2*(2*r+1),'rank bounds at smaller threshold');check(eta>0 and zeta>0,'strict ratio positive interval');check((k-r-1)%(X*Y)==0 and k>r+1,'positive h');check((d-X-a*c)%(4*a+3)==0 and d>X+a*c,'positive ga');check(t%2==1 and Y%q==0 and (Y//q)%2==1 and Y//q>1,'tau and odd scale');check(d*d-D*c*c==1 and t*t-(P0*P0-1)*k*k==1,'two exact Pell norms')
  rows.append({'r':r,'q':q,'c_bits':c.bit_length(),'positive_initial_coordinates':True,'full_auxiliary_extension_materialized':False})
 return rows
def outer_checks(packet):
 count=ones=0
 for n in range(2,11):
  q=2**n;B=2*q;P0=B**n;J=sum(B**i for i in range(n));K=sum((2*B)**i for i in range(n));S=q*P0
  check(J>B and J%2==1 and J.bit_count()==n and (2*B-1)*K+1==S,'duration synchronization')
  for x in range(1,q):
   bits=format(x,'0'+str(n)+'b');z=int(bits[::-1],2);R=sum(int(bits[i])*B**i for i in range(n));selected=(2*x*K)&(q*J)
   check(selected==q*R and R>=z and (R-z)%(q-1)==0,'independent reversal and residue')
   vals=dict(x=x,q=q,z=z,P=P0,J=J,K=K,Ahat=selected+1,quotient_hat=1+(R-z)//(q-1),input_slack=q-x,output_slack=q-z)
   check(all(v>0 for v in vals.values()),'positive outer extension');ev=evaluate(packet['source'][:19],vals);check(all(ev[a]==ev[b] for a,b in packet['comparisons'][:5]),'five outer comparisons');check(0<2*x*K<S and 0<q*J<S,'AND input ranges')
   count+=1;ones+=x==q-1
 return {'outer_cases_n2_to10':count,'all_ones_cases':ones,'full_native_Pell_zero_fixtures':0}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=WIP);ap.add_argument('--author-root',type=Path,default=Path('/tmp'));g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args()
 pins=[]
 for ext in ['py','json','md']:
  name='native_binary_reversal130.'+ext;b=(a.author_root/name).read_bytes();check(AUTHOR_PINS and digest(b)==AUTHOR_PINS[ext],'frozen author '+ext);pins.append({'name':name,'sha256':digest(b),'bytes':len(b),'read_scope':'full inert source, receipt, or proof'})
 author=read(a.author_root/'native_binary_reversal130.json');check(author['source_sha256']==AUTHOR_PINS['py'],'author receipt source binding');old=read(a.root/'native_binary_input_dilation129.json');packet=author['certificate']
 for dep in author['inert_dependencies']:
  b=(a.root/dep['name']).read_bytes();check(len(b)==dep['bytes'] and digest(b)==dep['sha256'],'author dependency '+dep['name'])
 b=(a.root/'native_binary_input_dilation129.json').read_bytes();check(packet['parent_json']['sha256']==digest(b) and packet['parent_json']['bytes']==len(b),'actual parent byte binding')
 result={'status':'PASS_INDEPENDENT_REVERSAL130','source_sha256':digest(Path(__file__).read_bytes()),'author_pins':pins,'source':source_review(packet,old),'fresh_outer_checks':outer_checks(packet),'fresh_partial_geometry_checks':partial_geometry(),'scope':'Complete literal source and whole-polynomial review; raw r>=5 proof challenge and inherited native positive converses. No predecessor execution; no full native Pell zero tuple materialized.'}
 for name in ['native_binary_input_dilation129.json','native_binary_input_dilation129.md','group_linked_binary_geometry47.md','native_binary_masked_selection63.md']:
  b=(a.root/name).read_bytes();result.setdefault('inert_dependencies',[]).append({'name':name,'sha256':digest(b),'bytes':len(b)})
 for name in ['PELL_RELAXED_AUXILIARY_PROOF.md','HALF_PARAMETER_PELL_92_PROOF.md','EXPLORATION_FIXED_MINUS_INDEX_PARITY.md']:
  b=(a.root.parent.parent/'1980'/name).read_bytes();result['inert_dependencies'].append({'name':name,'sha256':digest(b),'bytes':len(b)})
 if a.output:
  with a.output.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
 else:check(equal(result,read(a.expect)),'type-exact receipt replay')
 print(json.dumps({'status':result['status'],'source':result['source'],'outer':result['fresh_outer_checks']}))
if __name__=='__main__':main()
