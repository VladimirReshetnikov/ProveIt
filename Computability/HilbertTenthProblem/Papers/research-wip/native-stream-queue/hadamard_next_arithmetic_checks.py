#!/usr/bin/env python3
"""Fresh finite-integer graph; no supplied, archived or predecessor code executes."""
import argparse,hashlib,itertools,json
from pathlib import Path

def need(ok,msg):
 if not ok: raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def mu(e):return e.bit_length()-1+e.bit_count()-1

def build(n,T,constructed=False):
 need(n>=2 and T>=1,'domain')
 rows=[];eq=[];witness=[]
 def gate(name,op,a,b):rows.append([name,op,a,b]);return name
 def plus(name,a,b):return gate(name,'+',a,b)
 def minus(name,a,b):return gate(name,'-',a,b)
 def times(name,a,b):return gate(name,'*',a,b)
 def power(name,e):
  v=2
  for j,c in enumerate(bin(e)[3:]):
   v=times(name+'_square_'+str(j),v,v)
   if c=='1':v=times(name+'_double_'+str(j),v,2)
  return v
 L=(n-1)*(n*n-1);fixed=[4,4**(n*n),4**(n*(n-1)),4**(n-1),4**L,4**n]
 if constructed:
  exps=[2,2*n*n,2*n*(n-1),2*(n-1),2*L,2*n]
  B,KA,KB,KC,P,Q=[power('power_'+str(j),e) for j,e in enumerate(exps)]
  PQ=times('power_PQ',P,Q);off=plus('power_offset_base',PQ,P);off=plus('power_offset',off,1)
  Pb=plus('power_P_bound',P,1);Qb=plus('power_Q_bound',Q,1)
 else:
  B,KA,KB,KC,P,Q=fixed;off=P*Q+P+1;Pb=P+1;Qb=Q+1
 prefix=len(rows)
 bits=[];hats=[]
 for t in range(T+1):
  bt=[];ht=[]
  for i in range(n):
   h=f'bit_hat_{t}_{i}';witness.append(h);ht.append(h)
   b=minus(f'bit_{t}_{i}',h,1);o=minus(f'bit_other_{t}_{i}',h,2)
   v=times(f'boolean_{t}_{i}',b,o);eq.append([v,0,'already_residual']);bt.append(b)
  bits.append(bt);hats.append(ht)
 def horner(name,digits,base):
  v=digits[0];pen=None
  for j,d in enumerate(digits[1:],1):
   pen=v;v=times(f'{name}_mul_{j}',v,base);v=plus(f'{name}_add_{j}',v,d)
  return v,pen
 oldbin,_=horner('input_binary',list(reversed(bits[0])),2)
 newbin,_=horner('output_binary',list(reversed(bits[-1])),2)
 eq.extend([[oldbin,'input_word','comparison'],[newbin,'output_word','comparison']])
 basewords=[];suffixes=[]
 for t in range(T+1):
  z,suffix=horner('base_word_'+str(t),list(reversed(bits[t])),B)
  basewords.append(z);suffixes.append(suffix)
 for t in range(T):
  rbits=[bits[t][(i+1)%n] for i in range(n)]
  lhats=[hats[t][(i-1)%n] for i in range(n)]
  A,_=horner(f'A_{t}',list(reversed(bits[t])),KA)
  C,_=horner(f'C_{t}',rbits,KB)
  D,_=horner(f'D_{t}',lhats,KC)
  rot=times(f'rotate_wrap_{t}',bits[t][0],KC)
  rot=plus(f'rotate_{t}',suffixes[t],rot)
  names=[f'{stem}_{t}' for stem in ['middle_hat','low_hat','high_hat','low_slack','middle_slack']]
  H,low,high,ls,hs=names;witness.extend(names)
  pr=times(f'product_pair_{t}',A,C);pr=times(f'product_{t}',pr,D)
  qh=times(f'Q_high_{t}',Q,high);upper=plus(f'middle_plus_high_{t}',H,qh)
  upper=times(f'P_upper_{t}',P,upper);rhs=plus(f'extraction_rhs_{t}',low,upper)
  lhs=plus(f'extraction_lhs_{t}',pr,off)
  lb=plus(f'low_bound_{t}',low,ls);hb=plus(f'middle_bound_{t}',H,hs)
  eq.extend([[lhs,rhs,'comparison'],[lb,Pb,'comparison'],[hb,Qb,'comparison']])
  target=plus(f'center_plus_right_{t}',basewords[t],rot)
  target=minus(f'center_right_minus_next_{t}',target,basewords[t+1])
  target=plus(f'target_hat_{t}',target,1);eq.append([target,H,'comparison'])
 producers=len(rows);M=sum(r[1]=='*' for r in rows);AA=producers-M
 resid=[]
 for j,(a,b,kind) in enumerate(eq):
  v=a if kind=='already_residual' else minus(f'equality_residual_{j}',a,b)
  resid.append(times(f'residual_square_{j}',v,v))
 out=resid[0]
 for j,v in enumerate(resid[1:],1):out=plus(f'SOS_sum_{j}',out,v)
 extraM=sum(mu(e) for e in [2,2*n*n,2*n*(n-1),2*(n-1),2*L,2*n])+1 if constructed else 0
 extraA=4 if constructed else 0
 need(M==(5*n+1)*T+4*n-3+extraM,'M count')
 need(AA==(6*n+5)*T+5*n-3+extraA,'A count')
 need(len(rows)==(13*n+18)*T+11*n-1+extraM+extraA,'SOS count')
 need(len(witness)==n*(T+1)+5*T,'witness count')
 need(len(eq)==n*(T+1)+4*T+2,'equation count')
 free=['input_word','output_word']+witness;seen=set(free);deg={v:1 for v in free}
 degree=lambda v:deg[v] if isinstance(v,str) else 0
 for r,op,a,b in rows:
  need(r not in seen and all(not isinstance(v,str) or v in seen for v in [a,b]),'topology')
  if constructed:need(all(not isinstance(v,int) or v in [0,1,2] for v in [a,b]),'unconstructed numeral')
  deg[r]=degree(a)+degree(b) if op=='*' else max(degree(a),degree(b));seen.add(r)
 d={r[0]:r for r in rows};live=set();pending=[out]
 while pending:
  v=pending.pop()
  if not isinstance(v,str) or v in live:continue
  live.add(v)
  if v in d:pending.extend(d[v][2:])
 need(set(d)|set(free)==live,'liveness');need(deg[out]==6,'degree upper')
 return {'n':n,'T':T,'constructed_constants':constructed,'prefix_rows':prefix,'free':free,'positive_witnesses':witness,'source':rows,'comparisons':eq,'output':out,'producer_M':M,'producer_A':AA,'producer_count':producers,'SOS_M':sum(r[1]=='*' for r in rows),'SOS_A':sum(r[1]!='*' for r in rows),'SOS_count':len(rows),'degree_upper':6}

def word(v,B=2):return sum(x*B**i for i,x in enumerate(v))
def step(v):
 n=len(v);return [v[i]+v[(i+1)%n]-v[i]*v[(i+1)%n]-v[(i-1)%n]*v[i]*v[(i+1)%n] for i in range(n)]
def valuation(graph,states):
 n=graph['n'];T=graph['T'];B=4;Q=B**n;L=(n-1)*(n*n-1);P=B**L
 env={'input_word':word(states[0]),'output_word':word(states[-1])}
 for t,v in enumerate(states):
  for i,x in enumerate(v):env[f'bit_hat_{t}_{i}']=x+1
 for t in range(T):
  v=states[t]
  A=sum(v[i]*B**(n*n*i) for i in range(n))
  C=sum(v[(j+1)%n]*B**(n*(n-1)*(n-1-j)) for j in range(n))
  D=sum((1+v[(k-1)%n])*B**((n-1)*(n-1-k)) for k in range(n))
  pr=A*C*D;low=pr%P;mid=pr//P%Q;high=pr//(P*Q)
  need(mid==sum(v[i]*v[(i+1)%n]*(1+v[(i-1)%n])*B**i for i in range(n)),'diagonal')
  for stem,x in [('middle_hat',mid+1),('low_hat',low+1),('high_hat',high+1),('low_slack',P-low),('middle_slack',Q-mid)]:env[f'{stem}_{t}']=x
 need(all(env[w]>0 for w in graph['positive_witnesses']),'positive')
 value=lambda x:env[x] if isinstance(x,str) else x
 for r,op,a,b in graph['source']:
  a,b=value(a),value(b);env[r]=a*b if op=='*' else a+b if op=='+' else a-b
 return env[graph['output']]

def evidence(root):
 data={'scope':'Fixed-width fixed-horizon ordinary integer graph; no universality or fixed-arity claim','source_sha256':sha(Path(__file__).read_bytes())}
 names=['review_definable_operations_de37a66d1.md','finite_word_hadamard_skew.md','native_binary_reversal_inline129.md']
 data['inert_notes']=[{'path':n,'sha256':sha((root/n).read_bytes()),'read':'full Markdown only'} for n in names]
 arrays=[build(n,T,k) for n in [2,3,4] for T in [1,2] for k in [False,True]]
 data['full_finite_arrays']=arrays
 zeros=0
 for n in range(2,7):
  for T in [1,2,3]:
   graphs=[build(n,T,k) for k in [False,True]]
   for bits in itertools.product([0,1],repeat=n):
    states=[list(bits)]
    for t in range(T):states.append(step(states[-1]))
    for g in graphs:need(valuation(g,states)==0,'full trajectory');zeros+=1
 pairs=0
 for n in range(2,7):
  g=build(n,1)
  for old in itertools.product([0,1],repeat=n):
   expect=step(old)
   for new in itertools.product([0,1],repeat=n):
    need((valuation(g,[old,new])==0)==(list(new)==expect),'full transition equivalence');pairs+=1
 exponents=0
 for n in range(2,17):
  L=(n-1)*(n*n-1);seen=set()
  for i,j,k in itertools.product(range(n),repeat=3):
   e=n*n*i+n*(n-1)*(n-1-j)+(n-1)*(n-1-k)
   need(e not in seen,'collision');seen.add(e)
   need((L<=e<L+n)==(i==j==k),'band');exponents+=1
 data['checks']={'complete_positive_trajectory_zeros':zeros,'complete_one_step_word_pairs':pairs,'three_way_exponent_positions':exponents,'truth_table':[{'lcr':list(a),'out':a[1]+a[2]-a[1]*a[2]-a[0]*a[1]*a[2]} for a in itertools.product([0,1],repeat=3)]}
 return data

def main():
 a=argparse.ArgumentParser();a.add_argument('--root',required=True);g=a.add_mutually_exclusive_group(required=True);g.add_argument('--output');g.add_argument('--check');v=a.parse_args()
 b=(json.dumps(evidence(Path(v.root)),indent=2,sort_keys=True)+'\n').encode()
 if v.output:
  with open(v.output,'xb') as f:f.write(b)
 else:need(Path(v.check).read_bytes()==b,'receipt mismatch')
 print('PASS: fresh k-way packing probe and fully charged finite graphs')
if __name__=='__main__':main()
