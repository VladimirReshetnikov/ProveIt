#!/usr/bin/env python3
"""Fresh finite-word scout. Predecessor Markdown read/hash only; no imports."""
import argparse,hashlib,json
from pathlib import Path
DEFAULT_ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
READS={'native_controller_quadratic_sidon.md':[(1,107)],'input_bridge_central_product.md':[(1,210)],'gpcp_fixed_program_input_bridge.md':[(1,90)],'native_binary_input_dilation129.md':[(1,220)],'matrix193_packed_output_scout.md':[(1,175)],'matrix193_balanced_output_scout.md':[(30,90)]}
def need(p,msg):
 if not p:raise ValueError(msg)
def digest(b):return hashlib.sha256(b).hexdigest()
def emit(n,construct_constants=False):
 need(type(n) is int and n>=2,'n>=2')
 Q=2**n;P=2**((n-1)**2);rows=[];guards=[]
 def gate(name,op,a,b):rows.append([name,op,a,b]);return name
 def power(name,k):
  # Left-to-right binary chain for the fixed exponent k, starting at literal2.
  need(k>=1,'fixed exponent');v=2
  for j,bit in enumerate(bin(k)[3:]):
   v=gate(name+f'_square{j}','*',v,v)
   if bit=='1':v=gate(name+f'_times2_{j}','*',v,2)
  return v
 if construct_constants:
  qv=power('const_Q',n);rv=power('const_rev_radix',n-1);pv=power('const_P',(n-1)**2)
  pq=gate('const_PQ','*',pv,qv)
  offset=gate('const_offset','+',gate('const_offset_base','+',pq,pv),1)
  pplus=gate('const_Pplus1','+',pv,1);qplus=gate('const_Qplus1','+',qv,1)
 else:qv,rv,pv,offset,pplus,qplus=Q,2**(n-1),P,P*Q+P+1,P+1,Q+1
 prefix_cost=len(rows)
 bits={}
 for tag in ['a','b']:
  bits[tag]=[]
  for j in range(n):
   hat=f'{tag}{j}_hat';raw=gate(f'{tag}{j}','-',hat,1);minus=gate(f'{tag}{j}_minus2','-',hat,2)
   guards.append(gate(f'{tag}{j}_boolean','*',raw,minus));bits[tag].append(raw)
 def horner(name,order,radix):
  v=order[0]
  for j,d in enumerate(order[1:]):v=gate(f'{name}_join{j}','+',gate(f'{name}_mul{j}','*',v,radix),d)
  return v
 xw=horner('input_x',bits['a'][::-1],2);yw=horner('input_y',bits['b'][::-1],2)
 A=horner('spread_a',bits['a'][::-1],qv);C=horner('reverse_spread_b',bits['b'],rv)
 prod=gate('packed_product','*',A,C)
 qhigh=gate('q_high_hat','*',qv,'high_hat');mid=gate('middle_plus_high','+','Hhat',qhigh)
 upper=gate('shifted_upper','*',pv,mid);rhs=gate('decomposition_rhs','+','low_hat',upper)
 lhs=gate('decomposition_lhs','+',prod,offset)
 low=gate('low_bound','+','low_hat','low_slack');out=gate('output_bound','+','Hhat','output_slack')
 comparisons=[[xw,'x'],[yw,'y'],[lhs,rhs],[low,pplus],[out,qplus]]
 certificate=[list(r) for r in rows]
 residuals=list(guards)
 for j,(a,b) in enumerate(comparisons):residuals.append(gate(f'residual{j}','-',a,b))
 squares=[gate(f'square{j}','*',r,r) for j,r in enumerate(residuals)]
 F=squares[0]
 for j,s in enumerate(squares[1:]):F=gate(f'sos{j}','+',F,s)
 witnesses=[f'{s}{j}_hat' for s in ['a','b'] for j in range(n)]+['low_hat','high_hat','low_slack','output_slack']
 ports=['x','y','Hhat']+witnesses
 def audit(rs,outs):
  names=set(ports);defs={}
  for row in rs:
   nm,op,a,b=row;need(nm not in names,'duplicate')
   need(op in ['+','-','*'],'operator');need(all(type(v)is int or v in names for v in [a,b]),'topology')
   names.add(nm);defs[nm]=row
  live=set();todo=list(outs)
  while todo:
   v=todo.pop()
   if type(v)is int or v in live:continue
   live.add(v)
   if v in defs:todo.extend(defs[v][2:])
  need(set(defs)<=live and set(ports)<=live,'liveness')
  M=sum(r[1]=='*' for r in rs);return {'M':M,'A':len(rs)-M,'total':len(rs)}
 co=audit(certificate,guards+[v for eq in comparisons for v in eq]);fo=audit(rows,[F])
 if construct_constants:need(all(type(v)is not int or v in (1,2) for row in rows for v in row[2:]),'all derived constants paid')
 mu=lambda k:k.bit_length()+k.bit_count()-2
 extraM=mu(n)+mu(n-1)+mu((n-1)**2)+1 if construct_constants else 0
 extraA=4 if construct_constants else 0
 need(prefix_cost==extraM+extraA,'literal-free prefix')
 need(co=={'M':6*n-1+extraM,'A':8*n+1+extraA,'total':14*n+extraM+extraA},'certificate cost')
 need(fo=={'M':8*n+4+extraM,'A':10*n+10+extraA,'total':18*n+14+extraM+extraA},'polynomial cost')
 degree={p:1 for p in ports}
 for nm,op,a,b in rows:
  da=0 if type(a)is int else degree[a];db=0 if type(b)is int else degree[b]
  degree[nm]=da+db if op=='*' else max(da,db)
 need(degree[F]==4,'degree')
 return {'n_fixed':n,'construct_constants':construct_constants,'constant_prefix_cost':{'M':extraM,'A':extraA,'total':extraM+extraA},'parameters':['x','y','Hhat'],'positive_witnesses':witnesses,'witness_count':len(witnesses),'constants':{'Q':Q,'P':P,'input_spread_radix':Q,'reversed_spread_radix':2**(n-1),'decomposition_offset':P*Q+P+1},'certificate_rows':certificate,'boolean_zero_registers':guards,'comparisons':comparisons,'full_rows':rows,'output':F,'certificate_cost':co,'full_polynomial_cost':fo,'equations':2*n+5,'degree':4,'all_paid_rows_and_ports_live':True}
def evaluate(packet,values):
 env=dict(values)
 def v(a):return a if type(a)is int else env[a]
 for nm,op,a,b in packet['full_rows']:
  a,b=v(a),v(b);env[nm]=a*b if op=='*' else a+b if op=='+' else a-b
 return env[packet['output']]
def witness(n,x,y):
 a=[(x>>j)&1 for j in range(n)];b=[(y>>j)&1 for j in range(n)]
 A=sum(v*2**(n*j) for j,v in enumerate(a));C=sum(v*2**((n-1)*(n-1-j)) for j,v in enumerate(b))
 P=2**((n-1)**2);Q=2**n;low=A*C%P;middle=(A*C//P)%Q;high=A*C//(P*Q)
 need(middle==x&y,'band identity')
 env={'x':x,'y':y,'Hhat':middle+1,'low_hat':low+1,'high_hat':high+1,'low_slack':P-low,'output_slack':Q-middle}
 env.update({f'a{j}_hat':v+1 for j,v in enumerate(a)});env.update({f'b{j}_hat':v+1 for j,v in enumerate(b)})
 return env
VARIABLE_ROWS=[['Pplus1','+','P',1],['Qplus1','+','Q',1],['high','-','high_hat',1],['Qhigh','*','Q','high'],['middle_plus_high','+','Hhat','Qhigh'],['upper','*','P','middle_plus_high'],['rhs','+','low_hat','upper'],['product','*','A','C'],['lhs','+','product','Pplus1'],['low_bound','+','low_hat','low_slack'],['output_bound','+','Hhat','output_slack']]
def make(root):
 pins=[]
 for name,rs in READS.items():
  b=(root/name).read_bytes();ls=b.splitlines(keepends=True)
  # Coverage was read through these line endpoints; clamp only EOF.
  spans=[{'first':a,'last':min(z,len(ls)),'sha256':digest(b''.join(ls[a-1:z]))} for a,z in rs]
  pins.append({'path':name,'sha256':digest(b),'bytes':len(b),'read_spans':spans})
 packets=[emit(n,variant) for variant in [False,True] for n in [2,3,4,5,8]]
 paircases=0;fullcases=0;perturbations=0
 for n in range(2,8):
  current=[p for p in packets if p['n_fixed']==n]
  for x in range(2**n):
   for y in range(2**n):
    vals=witness(n,x,y);paircases+=1
    if n<=5:
     for packet in current:
      need(evaluate(packet,vals)==0,'full graph zero');fullcases+=1
      bad=dict(vals);bad['Hhat']+=1;need(evaluate(packet,bad)>0,'wrong output rejection');perturbations+=1
 # Complete pair-position census, not an all-n proof.
 positional=0
 for n in range(2,129):
  L=(n-1)**2;seen={}
  for i in range(n):
   for j in range(n):
    e=n*i+(n-1)*(n-1-j);need(e not in seen,'position collision');seen[e]=(i,j)
    need((L<=e<L+n)==(i==j),'diagonal band');positional+=1
  need(all(seen[L+i]==(i,i) for i in range(n)),'band coefficient')
 need(len(VARIABLE_ROWS)==11 and sum(r[1]=='*' for r in VARIABLE_ROWS)==3,'variable cost')
 aliases=[]
 # Without loader constraints two legal typed packed words may be unrelated to x,y.
 n=2;vals=witness(n,1,1);vals.update({'x':0,'y':0})
 aliases.append({'n':n,'claimed_inputs':[0,0],'loaded_bits':[1,1],'A':1,'C':2,'Hhat':2,'true_Hhat':1,'description':'All extraction/radix conditions hold; omitting both input-binding equations admits this false AND.'})
 for x,y,A,C,P,Q,missing in [(1,1,1,2,1,4,'P power'),(3,3,5,3,2,2,'Q power'),(1,2,1,2,2,4,'reversal')]:
  low=A*C%P;middle=A*C//P%Q;high=A*C//(P*Q)
  env={'A':A,'C':C,'P':P,'Q':Q,'Hhat':middle+1,'low_hat':low+1,'high_hat':high+1,'low_slack':P-low,'output_slack':Q-middle}
  need(all(v>0 for k,v in env.items() if k not in ['A','C']),'positive alias')
  for nm,op,v,w in VARIABLE_ROWS:
   v=v if type(v)is int else env[v];w=w if type(w)is int else env[w];env[nm]=v*w if op=='*' else v+w if op=='+' else v-w
  need(env['lhs']==env['rhs'] and env['low_bound']==P+1 and env['output_bound']==Q+1,'conditional graph alias')
  need(middle!=(x&y),'must be false AND')
  aliases.append({'n':2,'claimed_inputs':[x,y],'A':A,'C':C,'P':P,'Q':Q,'Hhat':middle+1,'true_Hhat':(x&y)+1,'missing':missing,'positive_extraction_witnesses':{k:env[k] for k in ['low_hat','high_hat','low_slack','output_slack']}})
 return {'scope':'Fixed-n family plus conditional loaded-word extraction; no uniform compiler or gate optimum.','source_sha256':digest(Path(__file__).read_bytes()),'inert_predecessor_read_scope':pins,'theorem':{'n_minimum':2,'binary_radix_suffices':True,'diagonal_start':'(n-1)^2','exponent':'n*i+(n-1)*(n-1-j)','identity':'((A*C)//2^((n-1)^2)) mod 2^n = x AND y','all_n_proof_in_companion':True},'complete_fixed_n_sources':packets,'variable_power_interface':{'rows':VARIABLE_ROWS,'comparisons':[['lhs','rhs'],['low_bound','Pplus1'],['output_bound','Qplus1']],'cost':{'M':3,'A':8,'total':11},'conditions':'P>=1,Q>=2 integers; loaded A,C nonnegative; positive Hhat,low_hat,high_hat,low_slack,output_slack. Correct P,Q powers and A,C bit loaders are not included.','missing':['Q=2^n','P=2^((n-1)^2)','A=spread_n(x)','C=spread_(n-1)(reverse_n(y))','input widths and consistency']},'finite_checks':{'all_word_pairs_n2_through7':paircases,'full_emitted_source_zeros_n2_through5':fullcases,'wrong_Hhat_perturbations_rejected':perturbations,'pair_position_tests_n2_through128':positional,'zero_words_included':True},'missing_loader_counterexample':aliases,'execution':'Fresh own arithmetic only; frozen predecessors read as Markdown bytes, never executed/imported.'}
def exact(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def unique(pairs):
 d={}
 for k,v in pairs:
  if k in d:raise ValueError('duplicate JSON key')
  d[k]=v
 return d
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=DEFAULT_ROOT);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);args=ap.parse_args();receipt=make(args.root)
 if args.output:
  with args.output.open('x') as f:json.dump(receipt,f,sort_keys=True,indent=2);f.write('\n')
 else:
  saved=json.loads(args.expect.read_text(),object_pairs_hook=unique,parse_float=lambda _:(_ for _ in ()).throw(ValueError('float')))
  need(exact(receipt,saved),'receipt mismatch')
 print('PASS fixed-n skew Hadamard: binary carry-free identity; complete14n relation /18n+14 SOS; variable loader still open')
