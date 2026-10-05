#!/usr/bin/env python3
"""New paid positive-guard graphs. Evaluate only arrays freshly authored here.
Frozen predecessors are read as metadata/text bytes, never run or imported.
"""
import argparse
import hashlib
import itertools
import json
from fractions import Fraction
from pathlib import Path

PINS={
 'markov_projective_counter_step.md':'01003a2063d442fa71d4a5e80dfd8218edb7940c22fcc90d6b847079fd63a5d2',
 'markov_projective_counter_step_checks.json':'ec34cd98a4330ba04c90c7304bc446950bb85ddbc206771684f1159aec678396',
 'review_markov_projective_counter_step.md':'8945e419b6349660e74929194f298d078bcabde58cea7f098aaceb2bb131c986',
 'residue_affine_factored_counter_step.md':'60250f0f6d12f7583b5de747c82d0d91205eab98ca0f4095992d458aaf8a951f',
 'markov_sine_lift.md':'7b30acebde3c5576773e92030242e4e8db1d00530fa9d7733b4ac8796270d1b2',
}

def check(ok,msg):
 if not ok: raise ValueError(msg)
def sha(data):return hashlib.sha256(data).hexdigest()
def plus(a,b,sign=1):
 out=dict(a)
 for k,v in b.items():out[k]=out.get(k,0)+sign*v
 return {k:v for k,v in out.items() if v}
def times(a,b):
 out={}
 for ka,va in a.items():
  for kb,vb in b.items():
   k=tuple(x+y for x,y in zip(ka,kb));out[k]=out.get(k,0)+va*vb
 return {k:v for k,v in out.items() if v}
def scalar(n,c):return {(0,)*n:c} if c else {}
def variable(n,j):return {tuple(int(i==j) for i in range(n)):1}
def degree(p):return max(map(sum,p),default=-1)
def encode(p):return [[list(k),v] for k,v in sorted(p.items())]

class Graph:
 def __init__(self,ports,external,witnesses):
  self.ports=ports;self.external=external;self.witnesses=witnesses;self.rows=[];self.residuals=[]
 def row(self,n,op,a,b):self.rows.append([n,op,a,b]);return n
 def residual(self,n):self.residuals.append(n);return n
 def finish(self):
  squares=[self.row('square_'+str(j),'*',r,r) for j,r in enumerate(self.residuals)]
  out=squares[0]
  for j,s in enumerate(squares[1:],1):out=self.row('join_'+str(j),'+',out,s)
  self.output=out;return self

def direct_step(g,j,Cp,B,u):
 t=g.row('t'+str(j),'-',B,2)
 g.residual(g.row('rz'+str(j),'*',t,u))
 tmp=g.row('transition_partial'+str(j),'-',Cp,u)
 g.residual(g.row('rt'+str(j),'+',tmp,t))

def raw_step(g,j,Xp,Hp,H,B,u,q):
 t=g.row('t'+str(j),'-',B,2)
 g.residual(g.row('rz'+str(j),'*',t,u))
 th=g.row('tH'+str(j),'*',t,H)
 qx=g.row('qX'+str(j),'*',q,Xp)
 tmp=g.row('transition_partial'+str(j),'-',qx,u)
 g.residual(g.row('rx'+str(j),'+',tmp,th))
 qh=g.row('qH'+str(j),'*',q,Hp)
 g.residual(g.row('rh'+str(j),'-',qh,H))

def direct_local():
 g=Graph(['C','Cp','B'],['C','Cp'],['B'])
 u=g.row('u0','-','C',1);direct_step(g,0,'Cp','B',u)
 return g.finish()

def raw_local(q,linked):
 ports=(['C','Cp'] if linked else [])+['B','X','H','Xp','Hp']
 g=Graph(ports,['C','Cp'] if linked else ['X','H','Xp','Hp'],['B','X','H','Xp','Hp'] if linked else ['B'])
 u=g.row('u0','-','X','H');raw_step(g,0,'Xp','Hp','H','B',u,q)
 if linked:
  hc=g.row('linked_product','*','H','C')
  g.residual(g.row('link','-','X',hc))
  hpc=g.row('linked_product_next','*','Hp','Cp')
  g.residual(g.row('link_next','-','Xp',hpc))
 return g.finish()

def direct_history(T):
 witnesses=['C'+str(j) for j in range(1,T+1)]+['B'+str(j) for j in range(T)]
 g=Graph(['x']+witnesses,['x'],witnesses)
 for j in range(T):
  u='x' if j==0 else g.row('u'+str(j),'-','C'+str(j),1)
  direct_step(g,j,'C'+str(j+1),'B'+str(j),u)
 g.residual(g.row('endpoint','-','C'+str(T),1))
 return g.finish()

def raw_history(T,q):
 witnesses=['H0']+[v+str(j) for j in range(1,T+1) for v in ['X','H']]+['B'+str(j) for j in range(T)]
 g=Graph(['x']+witnesses,['x'],witnesses)
 u0=g.row('u0','*','H0','x')
 for j in range(T):
  u=u0 if j==0 else g.row('u'+str(j),'-','X'+str(j),'H'+str(j))
  raw_step(g,j,'X'+str(j+1),'H'+str(j+1),'H'+str(j),'B'+str(j),u,q)
 g.residual(g.row('endpoint','-','X'+str(T),'H'+str(T)))
 return g.finish()

def inspect(g):
 seen=set(g.ports);by={};M=0
 check(len(seen)==len(g.ports),'duplicate port')
 check(set(g.external).isdisjoint(g.witnesses) and set(g.external+g.witnesses)==seen,'port domains')
 for row in g.rows:
  n,op,a,b=row
  check(n not in seen and op in ['+','-','*'],'row')
  check(all(type(x)is int or x in seen for x in [a,b]),'topology')
  seen.add(n);by[n]=row;M+=op=='*'
 live=set();stack=[g.output]
 while stack:
  n=stack.pop()
  if type(n)is int or n in live:continue
  live.add(n)
  if n in by:stack.extend(by[n][2:])
 check(live==seen,'liveness')
 return {'M':M,'A':len(g.rows)-M,'total':len(g.rows)}

def evaluate_new(g,values):
 env=dict(values)
 for n,op,a,b in g.rows:
  x=a if type(a)is int else env[a];y=b if type(b)is int else env[b]
  env[n]=x*y if op=='*' else x+y if op=='+' else x-y
 return env[g.output]

def expand_new(g):
 n=len(g.ports);env={name:variable(n,j) for j,name in enumerate(g.ports)}
 for dest,op,a,b in g.rows:
  x=scalar(n,a) if type(a)is int else env[a];y=scalar(n,b) if type(b)is int else env[b]
  env[dest]=times(x,y) if op=='*' else plus(x,y,-1 if op=='-' else 1)
 return env

def mathematical_residuals(g,kind,T,q):
 # Independently written closed formulas, not a predecessor array interpreter.
 n=len(g.ports);v={name:variable(n,j) for j,name in enumerate(g.ports)}
 one=scalar(n,1);two=scalar(n,2);Q=scalar(n,q)
 out=[];old=[];boolean=[]
 if kind=='direct_local':
  C,Cp,B=[v[s] for s in ['C','Cp','B']]
  out=[times(plus(B,two,-1),plus(C,one,-1)),plus(plus(plus(Cp,C,-1),B),one,-1)]
  boolean=[times(plus(B,one,-1),plus(B,two,-1))];old=list(out)
 elif kind.startswith('raw_local'):
  X,H,Xp,Hp,B=[v[s] for s in ['X','H','Xp','Hp','B']]
  rz=times(plus(B,two,-1),plus(X,H,-1))
  rx=plus(plus(times(Q,Xp),X,-1),times(plus(B,one,-1),H))
  rh=plus(times(Q,Hp),H,-1);out=[rz,rx,rh];old=list(out)
  boolean=[times(plus(B,one,-1),plus(B,two,-1))]
  if kind=='raw_local_linked':
   L=plus(X,times(H,v['C']),-1);Lp=plus(Xp,times(Hp,v['Cp']),-1)
   out += [L,Lp]
   old=[times(plus(B,two,-1),plus(v['C'],one,-1)),rx,rh,L,Lp]
 elif kind=='direct_history':
  for j in range(T):
   C=plus(v['x'],one) if j==0 else v['C'+str(j)]
   Cp=v['C'+str(j+1)];B=v['B'+str(j)]
   out += [times(plus(B,two,-1),plus(C,one,-1)),plus(plus(plus(Cp,C,-1),B),one,-1)]
   boolean.append(times(plus(B,one,-1),plus(B,two,-1)))
  out.append(plus(v['C'+str(T)],one,-1));old=list(out)
 else:
  for j in range(T):
   H=v['H'+str(j)];X=times(H,plus(v['x'],one)) if j==0 else v['X'+str(j)]
   Xp=v['X'+str(j+1)];Hp=v['H'+str(j+1)];B=v['B'+str(j)]
   out += [times(plus(B,two,-1),plus(X,H,-1)),plus(plus(times(Q,Xp),X,-1),times(plus(B,one,-1),H)),plus(times(Q,Hp),H,-1)]
   boolean.append(times(plus(B,one,-1),plus(B,two,-1)))
  out.append(plus(v['X'+str(T)],v['H'+str(T)],-1));old=list(out)
 return out,old,boolean

def squares(polys):
 out={}
 for p in polys:out=plus(out,times(p,p))
 return out

def legal(C,Cp,B):return (B==1 and C==Cp==1) or (B==2 and C>=2 and Cp==C-1)

def check_packet(name,g,kind,T,q):
 counts=inspect(g);env=expand_new(g);rs,old,booleans=mathematical_residuals(g,kind,T,q)
 check([env[r] for r in g.residuals]==rs,'residual formulas '+name)
 target=squares(rs);check(env[g.output]==target,'full polynomial '+name)
 expected_degree=6 if kind=='raw_history' else 4
 check(degree(target)==expected_degree,'exact degree '+name)
 if kind=='direct_local':expected={'M':3,'A':5,'total':8}
 elif kind=='raw_local_unlinked':expected={'M':7,'A':7,'total':14}
 elif kind=='raw_local_linked':expected={'M':11,'A':11,'total':22}
 elif kind=='direct_history':expected={'M':3*T+1,'A':6*T,'total':9*T+1}
 else:expected={'M':7*T+2,'A':8*T,'total':15*T+2}
 check(counts==expected,'ledger '+name)
 old_poly=squares(old+booleans)
 if kind!='raw_local_linked':
  check(plus(old_poly,target,-1)==squares(booleans),'Boolean deletion identity')
  relation='old_formula = new_polynomial + sum Boolean_residual^2'
 else:
  n=len(g.ports);v={s:variable(n,j) for j,s in enumerate(g.ports)};t=plus(v['B'],scalar(n,2),-1)
  rzold=old[0];link=rs[-2];H=v['H']
  corr=plus(times(plus(times(H,H),scalar(n,1),-1),times(rzold,rzold)),times(times(times(scalar(n,2),H),t),times(link,rzold)))
  corr=plus(corr,times(times(t,t),times(link,link)))
  corr=plus(corr,squares(booleans),-1)
  check(plus(target,old_poly,-1)==corr,'linked full correction')
  relation='new-old = (H^2-1)*rz_old^2 + 2*H*t*link*rz_old + t^2*link^2 - rb^2'
 return {'kind':kind,'T':T,'q':q if kind.startswith('raw') else None,'ports':g.ports,'external_positive_integer_ports':g.external,'positive_witnesses':g.witnesses,
         'source':g.rows,'residuals':g.residuals,'output':g.output,**counts,'exact_degree':expected_degree,
         'full_output_coefficients':encode(target),'residual_coefficients':[encode(r) for r in rs],
         'all_ports_and_rows_live':True,'predecessor_relation':relation}

def run_tests(graphs):
 counts={'direct_local_exhaustive':0,'raw_local_exhaustive':0,'raw_linked_constructed_and_false':0,'history_assignments':0,'valid_histories':0,'history_single_port_rejections':0}
 g=graphs['direct_local']
 for C,Cp,B in itertools.product(range(1,9),range(1,9),range(1,7)):
  val=evaluate_new(g,dict(C=C,Cp=Cp,B=B))
  check((val==0)==legal(C,Cp,B),'direct graph');counts['direct_local_exhaustive']+=1
 for q in [5,7]:
  g=graphs['raw_unlinked_q'+str(q)]
  for X,H,Xp,Hp,B in itertools.product(range(1,33),range(1,15),range(1,9),range(1,3),range(1,6)):
   good=q*Hp==H and ((B==1 and X==H and Xp==Hp) or (B==2 and X>H and q*Xp==X-H))
   val=evaluate_new(g,dict(X=X,H=H,Xp=Xp,Hp=Hp,B=B))
   check((val==0)==good,'raw graph');counts['raw_local_exhaustive']+=1
  g=graphs['raw_linked_q'+str(q)]
  for C,Cp,Hp,B in itertools.product(range(1,7),range(1,7),range(1,4),range(1,6)):
   H=q*Hp;values=dict(C=C,Cp=Cp,Hp=Hp,H=H,B=B,X=H*C,Xp=Hp*Cp)
   check((evaluate_new(g,values)==0)==legal(C,Cp,B),'linked graph');counts['raw_linked_constructed_and_false']+=1
  for T in [1,2,4]:
   for x in range(1,T+4):
    for scale in [1,2]:
     vals={'x':x,'H0':q**T*scale}
     for j in range(1,T+1):vals['H'+str(j)]=q**(T-j)*scale;vals['X'+str(j)]=vals['H'+str(j)]*(max(x-j,0)+1)
     for j in range(T):vals['B'+str(j)]=2 if x>j else 1
     g=graphs['raw_T'+str(T)+'_q'+str(q)]
     check((evaluate_new(g,vals)==0)==(x<=T),'raw history');counts['history_assignments']+=1
     if x<=T:
      counts['valid_histories']+=1
      for port in g.ports:
       for shift in [-1,1]:
        if vals[port]+shift<=0:continue
        changed=dict(vals);changed[port]+=shift
        check(evaluate_new(g,changed)!=0,'raw perturbed port')
        counts['history_single_port_rejections']+=1
 for T in [1,2,4]:
  g=graphs['direct_T'+str(T)]
  for x in range(1,T+4):
   vals={'x':x}
   for j in range(1,T+1):vals['C'+str(j)]=max(x-j,0)+1
   for j in range(T):vals['B'+str(j)]=2 if x>j else 1
   check((evaluate_new(g,vals)==0)==(x<=T),'direct history');counts['history_assignments']+=1
   if x<=T:
    counts['valid_histories']+=1
    for port in g.ports:
     for shift in [-1,1]:
      if vals[port]+shift<=0:continue
      changed=dict(vals);changed[port]+=shift
      check(evaluate_new(g,changed)!=0,'direct perturbed port')
      counts['history_single_port_rejections']+=1
 # Explicit domain failures and omitted-integrality boundary, on new graphs only.
 direct=graphs['direct_local']
 check(evaluate_new(direct,dict(C=1,Cp=2,B=0))==0,'nonpositive selector boundary')
 check(evaluate_new(direct,dict(C=1,Cp=0,B=2))==0,'zero output boundary')
 check(evaluate_new(direct,dict(C=1,Cp=Fraction(1,2),B=Fraction(3,2)))==0,'noninteger selector boundary')
 for q in [5,7]:check(evaluate_new(graphs['raw_unlinked_q'+str(q)],dict(X=3*q,H=2*q,Xp=1,Hp=2,B=2))==0,'nonintegral ratio')
 return counts

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
 deps={}
 for name,pin in PINS.items():
  data=(args.root/name).read_bytes();check(sha(data)==pin,'dependency '+name)
  deps[name]={'sha256':pin,'bytes':len(data),'executed_or_imported':False}
 # Read only old declared ledgers/interfaces; never evaluate old arrays.
 old=json.loads((args.root/'markov_projective_counter_step_checks.json').read_bytes())['packets']
 graphs={};packets={}
 def put(name,g,kind,T=None,q=1):graphs[name]=g;packets[name]=check_packet(name,g,kind,T,q)
 put('direct_local',direct_local(),'direct_local')
 for q in [5,7]:
  put('raw_unlinked_q'+str(q),raw_local(q,False),'raw_local_unlinked',q=q)
  put('raw_linked_q'+str(q),raw_local(q,True),'raw_local_linked',q=q)
 for T in [1,2,4]:
  put('direct_T'+str(T),direct_history(T),'direct_history',T)
  check(graphs['direct_T'+str(T)].ports==old['direct_'+str(T)]['ports'],'same direct ports')
  check(old['direct_'+str(T)]['total']==13*T+3,'old direct ledger')
  for q in [5,7]:
   put('raw_T'+str(T)+'_q'+str(q),raw_history(T,q),'raw_history',T,q)
   check(set(graphs['raw_T'+str(T)+'_q'+str(q)].ports)==set(old['raw_'+str(T)]['ports']),'same raw ports')
   check(old['raw_'+str(T)]['total']==19*T+4,'old raw ledger')
 counts=run_tests(graphs)
 result={'schema':'markov-positive-guard-savings-v1','helper_sha256':sha(Path(__file__).read_bytes()),'dependencies':deps,'packets':packets,
         'counts':{'arrays':len(packets),'rows':sum(len(g.rows) for g in graphs.values()),**counts},
         'domain_boundaries':{'B_zero':{'C':1,'Cp':2,'B':0},'Cp_zero':{'C':1,'Cp':0,'B':2},'rational_selector':{'C':'1','Cp':'1/2','B':'3/2'},
                              'nonintegral_raw_ratios':'(X,H,Xp,Hp,B)=(3q,2q,1,2,2), ratios3/2 and1/2'},
         'scope':{'all_size_semantics':'Proof in companion MD','input':'strictly positive integer x','duration':'fixed T>=1, not a quantified source port',
                  'predecessor_array_evaluation':False,'predecessor_execution_import':False,'new_source_arrays_only_executed':True,
                  'universal_compiler_claim':False,'global_optimality_claim':False,'repository_mutation':False},'status':'PASS'}
 with args.output.open('x',encoding='utf-8',newline='\n') as f:json.dump(result,f,sort_keys=True,indent=2);f.write('\n')
 print(json.dumps({'status':'PASS','counts':result['counts']},sort_keys=True))

if __name__=='__main__':main()
