"""Fresh exact rational-root algebra scout; frozen source is inert JSON only."""
import argparse,hashlib,json
from collections import Counter
from pathlib import Path

PIN='8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf'
def need(x,m):
 if not x:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def add(a,b,s=1):
 out=dict(a)
 for m,c in b.items():out[m]=out.get(m,0)+s*c
 return {m:c for m,c in out.items()if c}
def mul(a,b):
 out={}
 for m,c in a.items():
  for n,d in b.items():
   k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
 return {m:c for m,c in out.items()if c}
def num(c):return {():c}if c else{}
def var(n):return {(n,):1}
def sq(p):return mul(p,p)
def times(*polys):
 out=num(1)
 for p in polys:out=mul(out,p)
 return out
def encode(p):return [[list(m),c]for m,c in sorted(p.items())]
def value(p,assignment):
 out=0
 for m,c in p.items():
  for n in m:c*=assignment[n]
  out+=c
 return out

LOCAL=[
 ['rr_ic2','*','i','c2'],['rr_dprod','*','S','rr_ic2'],['rr_D','+','rr_dprod',1],
 ['rr_RD','*','R','rr_D'],['rr_b','+','c','rr_RD'],['rr_cT','*','c','T'],
 ['rr_cT2','*','rr_cT','rr_cT'],['rr_DcT2','*','rr_D','rr_cT2'],['rr_b2','*','rr_b','rr_b'],
 ['rr_sum','+','rr_DcT2','rr_b2'],['rr_gap','-','rr_sum','y2'],['rr_Qgap','*','Q','rr_gap'],
 ['rr_Aplus','+','rr_Qgap','y2'],['rr_A','-','rr_Aplus',1],
 ['rr_QcT','*','Q','rr_cT'],['rr_QcTb','*','rr_QcT','rr_b'],['rr_B','+','rr_QcTb','rr_QcTb'],
 ['rr_A2','*','rr_A','rr_A'],['rr_B2','*','rr_B','rr_B'],['rr_DB2','*','rr_D','rr_B2'],
 ['rr_K','-','rr_A2','rr_DB2'],
]

def build(root):
 raw=(root/'complete84_scaled_strong_output.json').read_bytes();need(sha(raw)==PIN,'actual84 pin')
 source=json.loads(raw)['packet'];rows=source['source'];defs={r[0]:r for r in rows}
 need(len(defs)==84 and len(source['free'])==25,'full source census')
 dependencies={n:{n}for n in source['free']}
 for n,o,a,b in rows:
  need(n not in dependencies and o in('+','-','*'),'SSA schema')
  need(all(type(x)is int or x in dependencies for x in(a,b)),'source closure')
  dependencies[n]=set().union(*(dependencies[x]for x in(a,b)if type(x)is str))
 independent=[n for n in dependencies if 'f'not in dependencies[n]]
 computed=[n for n in independent if n in defs];supplied=[n for n in independent if n not in defs]
 need(len(computed)==67 and len(supplied)==24,'actual91 census')
 direct=[r for r in rows if 'f'in r[2:]]
 need(direct==[['L16','*','f','f'],['auxiliary_Tf','*','auxiliary_quotient','f']],'all direct f consumers')
 Delta,c,R,i,T,y,f=map(var,['Delta','c','R','i','T','y','f'])
 c2=sq(c);S=times(Delta,i,c2);Q=sq(S)
 D=add(num(1),times(Delta,sq(i),sq(c2)));b=add(c,mul(R,D))
 V=add(add(times(c,T,f),c,-1),times(R,sq(f)),-1)
 Na=add(mul(Q,add(sq(V),sq(y),-1)),sq(y));Ns=add(mul(Delta,sq(f)),Q,-1)
 A=add(add(mul(Q,add(times(c2,D,sq(T)),sq(b))),mul(add(Q,num(1),-1),sq(y)),-1),num(1),-1)
 B=times(num(2),Q,c,T,b);E=add(sq(f),D,-1);K=add(sq(A),mul(D,sq(B)),-1)
 cuts={'A':Delta,'R10a':c,'r_lhs':R,'i':i,'auxiliary_quotient':T,'y_aux':y,'f':f}
 factors=['norm_first','norm_main','norm_input','norm_index','norm_transport']
 cuts.update({n:var(n)for n in factors})
 memo=dict(cuts)
 def at(n):
  if type(n)is int:return num(n)
  if n not in memo:
   need(n in defs,'unbound actual cut '+n)
   _,o,a,b=defs[n];a,b=at(a),at(b)
   memo[n]=mul(a,b)if o=='*'else add(a,b,1 if o=='+'else-1)
  return memo[n]
 for n,p in [('c2',c2),('Ac2',mul(Delta,c2)),('aux_coefficient_root',S),('R16',Q),
             ('aux_u_rhs',V),('norm_aux',Na),('norm_strong',Ns)]:need(at(n)==p,'actual source producer '+n)
 P5=times(*(var(n)for n in factors))
 need(at('polynomial')==add(times(P5,Na,Ns),Delta,-1),'entire source finalizer binding')
 quotient=times(Q,add(add(times(c2,sq(T)),times(num(2),R,c,T,f),-1),
                     add(times(num(2),R,b),times(sq(R),E))))
 need(add(add(Na,num(1),-1),add(A,mul(B,f),-1),-1)==mul(E,quotient),'exact strong-remainder identity')
 need(add(Ns,Delta,-1)==mul(Delta,E),'actual scaled strong identity')
 # Full output modulo E, obtained by explicit ideal membership rather than a
 # numerical specialization: F-Delta[P5(A-Bf+1)-1] = P5 E(Delta*q+Delta*Na).
 contracted=mul(Delta,add(mul(P5,add(add(A,mul(B,f),-1),num(1))),num(1),-1))
 need(add(at('polynomial'),contracted,-1)==times(P5,Delta,E,add(quotient,Na)),
      'full output strong-ideal remainder')
 local={'Delta':Delta,'c':c,'c2':c2,'i':i,'S':S,'Q':Q,'R':R,'T':T,'y2':sq(y)}
 for n,o,a,b0 in LOCAL:
  a=num(a)if type(a)is int else local[a];b0=num(b0)if type(b0)is int else local[b0]
  local[n]=mul(a,b0)if o=='*'else add(a,b0,1 if o=='+'else-1)
 need(local['rr_D']==D and local['rr_b']==b and local['rr_A']==A and local['rr_B']==B and local['rr_K']==K,'paid local outputs')
 d={r[0]:r for r in LOCAL};live=set();todo=['rr_K']
 while todo:
  n=todo.pop()
  if type(n)is str and n in d and n not in live:live.add(n);todo.extend(d[n][2:])
 need(live==set(d),'all21 local rows live')
 fixture={'Delta':8,'c':1,'i':1,'R':1,'T':81,'y':255,'f':-3}
 sample={n:value(p,fixture)for n,p in [('D',D),('Q',Q),('b',b),('A',A),('B',B),('K',K),('Na',Na),('Ns',Ns)]}
 need(sample=={'D':9,'Q':64,'b':10,'A':-311040,'B':103680,'K':0,'Na':1,'Ns':8},'negative-root local diagnostic')
 need(value(add(A,mul(B,f),-1),fixture)==0,'local rational reconstruction')
 op=Counter(r[1]for r in LOCAL);need((len(LOCAL),op['*'],op['+']+op['-'])==(21,13,8),'local ledger')
 return {'scope':'Bounded exact rational reconstruction scout, not a new universal polynomial or witness/gate bound',
 'source_sha256':sha(Path(__file__).read_bytes()),'actual84_json_sha256':PIN,
 'f_independent_computed':computed,'f_independent_supplied':supplied,'direct_f_consumers':direct,
 'actual_boundaries':{k:encode(v)for k,v in cuts.items()},
 'polynomials':{n:encode(p)for n,p in [('D',D),('b',b),('Q',Q),('A',A),('B',B),('K',K),('E',E),('auxiliary_remainder_quotient',quotient)]},
 'exact_checks':['actual source producers','whole original finalizer','Ns-Delta=Delta*E',
                 'Na-1-(A-Bf)=E*auxiliary_remainder_quotient','whole output modulo E','all21 local producer outputs and liveness'],
 'local_paid_source':LOCAL,'local_ledger':{'operations':21,'M':13,'A':8},
 'local_paid_ports':['Delta','c','c2','i','S','Q','R','T','y2'],
 'negative_root_component_only':{'assignment':fixture,'computed':sample,'native_full_tuple':False},
 'frozen_programs_executed_or_imported':False}

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
 result=build(args.root)
 with args.output.open('x')as stream:json.dump(result,stream,sort_keys=True,indent=2);stream.write('\n')
 print('PASS rational identity, actual91 boundary, local21 ledger, negative-root component')
