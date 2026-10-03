#!/usr/bin/env python3
"""Independent bounded receipt/source review; does not import the scout."""
import argparse, hashlib, itertools, json, math, random
from collections import Counter
from fractions import Fraction
from pathlib import Path
import sympy as sp

if not __debug__: raise RuntimeError('Run without -O')
SOURCE_PIN='24728e3c3bd4f3b24a929ad816b9a4b4110678923ca50499dcf02c96eb6ac61f'
RECEIPT_PIN='dc2d26d1f88144bf92fe5e867c78669531a5f117075ab691d98486f60254e810'
NOTE_PIN='1501ac846c4d617d37df8db144ae0388b4826c69355c0da3f18f3bafc475f9c6'
PARENT_PINS={
 'complete86_factored_first_root.py':'29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f',
 'complete86_factored_first_root.json':'2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e',
 'complete86_factored_first_root.md':'9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b'}
FACTORS=('norm_first','norm_main','norm_input','norm_index','norm_transport','norm_linear')

def sha(b): return hashlib.sha256(b).hexdigest()
def same(a,b):
 if type(a) is not type(b): return False
 if type(a) is dict: return a.keys()==b.keys() and all(same(a[k],b[k]) for k in a)
 if type(a) is list: return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
 return a==b

def check_rows(rows,out):
 assert type(rows) is list
 names=set(); free=set(); nodes={}; M=0
 for r in rows:
  assert type(r) is list and len(r)==4
  n,op,a,b=r;assert type(n) is str and n not in names and op in ('+','-','*')
  for v in (a,b):
   assert type(v) in (int,str)
   if type(v) is str and v not in names: free.add(v)
  names.add(n); nodes[n]=(op,a,b);M+=op=='*'
 assert not free & names
 seen=set();todo=[out]
 while todo:
  n=todo.pop()
  if type(n) is str and n in nodes and n not in seen:
   seen.add(n);todo.extend(nodes[n][1:])
 assert seen==names
 return {'operations':len(rows),'M':M,'A':len(rows)-M,'free':sorted(free),'live':len(seen)}

def expand_cut(rows,out,cuts):
 nodes={n:(op,a,b) for n,op,a,b in rows}; memo=dict(cuts)
 def get(v):
  if type(v) is int:return sp.Integer(v)
  if v not in memo:
   assert v in nodes,('unbound cut',v)
   op,a,b=nodes[v];a,b=get(a),get(b)
   memo[v]=sp.expand(a*b if op=='*' else a+b if op=='+' else a-b)
  return memo[v]
 return get(out)

def signatures(rows,roots,intern):
 table={n:(op,a,b) for n,op,a,b in rows};memo={}
 def atom(k):
  if k not in intern:intern[k]=len(intern)
  return intern[k]
 def get(v):
  if type(v) is int:return atom(('integer',v))
  if v not in table:return atom(('free',v))
  if v not in memo:
   op,a,b=table[v];a,b=get(a),get(b)
   if op in ('+','*'):a,b=sorted((a,b))
   memo[v]=atom((op,a,b))
  return memo[v]
 return [get(r) for r in roots]

def recse(rows,out):
 env={};seen={};new=[]
 for n,op,a,b in rows:
  a=env.get(a,a);b=env.get(b,b)
  if type(a) is int and type(b) is int: z=a*b if op=='*' else a+b if op=='+' else a-b
  elif op=='+' and (a==0 or b==0):z=b if a==0 else a
  elif op=='-' and (b==0 or a==b):z=a if b==0 else 0
  elif op=='*' and (a in (0,1) or b in (0,1)):z=0 if a==0 or b==0 else b if a==1 else a
  else:
   if op in ('+','*') and repr(a)>repr(b):a,b=b,a
   k=op,a,b
   if k not in seen:seen[k]='c'+str(len(new));new.append([seen[k],op,a,b])
   z=seen[k]
  env[n]=z
 return new,env[out]

def value(rows,out,values):
 vals=dict(values)
 for n,op,a,b in rows:
  a=a if type(a) is int else vals[a];b=b if type(b) is int else vals[b]
  vals[n]=a*b if op=='*' else a+b if op=='+' else a-b
 return vals[out]

def restricted_growth_partitions(n):
 # Independent enumeration by restricted growth words, not incremental block mutation.
 out=[]
 for w in itertools.product(range(n),repeat=n):
  if w[0] or any(w[i]>1+max(w[:i]) for i in range(1,n)):continue
  out.append(tuple(tuple(i for i in range(n) if w[i]==j) for j in range(1+max(w))))
 return out

def verify(source,receipt,note,root):
 for path,pin in [(source,SOURCE_PIN),(receipt,RECEIPT_PIN),(note,NOTE_PIN)]:assert sha(path.read_bytes())==pin
 for name,pin in PARENT_PINS.items():assert sha((root/name).read_bytes())==pin
 r=json.loads(receipt.read_text()); parent=json.loads((root/'complete86_factored_first_root.json').read_text())['forms'][0]
 old=parent['source']; base=check_rows(old,'polynomial');assert base==r['baseline']
 assert (base['operations'],base['M'],base['A'])==(86,48,38)
 assert len(parent['witnesses'])==19 and 'tau_root' in parent['witnesses']
 expectedfree=set(parent['witnesses'])|{'x','Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF'}
 assert set(base['free'])==expectedfree
 cse,out=recse(old,'polynomial');assert check_rows(cse,out)==base
 ps=restricted_growth_partitions(6);assert len(ps)==len(set(ps))==203
 perms=list(itertools.permutations(range(5)));assert len(perms)==120
 assert r['choices']==6*2*len(ps)*len(perms)==292320
 assert (r['chart_count'],r['factorization_modes'],r['set_partitions'],r['orders_per_chart'])==(6,2,203,120)
 assert len(r['summaries'])==len(r['best_sources'])==12
 assert sum(s['distinct_local_sources'] for s in r['summaries'])==58113==r['distinct_local_source_proofs']
 assert r['whole_finalizer_identities']==58113 and r['retained_factor_DAG_identities']==6*58113
 A,i,c,f,V,y=sp.symbols('A i c f V y');t=i*c**2;H=A*t;Q=A*t**2;K=A*Q
 target=sp.expand((f*f-Q)*(K*(V*V-y*y)+y*y))
 ports={'A':A,'ic2':t,'ic22':t*t,'shared_H':H,'L16':f*f,'strong_difference':Q,'R16':K,'H2':V*V,'aux_y2':y*y,'f':f,'aux_u_rhs':V,'y_aux':y}
 charts={
 'QK':(['L16','strong_difference','R16','H2','aux_y2'],'separate_powers'),
 'QA':(['L16','strong_difference','A','H2','aux_y2'],'separate_powers'),
 'T2A':(['L16','ic22','A','H2','aux_y2'],'separate_powers'),
 'tH':(['L16','ic2','shared_H','H2','aux_y2'],'separate_powers'),
 'raw_tH_separate_powers':(['f','ic2','shared_H','aux_u_rhs','y_aux'],'separate_powers'),
 'raw_tH_joint_square':(['f','ic2','shared_H','aux_u_rhs','y_aux'],'joint_square')}
 v=sp.symbols('v0:5');F,q,k,u,Y=v
 generic={
 'QK':(F-q)*(k*(u-Y)+Y),
 'QA':(F-q)*(k*q*(u-Y)+Y),
 'T2A':(F-k*q)*(k*k*q*(u-Y)+Y),
 'tH':(F-q*k)*(k*k*(u-Y)+Y),
 'raw_tH_separate_powers':(F*F-q*k)*(k*k*(u*u-Y*Y)+Y*Y),
 'raw_tH_joint_square':(F*F-q*k)*(k*k*(u*u-Y*Y)+Y*Y)}
 for name,(pp,_) in charts.items():
  assert len(sp.Poly(sp.expand(generic[name]),*v).terms())==6
  assert sp.expand(generic[name].subs(dict(zip(v,[ports[k] for k in pp])),simultaneous=True))==target
 oldcuts={'A':A,'i':i,'R10a':c,'f':f,'aux_u_rhs':V,'y_aux':y}
 assert sp.expand(expand_cut(old,'norm_strong',oldcuts)*expand_cut(old,'norm_aux',oldcuts))==target
 intern={};oldfactor=signatures(old,FACTORS,intern);nn=sp.symbols('n0:8')
 assert expand_cut(old,'polynomial',{**dict(zip(FACTORS,nn[:6])),'norm_strong':nn[6],'norm_aux':nn[7]})==sp.prod(nn)-1
 rng=random.Random(870063);counts=Counter();results=[]
 for s,b in zip(r['summaries'],r['best_sources']):
  assert s['chart']==b['chart']; suffix='_binomial_factors' if b['binomial_factorization'] else '_monomial_factors'
  assert b['chart'].endswith(suffix);chart=b['chart'][:-len(suffix)]
  assert b['ports']==charts[chart][0] and b['style']==charts[chart][1]
  assert tuple(tuple(x) for x in b['partition']) in ps and tuple(b['order']) in perms
  assert sum(h['choices'] for h in s['histogram'])==24360==s['choices']
  assert all(type(h['choices']) is int and h['choices']>0 for h in s['histogram'])
  assert s['best']==min(h['cost'] for h in s['histogram'])
  led=check_rows(b['source'],b['output']);assert led==b['ledger']
  assert [led['operations'],led['M'],led['A']]==s['best'] and led['free']==base['free']
  re,ro=recse(b['source'],b['output']);assert check_rows(re,ro)==led
  local=expand_cut(b['local_source'],b['local_output'],dict(zip(['v'+str(j) for j in range(5)],v)))
  assert sp.expand(local-generic[chart])==0;counts['generic_local_polynomial_identities']+=1
  assert signatures(b['source'],[b['aliases'][k] for k in FACTORS],intern)==oldfactor;counts['unchanged_factor_DAG_identities']+=6
  cuts={b['aliases']['A']:A,'i':i,b['aliases']['R10a']:c,'f':f,b['aliases']['aux_u_rhs']:V,'y_aux':y}
  assert len(cuts)==6
  assert expand_cut(b['source'],b['joint_output'],cuts)==target;counts['actual_paid_joint_polynomial_identities']+=1
  joint=sp.Symbol('Joint');cc={b['aliases'][k]:nn[j] for j,k in enumerate(FACTORS)};cc[b['joint_output']]=joint
  assert expand_cut(b['source'],b['output'],cc)==sp.prod(nn[:6])*joint-1;counts['complete_polynomial_cut_proofs']+=1
  for j in range(12):
   vals={k:rng.randrange(-3,4) for k in base['free']}
   if j>=8:vals={k:Fraction(x,2) for k,x in vals.items()}
   assert value(old,'polynomial',vals)==value(b['source'],b['output'],vals)
   counts['full_numeric_checks']+=1;counts['rational_checks']+=j>=8
  counts['fully_recounted_live_gates']+=len(b['source'])
  results.append({'chart':b['chart'],'cost':s['best'],'generic_monomials':6,'same_full_polynomial':True})
 assert r['exact_degree']==179 and min(x['cost'][0] for x in results)==86
 return {'status':'PASS_BOUNDED_INDEPENDENT_REVIEW','review_source_sha256':sha(Path(__file__).read_bytes()),
 'source_pin':SOURCE_PIN,'receipt_pin':RECEIPT_PIN,'note_pin':NOTE_PIN,'parent_pins':PARENT_PINS,
 'counts':dict(counts,paid_chart_identities=6,independent_set_partitions=len(ps),variable_orders=len(perms),declared_schedules=292320),
 'baseline':base,'representatives':results,
 'scope':'Independently reconstructs all12 saved best full sources and six paid charts. Finite census coverage follows inspected source loops and independent203x120 combinatorics; full292320 cost histograms are authenticated author results, not independently rerun. Exact degree179 transfers by full polynomial equality; no general lower bound.'}

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 for n in ('source','receipt','note','root'):ap.add_argument('--'+n,type=Path,required=True)
 ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args()
 result=verify(a.source,a.receipt,a.note,a.root)
 if a.expect:assert same(result,json.loads(a.expect.read_text()))
 if a.output:a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':result['status'],'counts':result['counts']}))
if __name__=='__main__':main()
