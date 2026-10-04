#!/usr/bin/env python3
"""Independent sparse all-value audit of fresh finite-word source JSON only."""
import argparse,collections,hashlib,itertools,json
from pathlib import Path

def need(b,m):
 if not b:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def add(a,b,sgn=1):
 c=dict(a)
 for m,k in b.items():c[m]=c.get(m,0)+sgn*k
 return {m:k for m,k in c.items() if k}
def mul(a,b):
 c={}
 for u,x in a.items():
  for v,y in b.items():
   m=tuple(sorted(u+v));c[m]=c.get(m,0)+x*y
 return {m:k for m,k in c.items() if k}
def const(c):return {():c} if c else {}
def scale(a,c):return {m:k*c for m,k in a.items() if k*c}
def evaluate(rows,ports,assignment):
 env=dict(assignment)
 for name,op,a,b in rows:
  x=a if type(a)is int else env[a];y=b if type(b)is int else env[b]
  env[name]=x*y if op=='*' else x+y if op=='+' else x-y
 return env

def audit(p):
 n=p['n_fixed'];P=1<<((n-1)**2);Q=1<<n
 ports=p['parameters']+p['positive_witnesses'];need(len(ports)==len(set(ports))==2*n+7,'port census')
 need(p['parameters']==['x','y','Hhat'],'external parameters')
 need(p['positive_witnesses']==[f'{s}{k}_hat' for s in ['a','b'] for k in range(n)]+['low_hat','high_hat','low_slack','output_slack'],'witness order')
 env={v:{(i,):1} for i,v in enumerate(ports)};base=dict(env)
 def get(v):return const(v) if type(v)is int else env[v]
 defs={};uses=collections.Counter()
 for name,op,a,b in p['full_rows']:
  need(name not in env and op in ['+','-','*'],'unique acyclic definition')
  need(all(type(z)is int or z in env for z in [a,b]),'paid dependency')
  env[name]=mul(get(a),get(b)) if op=='*' else add(get(a),get(b),1 if op=='+' else -1)
  defs[name]=(op,a,b)
  for z in [a,b]:
   if type(z)is str:uses[z]+=1
 live=set();todo=[p['output']]
 while todo:
  v=todo.pop()
  if type(v)is int or v in live:continue
  live.add(v)
  if v in defs:todo.extend(defs[v][1:])
 need(set(defs)|set(ports)<=live,'full live closure')
 # Textbook independent expansion using only the supplied port symbols.
 ab=[[add(base[f'{s}{k}_hat'],const(1),-1) for k in range(n)] for s in ['a','b']]
 residuals=[mul(x,add(x,const(1),-1)) for xs in ab for x in xs]
 def weighted(xs,coeffs):
  ans={}
  for x,c in zip(xs,coeffs):ans=add(ans,scale(x,c))
  return ans
 x=weighted(ab[0],[1<<k for k in range(n)]);y=weighted(ab[1],[1<<k for k in range(n)])
 A=weighted(ab[0],[1<<(n*k) for k in range(n)]);C=weighted(ab[1],[1<<((n-1)*(n-1-k)) for k in range(n)])
 residuals.extend([add(x,base['x'],-1),add(y,base['y'],-1)])
 r=add(mul(A,C),const(P*Q+P+1))
 for port,c in [('low_hat',1),('Hhat',P),('high_hat',P*Q)]:r=add(r,scale(base[port],c),-1)
 residuals.extend([r,add(add(base['low_hat'],base['low_slack']),const(P+1),-1),add(add(base['Hhat'],base['output_slack']),const(Q+1),-1)])
 for nm,expected_cut in [(f'input_x_join{n-2}',x),(f'input_y_join{n-2}',y),(f'spread_a_join{n-2}',A),(f'reverse_spread_b_join{n-2}',C)]:need(env[nm]==expected_cut,'exact actual loader binding')
 need([env[nm] for nm in p['boolean_zero_registers']]==residuals[:2*n],'all actual bit guard polynomials')
 need([add(get(a),get(b),-1) for a,b in p['comparisons']]==residuals[2*n:],'all actual comparison polynomials')
 expected={}
 for r in residuals:expected=add(expected,mul(r,r))
 need(env[p['output']]==expected,'exact full-output polynomial identity')
 need(max(map(len,expected))==4,'exact quartic')
 constructed=p.get('construct_constants',False)
 mu=lambda k:len(bin(k))-3+bin(k).count('1')-1
 cm=mu(n)+mu(n-1)+mu((n-1)**2)+1 if constructed else 0;ca=4 if constructed else 0
 prefix=cm+ca
 need(len(p['certificate_rows'])==14*n+prefix,'certificate length')
 need(p['full_rows'][:14*n+prefix]==p['certificate_rows'],'certificate prefix')
 if constructed:
  need(all(v in [1,2] for r in p['full_rows'] for v in r[2:] if type(v)is int),'only literal1/2')
  need(all(set(env[r[0]])<=set([()]) for r in p['full_rows'][:prefix]),'constant-only prefix')
  need(env['const_offset']==const(P*Q+P+1),'computed offset')
  need(env['const_Pplus1']==const(P+1) and env['const_Qplus1']==const(Q+1),'computed bounds')
 counts=collections.Counter(r[1] for r in p['full_rows']);need(counts['*']==8*n+4+cm and counts['+']+counts['-']==10*n+10+ca,'full ledger')
 cc=collections.Counter(r[1] for r in p['certificate_rows']);need(cc['*']==6*n-1+cm and cc['+']+cc['-']==8*n+1+ca,'certificate ledger')
 need(p['full_polynomial_cost']=={'M':counts['*'],'A':counts['+']+counts['-'],'total':len(defs)},'full metadata ledger')
 need(p['certificate_cost']=={'M':cc['*'],'A':cc['+']+cc['-'],'total':len(p['certificate_rows'])},'certificate metadata ledger')
 need(p['equations']==2*n+5 and p['witness_count']==2*n+4,'metadata arity')
 cases=0;rejections=0
 # Complete words for n<=5; all zero/all one and one-hot pairs for larger emitted n.
 pairs=itertools.product(range(Q),repeat=2) if n<=5 else itertools.chain([(0,0),(0,Q-1),(Q-1,0),(Q-1,Q-1)],itertools.product([1<<k for k in range(n)],repeat=2))
 for x,y in pairs:
  aa=[(x>>k)&1 for k in range(n)];bb=[(y>>k)&1 for k in range(n)]
  av=sum(a*(1<<(n*k)) for k,a in enumerate(aa));cv=sum(b*(1<<((n-1)*(n-1-k))) for k,b in enumerate(bb));prod=av*cv
  hi,rem=divmod(prod,P*Q);mid,lo=divmod(rem,P)
  need(mid==x&y,'actual extracted bitmask')
  vals={'x':x,'y':y,'Hhat':mid+1,'low_hat':lo+1,'high_hat':hi+1,'low_slack':P-lo,'output_slack':Q-mid}
  vals.update({f'{s}{k}_hat':bits[k]+1 for s,bits in [('a',aa),('b',bb)] for k in range(n)})
  need(all(vals[w]>0 for w in p['positive_witnesses']) and vals['Hhat']>0,'positive existence incl zero endpoints')
  need(evaluate(p['full_rows'],ports,vals)[p['output']]==0,'full-DAG positive zero');cases+=1
  for port in ['Hhat','x','y','a0_hat','low_hat','high_hat','low_slack','output_slack']:
   bad=dict(vals);bad[port]+=1;need(evaluate(p['full_rows'],ports,bad)[p['output']]>0,'single-port rejection');rejections+=1
 # Exact polynomial coefficient digest, not used as equality oracle above.
 encoding=json.dumps([[list(m),v] for m,v in sorted(expected.items())],separators=(',',':')).encode()
 return {'n':n,'constructed_constants':constructed,'prefix_M':cm,'prefix_A':ca,'rows':len(defs),'ports':len(ports),'witnesses':len(p['positive_witnesses']),'M':counts['*'],'A':counts['+']+counts['-'],'polynomial_terms':len(expected),'polynomial_sha256':sha(encoding),'degree':4,'positive_zeros':cases,'perturbations_rejected':rejections,'all_rows_ports_live':True}

def audit_variable(vp):
 ports=['A','C','P','Q','Hhat','low_hat','high_hat','low_slack','output_slack']
 env={p:{(i,):1} for i,p in enumerate(ports)};base=dict(env)
 def get(v):return const(v) if type(v)is int else env[v]
 rows=vp['rows']
 for name,op,a,b in rows:
  need(name not in env and op in ['+','-','*'],'variable graph')
  env[name]=mul(get(a),get(b)) if op=='*' else add(get(a),get(b),1 if op=='+' else -1)
 expected=add(mul(base['A'],base['C']),const(1))
 expected=add(expected,base['P'])
 expected=add(expected,base['low_hat'],-1)
 h=add(base['Hhat'],mul(base['Q'],add(base['high_hat'],const(1),-1)))
 expected=add(expected,mul(base['P'],h),-1)
 need(add(env['lhs'],env['rhs'],-1)==expected,'variable exact decomposition')
 need(len(rows)==11 and sum(r[1]=='*' for r in rows)==3,'11 conditional producers')
 tested=0
 for P,Q,A,C in itertools.product(range(1,4),range(2,6),range(8),range(8)):
  hi,rem=divmod(A*C,P*Q);mid,lo=divmod(rem,P)
  vals={'A':A,'C':C,'P':P,'Q':Q,'Hhat':mid+1,'low_hat':lo+1,'high_hat':hi+1,'low_slack':P-lo,'output_slack':Q-mid}
  envnum=evaluate(rows,ports,vals)
  need(all(envnum[a]==envnum[b] for a,b in vp['comparisons']),'conditional extraction endpoint')
  need(all(vals[p]>0 for p in ports if p not in ['A','C']),'conditional positivity');tested+=1
 return {'rows':11,'M':3,'A':8,'comparisons':3,'bounded_positive_extractions':tested,'exact_polynomial_decomposition':True,'not_a_complete_AND_loader':True}

def unique(pairs):
 ans={}
 for k,v in pairs:
  need(k not in ans,'duplicate JSON key');ans[k]=v
 return ans

def type_equal(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(type_equal(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(type_equal(x,y) for x,y in zip(a,b))
 return a==b

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,default=Path('/tmp/finite_word_hadamard_skew.json'))
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 a=ap.parse_args();b=a.source.read_bytes();data=json.loads(b,object_pairs_hook=unique)
 pins=[]
 for ext in ['py','json','md']:
  p=a.source.with_suffix('.'+ext);z=p.read_bytes();pins.append({'name':p.name,'bytes':len(z),'sha256':sha(z),'read_scope':'complete text' if ext in ['py','md'] else 'complete machine source arrays and metadata'})
 need(data['source_sha256']==pins[0]['sha256'],'source receipt byte binding')
 packets=[audit(p) for p in data['complete_fixed_n_sources']]
 out={'author_trio':pins,'review_helper_sha256':sha(Path(__file__).read_bytes()),'scope':'Fresh independent exact polynomial expansion, DAG liveness and bounded integer evaluations; no predecessor import/execution.','packets':packets,'variable_interface':audit_variable(data['variable_power_interface'])}
 # Concrete necessity of strict output positivity, outside the asserted domain.
 p=next(p for p in data['complete_fixed_n_sources'] if p['n_fixed']==2 and not p['construct_constants'])
 vals={'x':3,'y':3,'Hhat':0,'low_hat':2,'high_hat':3,'low_slack':1,'output_slack':5}
 vals.update({f'{s}{i}_hat':2 for s in ['a','b'] for i in range(2)})
 need(evaluate(p['full_rows'],[],vals)[p['output']]==0,'Hhat0 excluded-domain alias')
 out['strict_Hhat_positivity_necessary']={'excluded_tuple':vals,'full_polynomial':0,'correct_Hhat':4,'not_a_counterexample_to_positive_domain':True}
 out['totals']={key:sum(q[key] for q in packets) for key in ['rows','polynomial_terms','positive_zeros','perturbations_rejected']}
 if a.output:
  with a.output.open('x') as f:json.dump(out,f,indent=2);f.write('\n')
 else:
  saved=json.loads(a.expect.read_text(),object_pairs_hook=unique);need(type_equal(out,saved),'review receipt equality')
 print(json.dumps({'status':'PASS','totals':out['totals'],'author_trio':pins,'variable_interface':out['variable_interface']}))
if __name__=='__main__':main()
