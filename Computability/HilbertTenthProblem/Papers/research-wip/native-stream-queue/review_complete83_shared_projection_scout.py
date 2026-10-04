#!/usr/bin/env python3
"""Independent emitted-data review; executes no author or predecessor program."""
import argparse, collections, hashlib, json
from fractions import Fraction
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
AUTHOR=Path('/tmp')
PINS={
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
 'complete84_scaled_strong_output.py':'8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737'}
APINS={'complete83_shared_projection_scout.py':'2ff8bede5f08b0bc452ca50a432ebc6dbcad5ddd18bd5da5acc2b1d5b189ae9c',
 'complete83_shared_projection_scout.json':'dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c'}
def need(ok,msg):
 if not ok: raise ValueError(msg)
def digest(b):return hashlib.sha256(b).hexdigest()
def pairs(items):
 d={}
 for k,v in items:
  need(k not in d,'duplicate JSON key');d[k]=v
 return d
def read(root,name,pin):
 b=(root/name).read_bytes();need(digest(b)==pin,'pin '+name);return b
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
# Sparse polynomials: a monomial is its sorted tuple of variable indices, with repetitions.
def pc(n):return {():n} if n else {}
def pv(n):return {(n,):1}
def padd(a,b,sign=1):
 c=dict(a)
 for m,v in b.items(): c[m]=c.get(m,0)+sign*v
 return {m:v for m,v in c.items() if v}
def pmul(a,b):
 c={}
 for m,x in a.items():
  for n,y in b.items():
   q=tuple(sorted(m+n));c[q]=c.get(q,0)+x*y
 return {m:v for m,v in c.items() if v}
def ppow(a,n):
 c=pc(1)
 for _ in range(n):c=pmul(c,a)
 return c
def polykey(p):return tuple(sorted(p.items()))
def pserial(p):return [[list(m),v] for m,v in sorted(p.items())]
def polycut(name,by,bounds):
 memo=dict(bounds)
 def rec(x):
  if type(x) is int:return pc(x)
  if x in memo:return memo[x]
  _,op,a,b=by[x];a,b=rec(a),rec(b)
  memo[x]=pmul(a,b) if op=='*' else padd(a,b,1 if op=='+' else -1)
  return memo[x]
 return rec(name)
def inspect(packet):
 rows=packet['source'];free=packet['free'];known=set(free);by={};counts=collections.Counter()
 need(len(known)==len(free),'duplicate free')
 for row in rows:
  need(type(row) is list and len(row)==4,'row format');n,op,a,b=row
  need(type(n) is str and n not in known and op in ('+','-','*'),'gate name/op')
  need(all(type(x) is int or type(x) is str and x in known for x in (a,b)),'topology')
  known.add(n);by[n]=row;counts[op]+=1
 live={'polynomial'}
 for n,op,a,b in reversed(rows):
  need(n in live,'dead row '+n);live.update(x for x in (a,b) if type(x) is str)
 need(set(free)<=live,'dead free')
 return by,{'M':counts['*'],'A':counts['+']+counts['-'],'total':len(rows)}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=ROOT);ap.add_argument('--author-root',type=Path,default=AUTHOR);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);args=ap.parse_args()
 for n,h in PINS.items():read(args.root,n,h)
 for n,h in APINS.items():read(args.author_root,n,h)
 parent=json.loads((args.root/'complete84_scaled_strong_output.json').read_bytes(),object_pairs_hook=pairs)['packet']
 author=json.loads((args.author_root/'complete83_shared_projection_scout.json').read_bytes(),object_pairs_hook=pairs);child=author['packet']
 old,new=parent['source'],child['source'];ob,ol=inspect(parent);nb,nl=inspect(child)
 expected=[]
 for n,op,a,b in old:
  if n in ('gamma_sum','modulus_multiple'):continue
  if n=='gam':expected.append([n,'*','sigma','a4m5'])
  elif n=='R14':expected.extend([['shared_main_partial','+','D1','shared_projection'],[n,'+','shared_main_partial','gam']])
  elif n=='exponent_rhs':expected.append([n,'+','exponent_partial','shared_projection'])
  else:expected.append([n,op,a,b])
 need(expected==new,'entire source reconstruction')
 need(ol=={'M':47,'A':37,'total':84} and nl=={'M':46,'A':37,'total':83},'ledgers')
 need(child['ledger']==nl,'reported ledger')
 need(child['free']==['shared_projection' if x=='rho' else x for x in parent['free']],'free map')
 need(child['witnesses']==['shared_projection' if x=='rho' else x for x in parent['witnesses']],'witness map')
 need(len(child['free'])==25 and len(child['witnesses'])==18,'arity')
 for k in ['ordinary_input','fixed_numerals','factors']:need(child[k]==parent[k],'interface '+k)
 consumers={x:[n for n,op,a,b in old if x in (a,b)] for x in ['rho','gamma_sum','modulus_multiple','gam']}
 need(consumers=={'rho':['gamma_sum','modulus_multiple'],'gamma_sum':['gam'],'modulus_multiple':['exponent_rhs'],'gam':['R14']},'consumer closure')
 need(ob['a4m5']==['a4m5','+','a4',3] and ob['a4']==['a4','*',4,'R12'],'actual H')
 need(sum(ob.get(n)==r for n,*_ in new for r in [nb[n]])==79,'79 literal rows')
 # Exact cuts, with actual named boundaries, not digest equality or a sampled assignment.
 D,H,rho,sigma,E=map(pv,range(5));U=pmul(rho,H)
 oldbounds={'D1':D,'a4m5':H,'rho':rho,'sigma':sigma,'exponent_partial':E}
 newbounds={'D1':D,'a4m5':H,'shared_projection':U,'sigma':sigma,'exponent_partial':E}
 cuts={}
 for name in ['R14','exponent_rhs']:
  a=polycut(name,ob,oldbounds);b=polycut(name,nb,newbounds);need(a==b,'cut '+name);cuts[name]=a
 # Entire-DAG exact expression interning. Only R14 is replaced by its proved
 # polynomial cut; all its atom IDs are actual equal upstream values.
 intern={}
 def node(x):
  if x not in intern:intern[x]=len(intern)
  return intern[x]
 def operation(op,a,b):return node((op,a,b))
 def atom(x,env):return node(('integer',x)) if type(x) is int else env[x]
 def evaluate(rows,ports,rho_id):
  env=dict(ports)
  for n,op,a,b in rows:
   if n=='R14':
    boundids=(env['D1'],env['a4m5'],rho_id,env['sigma'])
    env[n]=node(('proved_main_cut',boundids,polykey(cuts['R14'])))
   else:env[n]=operation(op,atom(a,env),atom(b,env))
  return env
 base={x:node(('variable',x)) for x in parent['free']}
 oe=evaluate(old,base,base['rho'])
 newbase={x:v for x,v in base.items() if x!='rho'}
 newbase['shared_projection']=operation('*',base['rho'],oe['a4m5'])
 ne=evaluate(new,newbase,base['rho'])
 # Auditing the common upstream IDs is essential to binding the formal cut.
 for n in ['D1','a4m5','sigma','exponent_partial']:need(oe[n]==ne[n],'actual boundary '+n)
 common=sorted(set(oe)&set(ne)-{'gam'})
 for n in common:need(oe[n]==ne[n],'retained equality '+n)
 need(len(common)==105,'retained equality census')
 for n in parent['factors']+['polynomial']:need(oe[n]==ne[n],'factor/full output identity')
 # Two exact norm expansions guard all highest-degree cancellations.
 a,c,X,u,sg,Hc=map(pv,range(6));ee=padd(padd(X,u),pmul(sg,Hc))
 main_bounds={'R12':a,'R10a':c,'wn2':X,'shared_projection':u,'sigma':sg,'a4m5':Hc}
 main_form=padd(padd(ppow(ee,2),pmul(pc(2),pmul(pmul(a,c),ee))),pmul(Hc,ppow(c,2)),-1)
 need(polycut('norm_main',nb,main_bounds)==main_form,'actual expanded main norm')
 aa,kap,W,uu,hh=map(pv,range(5));eei=padd(W,uu)
 input_bounds={'R12':aa,'index_rhs':kap,'W':W,'shared_projection':uu,'a4m5':hh}
 input_form=padd(padd(ppow(eei,2),pmul(pc(2),pmul(pmul(aa,kap),eei))),pmul(hh,ppow(kap,2)),-1)
 need(polycut('norm_input',nb,input_bounds)==input_form,'actual expanded input norm')
 # Exact homogeneous leaders with compiler numerals weight zero, still symbolic.
 free=child['free'];ix={n:j for j,n in enumerate(free)};fixed=set(child['fixed_numerals'])
 weights=[0 if n in fixed else 1 for n in free]
 def weight(m):return sum(weights[i] for i in m)
 def lc(n):return (0,pc(n))
 def ladd(x,y,sgn=1):
  dx,p=x;dy,q=y
  if dx>dy:return x
  if dy>dx:return (dy,{m:sgn*v for m,v in q.items()})
  r=padd(p,q,sgn);need(bool(r),'unhandled leading cancellation')
  return dx,r
 def lmul(x,y):return x[0]+y[0],pmul(x[1],y[1])
 def lpower(x,n):
  r=lc(1)
  for _ in range(n):r=lmul(r,x)
  return r
 le={n:(weights[j],pv(j)) for n,j in ix.items()}
 for n,op,left,right in new:
  if n=='norm_main':
   e=ladd(ladd(le['wn2'],le['shared_projection']),lmul(le['sigma'],le['a4m5']))
   le[n]=ladd(ladd(lpower(e,2),lmul(lc(2),lmul(lmul(le['R12'],le['R10a']),e))),lmul(le['a4m5'],lpower(le['R10a'],2)),-1)
  elif n=='norm_input':
   e=ladd(le['W'],le['shared_projection'])
   le[n]=ladd(ladd(lpower(e,2),lmul(lc(2),lmul(lmul(le['R12'],le['index_rhs']),e))),lmul(le['a4m5'],lpower(le['index_rhs'],2)),-1)
  else:
   av=lc(left) if type(left) is int else le[left];bv=lc(right) if type(right) is int else le[right]
   le[n]=lmul(av,bv) if op=='*' else ladd(av,bv,1 if op=='+' else -1)
  need(all(weight(m)==le[n][0] for m in le[n][1]),'homogeneous weight')
 factor_degrees=[le[n][0] for n in child['factors']]
 need(factor_degrees==[22,18,32,60,7,2,46] and le['polynomial'][0]==187,'factor/output degree')
 var=lambda n:pv(ix[n])
 q0=pmul(var('Bm1'),var('Jrep'));k=padd(var('eta'),var('zeta'))
 C1=q0
 for n in ['F','Z','alpha']:C1=padd(C1,var(n),-1)
 C1=padd(C1,pmul(var('twice_cell_bits'),var('x')),-1)
 transport=padd(pmul(var('w'),C1),pmul(var('transport_quotient'),q0),-1)
 lead=pc(32)
 for factor,n in [(q0,111),(var('h'),1),(var('sigma'),1),(var('delta'),2),(var('i'),4),(k,13),(var('w'),18),(var('s'),31),(transport,1),(var('auxiliary_quotient'),2),(var('f'),2)]:lead=pmul(lead,ppow(factor,n))
 need(le['polynomial'][1]==lead,'uniform complete leading form')
 term={'Bm1':112,'Jrep':112,'h':1,'sigma':1,'delta':2,'i':4,'eta':13,'w':18,'s':31,'transport_quotient':1,'auxiliary_quotient':2,'f':2}
 mon=tuple(sorted(j for n,power in term.items() for j in [ix[n]]*power))
 need(lead[mon]==-32,'uniform nonzero monomial')
 ordinary_mon=tuple(j for j in mon if weights[j])
 matches={m:v for m,v in lead.items() if tuple(j for j in m if weights[j])==ordinary_mon}
 need(matches=={mon:-32},'no coefficient cancellation after fixed-numeral specialization')
 # Signed/rational full row evaluations are supplementary, not identity evidence.
 def numeric(rows,ports):
  env=dict(ports)
  for n,op,a,b in rows:
   x=a if type(a) is int else env[a];y=b if type(b) is int else env[b]
   env[n]=x*y if op=='*' else x+y if op=='+' else x-y
  return env
 checks=0
 for case in range(12):
  ports={n:Fraction(((j+3)*(case+7))%17-8,1 if case<6 else j%4+1) for j,n in enumerate(parent['free'])}
  xenv=numeric(old,ports);np={n:v for n,v in ports.items() if n!='rho'};np['shared_projection']=ports['rho']*xenv['a4m5'];yenv=numeric(new,np)
  for n in common:need(xenv[n]==yenv[n],'numeric retained '+n);checks+=1
 result={'scope':'Independent exact source/all-ring forward-map/degree audit only; no positive inverse without divisibility and no new universality claim',
 'author_pins':APINS,'parent_pins':PINS,'reviewer_sha256':digest(Path(__file__).read_bytes()),
 'source':{'parent_ledger':ol,'ledger':nl,'witnesses':18,'free_ports':25,'literal_unchanged_rows':79,'all_rows_live':True,'all_ports_live':True,'source_sha256':digest(canonical(new)),'consumer_sets':consumers},
 'identity':{'cut_variable_order':['D1','H','rho','sigma','exponent_partial'],'cuts':{n:pserial(p) for n,p in cuts.items()},'actual_boundary_registers':['D1','a4m5','sigma','exponent_partial'],'retained_value_equalities':len(common),'exception':'gam','all_seven_factors_and_output_equal':True,'finalizer_rows':[r for r in new if r[0] in ['norm_pair','norm_triple','norm_four','norm_product','all_units','seven_units','polynomial']]},
 'degree':{'fixed_numerals_weight':0,'other_free_ports_weight':1,'factor_degrees':factor_degrees,'exact_degree':187,'main_cut_terms':len(main_form),'input_cut_terms':len(input_form),'leading_terms':len(lead),'leading_sha256':digest(canonical(pserial(lead))),'uniform_monomial_exponents':term,'uniform_monomial_coefficient':-32,'nonzero_after_valid_numeral_specialization':'-32*(Bm1)^112, and valid Bm1>0'},
 'supplementary_numeric':{'assignments':12,'rational_assignments':6,'retained_equalities':checks,'full_positive_zeros_materialized':0},
 'execution':{'predecessor_or_author_programs_run':False,'inputs_read_as_bytes_json_only':True}}
 encoded=json.dumps(result,sort_keys=True,indent=2)+'\n'
 if args.expect:need(args.expect.read_text()==encoded,'receipt replay')
 if args.output:
  with args.output.open('x') as f:f.write(encoded)
 print(json.dumps({'ledger':nl,'degree':187,'retained_identities':len(common),'receipt_sha256':digest(encoded.encode())},sort_keys=True))
if __name__=='__main__':main()
