#!/usr/bin/env python3
"""Independent final complete86/87 source, API, metadata and positivity audit.
No parent imports, source writes, or claim that finite cases prove universality.
"""
import argparse,copy,hashlib,json,random,subprocess,tempfile,types
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'complete75_asymmetric_scale_tradeoffs.py':'a87578023ae99433519555a3d1f566c853a4b6a8323ab566a72fc9108acb6660','complete75_asymmetric_scale_tradeoffs.json':'47a059a8871c101466d7d0440cf39c5dda4ddffd55fcc8d8ac118874aedbac98','complete75_normalized_strong87.py':'7dae1b0038cb15ce197e03ff5c75a68f294b811cc200b6cafb3cbf5c24867cf8','complete75_coupled_index_linear88.py':'e43dc5c65659ab8526817f674384b1faaf324671e8e24ccc82b72f3b4e8c7aed','complete75_positive_elimination.py':'70123af4f0787b38271f7c4f0fa60e4235cd2f1964ee1b0ad345fe0e3bb82749'}
SOURCE_PIN='29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f'
RECEIPT_PIN='2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e'
NOTE_PIN='9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b'
WITNESSES=['Jrep','F','alpha','zplus','f','h','i','j','o','s','w','tau_gap','eta','zeta','y_aux','Z','delta','rho','sigma']
FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong','norm_linear']
def need(x,m):
 if not x:raise ValueError(m)
def sha(x):return hashlib.sha256(x).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)is list:return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def execute(rows,values):
 e=dict(values)
 for n,op,a,b in rows:
  a=a if type(a)is int else e[a];b=b if type(b)is int else e[b]
  e[n]=a+b if op=='+' else a-b if op=='-' else a*b
 return e
def literal(old):
 r=[]
 for row in old:
  n,op,a,b=row
  if n in ['twice_tau_gap','first_signed_gap','first_cross']:continue
  if n=='norm_first':r += [['first_next','+','first_root_base','R10b'],['first_product','*','first_root_base','first_next'],['norm_first','-','tau_square','first_product']]
  elif n=='tau_square':r.append([n,op,'tau_root','tau_root'])
  else:r.append(row[:])
 return r
def inspect(rows):
 names={n for n,_,_,_ in rows};need(len(names)==len(rows),'duplicate source name')
 free={a for _,_,x,y in rows for a in (x,y) if type(a)is str and a not in names};seen=set(free)
 for n,op,a,b in rows:
  need(type(n)is str and op in ['+','-','*'] and n not in seen,'bad row')
  need(all(type(x)is int or type(x)is str and x in seen for x in [a,b]),'bad operand');seen.add(n)
 d={n:(a,b) for n,_,a,b in rows};live=set()
 def visit(x):
  if type(x)is int or x in free or x in live:return
  need(x in d,'not closed');live.add(x)
  for y in d[x]:visit(y)
 visit('polynomial');need(live==names,'dead gates')
 c=Counter(op for _,op,_,_ in rows)
 return {'operations':len(rows),'M':c['*'],'A':c['+']+c['-'],'free':sorted(free),'live_gates':len(live)}
def cuts(old,new):
 # Shared first-norm cut justified by the explicitly checked 3-atom identity;
 # every other factor and finalizer must be the identical expression DAG.
 table={}
 def intern(x):
  if x not in table:table[x]=len(table)
  return table[x]
 def run(rows):
  env={}
  for n,op,a,b in rows:
   if n=='norm_first':env[n]=intern(('proved_first_norm',));continue
   a=intern(('int',a)) if type(a)is int else env.get(a,intern(('input',a)))
   b=intern(('int',b)) if type(b)is int else env.get(b,intern(('input',b)))
   if op in ['+','*'] and b<a:a,b=b,a
   env[n]=intern((op,a,b))
  return env
 a=run(old);b=run(new)
 for n in FACTORS+['polynomial']:need(a[n]==b[n],'changed downstream '+n)
 return len(FACTORS)+1

def symbolic():
 # Sparse integer coefficients in independent atoms T,L,k; no CAS dependency.
 zero=(0,0,0)
 def add(a,b,s=1):
  c=a.copy()
  for m,x in b.items():c[m]=c.get(m,0)+s*x
  return {m:x for m,x in c.items() if x}
 def mul(a,b):
  c={}
  for m,x in a.items():
   for n,y in b.items():
    k=tuple(u+v for u,v in zip(m,n));c[k]=c.get(k,0)+x*y
  return {m:x for m,x in c.items() if x}
 T={(1,0,0):1};L={(0,1,0):1};k={(0,0,1):1};g=add(T,L,-1)
 old=add(mul(g,g),mul(L,add(add(g,g),k,-1)))
 new=add(mul(T,T),mul(L,add(L,k)),-1)
 need(old==new,'first norm coordinate polynomial identity')
 return {'independent_atoms':['T','L','k'],'expanded_coefficients':[[list(m),v] for m,v in sorted(new.items())]}

def dense(rows,values):
 def add(a,b,s=1):
  c=[0]*max(len(a),len(b))
  for i in range(len(c)):c[i]=(a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0)
  while len(c)>1 and not c[-1]:c.pop()
  return c
 def mul(a,b):
  c=[0]*(len(a)+len(b)-1)
  for i,x in enumerate(a):
   for j,y in enumerate(b):c[i+j]+=x*y
  while len(c)>1 and not c[-1]:c.pop()
  return c
 env={n:list(v) for n,v in values.items()}
 for n,op,a,b in rows:
  a=[a] if type(a)is int else env[a];b=[b] if type(b)is int else env[b]
  env[n]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
 return env

def verify(root,compiler):
 raw=compiler.read_bytes();need(sha(raw)==SOURCE_PIN,'final compiler byte pin')
 companion=compiler.with_suffix('.json');note=compiler.with_suffix('.md')
 need(sha(companion.read_bytes())==RECEIPT_PIN,'final author receipt pin');need(sha(note.read_bytes())==NOTE_PIN,'final companion note pin')
 saved=json.loads(companion.read_text());need(saved['source_sha256']==SOURCE_PIN and exact(saved['parent_pins'],PINS),'receipt provenance')
 # Execute exactly the inspected bytes, without timestamp/.pyc resolution.
 author=types.ModuleType('_independent_complete86_author');author.__file__=str(compiler)
 exec(compile(raw,str(compiler),'exec'),author.__dict__)
 for f,s in PINS.items():need(sha((root/f).read_bytes())==s,'parent source pin '+f)
 source=json.loads((root/'complete75_asymmetric_scale_tradeoffs.json').read_text())['source']
 rng=random.Random(86179);forms=[];whole=signed=rational=shared=0;degree_checks=[];rejects=copies=0
 for index,record in enumerate(source):
  old=record['source'];normal=record['normalized'];new=literal(old);li=inspect(new)
  actual_old,actual_new=author.rewrite(root,normal,copy.deepcopy(old))
  need(exact(actual_old,old) and exact(actual_new,new),'complete independent literal source emission')
  receipt=saved['forms'][index];need(type(receipt['normalized'])is bool and receipt['normalized']is normal,'receipt mode')
  need(exact(receipt['source'],new),'receipt actual complete source')
  witness=['tau_root' if n=='tau_gap' else n for n in WITNESSES]
  need(exact(receipt['witnesses'],witness) and receipt['output']=='polynomial','current witness metadata')
  need(li['operations']==(86 if normal else 87) and li['M']==(48 if normal else 47) and li['A']==(38 if normal else 40),'paid counts')
  need(set(inspect(old)['free'])-{'tau_gap'}==set(li['free'])-{'tau_root'},'changed interface')
  expected_degrees=[22,18,32,56 if normal else 24,7,3,34 if normal else 22,7]
  ledger={'operations':li['operations'],'M':li['M'],'A':li['A'],'certificate_operations':li['operations']-1,'comparisons':1,'positive_witnesses':19,'all_gates_live':True,'fixed_numerals':['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF'],'ordinary_input':'x','exact_degree':sum(expected_degrees),'factor_degrees':expected_degrees}
  need(exact(receipt['ledger'],ledger),'current full ledger metadata')
  parent_inspect=inspect(old);base=copy.deepcopy(ledger);base.update(operations=parent_inspect['operations'],M=parent_inspect['M'],A=parent_inspect['A'],certificate_operations=parent_inspect['operations']-1);base.pop('exact_degree');base.pop('factor_degrees')
  need(exact(receipt['baseline'],base),'fair parent baseline metadata')
  need([n for n,_,a,b in old if 'tau_gap' in [a,b]]==['tau_square','twice_tau_gap'],'hidden old coordinate consumer')
  need([n for n,_,a,b in new if 'tau_root' in [a,b]]==['tau_square'],'hidden new coordinate consumer')
  need(not any('tau_gap' in r for r in new),'stale gap coordinate in current source')
  cuts(old,new)
  for case in range(128):
   v={n:rng.randrange(-5,6) if case%2 else rng.randrange(1,6) for n in WITNESSES+['x']}
   if case>=112:v={n:Fraction(x,3) for n,x in v.items()};rational+=2
   B=(16,32,64,128)[case%4];v.update(Bm1=B-1,Kconstant=3+B*5,twice_cell_bits=2*(B.bit_length()-1),inner_bits=3,MC=B-2,MF=4+B-1)
   a=execute(old,v);vp={n:x for n,x in v.items() if n!='tau_gap'};vp['tau_root']=v['tau_gap']+a['first_root_base'];b=execute(new,vp)
   need(a['polynomial']==b['polynomial'],'forward whole identity')
   need(author.evaluate(actual_new,vp)['polynomial']==b['polynomial'],'author low-level interpreter agrees')
   for n in (set(a)&set(b))-{'tau_square'}:need(a[n]==b[n],'forward shared register '+n);shared+=1
   child={('tau_root' if n=='tau_gap' else n):x for n,x in v.items()};b=execute(new,child);vm={n:x for n,x in child.items() if n!='tau_root'};vm['tau_gap']=child['tau_root']-b['first_root_base'];a=execute(old,vm)
   need(a['polynomial']==b['polynomial'],'inverse whole identity')
   for n in (set(a)&set(b))-{'tau_square'}:need(a[n]==b[n],'inverse shared register '+n);shared+=1
   need(vm['tau_gap']+a['first_root_base']==child['tau_root'],'coordinate round trip')
   whole+=2;signed+=2*(case%2)
  for fixedbase in [16,32]:
   slopes={n:(i%5)+1 for i,n in enumerate(witness+['x'])};q0=(fixedbase-1)*slopes['Jrep'];k=slopes['eta']+slopes['zeta'];gamma=slopes['rho']+slopes['sigma'];d=fixedbase.bit_length()-1
   ct=q0-slopes['F']-slopes['Z']-slopes['alpha']-2*d*slopes['x'];need(ct!=0,'bad certificate direction')
   params={'Bm1':fixedbase-1,'Kconstant':3+fixedbase*5,'twice_cell_bits':2*d,'inner_bits':3,'MC':fixedbase-2,'MF':4+fixedbase-1}
   env={n:[0,s] for n,s in slopes.items()};env.update({n:[v] for n,v in params.items()});p=dense(new,env)
   need([len(p[n])-1 for n in FACTORS]==expected_degrees,'full factor degrees')
   coeff=(-32*q0**108*slopes['h']**2*gamma*slopes['delta']**2*slopes['i']**4*k**13*slopes['w']**18*slopes['s']**30*ct if normal else 32*q0**80*slopes['h']**2*gamma*slopes['delta']**2*slopes['i']**2*slopes['f']**2*k**9*slopes['w']**14*slopes['s']**22*ct)
   need(len(p['polynomial'])-1==sum(expected_degrees) and p['polynomial'][-1]==coeff,'exact full leading coefficient')
   degree_checks.append({'normalized':normal,'fixed_B':fixedbase,'factor_degrees':expected_degrees,'complete_degree':sum(expected_degrees),'leading_coefficient_sha256':sha(str(coeff).encode()),'all_coefficients_evaluated':True})
  bads=[[],old[:-1],old+[old[-1]],tuple(old),new,source[1-index]['source']]
  for j,row in enumerate(old):
   x=copy.deepcopy(old);x[j][1]='+' if row[1]!='+' else '-';bads.append(x)
   x=copy.deepcopy(old);x[j]=tuple(x[j]);bads.append(x)
   x=copy.deepcopy(old);x[j][0]+='_renamed';bads.append(x)
   for pos in [2,3]:
    if type(row[pos])is int:
     for value in [float(row[pos]),bool(row[pos])]:
      x=copy.deepcopy(old);x[j][pos]=value;bads.append(x)
  # Full polynomial no-op mutation: append a +0 and make it the named output.
  x=copy.deepcopy(old);x[-1][0]='old_output';x.append(['polynomial','+','old_output',0]);bads.append(x)
  # Another algebraic no-op source change: commute one multiplication.
  x=copy.deepcopy(old);j=next(i for i,r in enumerate(x) if r[1]=='*' and r[2]!=r[3]);x[j][2],x[j][3]=x[j][3],x[j][2];bads.append(x)
  for bad in bads:
   try:author.rewrite(root,normal,bad)
   except ValueError:rejects+=1
   else:raise ValueError('noncanonical parent accepted')
  # Every returned source and parent record is independent of future builds.
  first_old,first_new=author.rewrite(root,normal);first_old[0][0]='poison';first_new[0][0]='poison'
  second_old,second_new=author.rewrite(root,normal);need(exact(second_old,old) and exact(second_new,new),'rewrite return isolation');copies+=2
  records=author.parents(root);records[index]['source'][0][0]='poison';need(exact(author.parents(root)[index]['source'],old),'parent record isolation');copies+=1
  # Check the recorded off-zero inverse boundary against our own executor.
  boundary=receipt['positive_offzero_inverse_counterexample'];ev=execute(new,boundary['assignment'])
  need(ev['polynomial']==boundary['complete_output']!=0 and boundary['assignment']['tau_root']-ev['first_root_base']==boundary['restored_gap']<0,'false whole-orthant claim/boundary')
  forms.append({'normalized':normal,'ledger':ledger,'source':new,'full_factor_cut_identities':9,'witnesses':witness,'strict_parent_rejections':len(bads),'scope':'Full positive-zero coordinate bijection; all-integer coordinate graph identity. Exact same named tuple polynomial equality is not claimed.'})
 for bad in [0,1,0.0,1.0,None,[],{},'normalized']:
  try:author.rewrite(root,bad)
  except ValueError:rejects+=1
  else:raise ValueError('inexact Boolean mode accepted')
 # No cache may conceal a changed parent file on a repeated call.
 with tempfile.TemporaryDirectory(prefix='review86-parent-') as td:
  private=Path(td)
  for f in PINS:(private/f).write_bytes((root/f).read_bytes())
  author.rewrite(private,True)
  warm=0
  for name in ['complete75_asymmetric_scale_tradeoffs.py','complete75_asymmetric_scale_tradeoffs.json']:
   p=private/name;oldbytes=p.read_bytes();p.write_bytes(oldbytes+b'\n')
   try:author.rewrite(private,True)
   except ValueError:warm+=1
   else:raise ValueError('warm parent mutation accepted')
   p.write_bytes(oldbytes)
  author.rewrite(private,False)
 # Reproduce author receipt after reading all source, then compare exact types.
 need(exact(author.verify(root),saved),'full author saved receipt replay')
 need(whole==512 and rational==64,'case accounting')
 return {'status':'PASS_FINAL_COMPLETE86_SOURCE','self_sha256':sha(Path(__file__).read_bytes()),'compiler_sha256':SOURCE_PIN,'author_receipt_sha256':RECEIPT_PIN,'companion_note_sha256':NOTE_PIN,'parent_pins':PINS,'symbolic_identity':symbolic(),'forms':forms,'complete_coordinate_identities':whole,'signed_cases':signed,'rational_cases_included':rational,'shared_register_comparisons':shared,'exact_dense_degree_certificates':degree_checks,'strict_parent_and_mode_rejections':rejects,'returned_source_isolation_checks':copies,'warm_parent_pin_rejections':warm,'fresh_author_receipt_replay':True,'positive_zero_proof':'Integer factors are +/-1. Positive L and k>=2 imply T²-L²=Lk+epsilon>=1, so positive T restores positive g=T-L. Forward T=L+g is positive; other coordinates fixed. No first-factor sign theorem is needed before restoration.','limits':'Finite fixtures do not materialize a full universal Pell zero. Rewrite validates a complete selected canonical parent; evaluate is a low-level arithmetic interpreter rather than a separately guarded natural-domain public compiler API.'}

def main():
 a=argparse.ArgumentParser();a.add_argument('--root',type=Path,required=True);a.add_argument('--compiler',type=Path);a.add_argument('--output',type=Path);a.add_argument('--expect',type=Path);v=a.parse_args();compiler=v.compiler or v.root/'complete86_factored_first_root.py';r=verify(v.root,compiler)
 if v.expect:need(exact(r,json.loads(v.expect.read_text())),'saved receipt mismatch')
 if v.output:v.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(r['status'],r['complete_coordinate_identities'],r['strict_parent_and_mode_rejections'],r['returned_source_isolation_checks'],r['warm_parent_pin_rejections'])
if __name__=='__main__':main()
