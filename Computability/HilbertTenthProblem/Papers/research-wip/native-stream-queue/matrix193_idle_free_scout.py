#!/usr/bin/env python3
"""Fresh IDLE specialization; frozen predecessors are inert bytes/JSON only."""
import argparse,copy,hashlib,json,random
from collections import Counter
from pathlib import Path
PINS = {'matrix193_entry_flow_scout.py': '0a34977902f9ada25c5007c2576d0aa2a1761bf4e8cd4d5bcad49344388a43bf', 'matrix193_entry_flow_scout.json': '321a8c77b63a62d131dc52073d85f27a1f1f5086a2e19e0e42dca2df398e88da', 'matrix193_entry_flow_scout.md': '5a6c5330e2d29a6149965ed671bedd1838c0114deb240d1e55992960ce3d32f2', 'matrix193_entry_controller_charts.py': '7c1e55ca1396958f234c2caf6c117702c4d69537cefcad51089498cb1e58f2bf', 'matrix193_entry_controller_charts.json': 'd5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571', 'matrix193_entry_controller_charts.md': '27245d944d03b1d31ad79470dfd5625798834b7a47c1a03dee319f198214d122', 'matrix193_atomic_context_packing.py': '18ed65a37a471a17b31245b237b7e3b987c4cef58fcbd3c9dfb4b6d0c67daa32', 'matrix193_atomic_context_packing.json': '7f9f9614f3862d08fa2645a5944a4567f4f268e4e93a57c5dec6e59d5a9fe8c9', 'matrix193_atomic_context_packing.md': 'b19f3a7188eac22055323ecc277522e18d68f0818c6f5d2da3a05ceea94262ca', 'matrix193_positive_controller_charts.md': 'e7fda47c1c60c168d65307edb78b77709b0b24c10827ace85d2e6b82e752f53c', 'matrix193_bounded_high_output.md': '7f5a5bab9bff8518881a16a7c9d32916ce4ca1ff9dcbaa18f7fab7d452da654c', 'matrix193_balanced_output_scout.md': 'cfc892b2c7a577d2348c3583d968e04ab271f065003cc0bfa6316a9f05f3abde'}
def ck(ok,msg):
 if not ok:raise ValueError(msg)
def sha(x):return hashlib.sha256(x).hexdigest()
def enc(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def read(p):
 def pairs(xs):
  d={}
  for k,v in xs:ck(k not in d,'duplicate key');d[k]=v
  return d
 def bad(x):raise ValueError('nonfinite JSON')
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_constant=bad)
def equal(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(equal(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(equal(x,y) for x,y in zip(a,b))
 return a==b

def atom(n):return {((n,1),):1}
def constant(n):return {():n} if n else {}
def add(a,b,sign=1):
 out=dict(a)
 for m,c in b.items():out[m]=out.get(m,0)+sign*c
 return {m:c for m,c in out.items() if c}
def mul(a,b):
 out={}
 for m,c in a.items():
  for n,d in b.items():
   e=dict(m)
   for v,k in n:e[v]=e.get(v,0)+k
   t=tuple(sorted(e.items()));out[t]=out.get(t,0)+c*d
 return {m:c for m,c in out.items() if c}
def expand(rows,target,cuts):
 by={r[0]:r for r in rows};env=dict(cuts)
 def get(v):
  if type(v)is int:return constant(v)
  if v not in env:
   _,o,a,b=by[v];a=get(a);b=get(b);env[v]=mul(a,b) if o=='*' else add(a,b,1 if o=='+' else -1)
  return env[v]
 return get(target)
def describe(poly):return [[list(map(list,m)),c] for m,c in sorted(poly.items())]
def labels(p):return (lambda v:p['map'].get(v,v)) if 'chart' in p else (lambda v:v)
def graph(p):
 known=set(p['free']);ck(len(known)==len(p['free']),'unique ports');deps={};counts=Counter()
 for n,o,a,b in p['source']:
  ck(n not in known and o in ['+','-','*'] and all(type(v)is int or v in known for v in [a,b]),'closed ordered source')
  known.add(n);deps[n]=(a,b);counts[o]+=1
 live=set();todo=[p['output']]
 while todo:
  v=todo.pop()
  if type(v)is str and v not in live:live.add(v);todo.extend(deps.get(v,()))
 ck(live==known,'all rows and supplied ports live')
 return {'total':len(p['source']),'M':counts['*'],'A':counts['+']+counts['-'],'positive_witnesses':len(p['witnesses']),'all_live':True,'integer_literals':len({v for row in p['source'] for v in row[2:] if type(v)is int})}

def transform(parent):
 w=labels(parent);by={r[0]:r for r in parent['source']};idle='edge_hat98';Q=w('r108');J=w('r105');ctrl=w('r774')
 ck(idle in parent['witnesses'],'positive IDLE hat')
 patterns=[['r104','+','r103',idle],['r105','-','r104',99],['r568','*',idle,'r108'],['r569','+','r568','edge_hat97'],['r570','*','r569','r108'],['r773','+','r772','r187'],['r774','-','r763','r773']]
 for n,o,a,b in patterns:ck(by[w(n)]==[w(n),o,w(a) if type(a)is str else a,w(b) if type(b)is str else b],'literal IDLE interface '+n)
 gone={w(n) for n in ['r104','r568','r569','r773']}
 edits={J:[J,'-',w('r103'),98],w('r570'):[w('r570'),'*','edge_hat97',Q],ctrl:[ctrl,'-',w('r763'),w('r772')]}
 rows=[edits.get(r[0],r[:]) for r in parent['source'] if r[0] not in gone]
 p={k:copy.deepcopy(parent[k]) for k in ['free','witnesses','fixed_numerals','fixture_fixed_bindings','output']}
 p['free'].remove(idle);p['witnesses'].remove(idle);p['source']=rows;p['variant']=parent.get('chart','no_controller_chart');p['ledger']=graph(p)
 old=graph(parent);ck((p['ledger']['total'],p['ledger']['M'],p['ledger']['A'])==(old['total']-4,old['M']-1,old['A']-3),'actual four-gate saving')
 # Every altered Horner intermediate has no consumer outside its cone except
 # the one proved controller word. The other removed nodes have no consumers.
 horner={w('r'+str(i)) for i in range(568,764)}
 for r in parent['source']:
  if r[0] not in horner and r[0]!=ctrl:ck(not any(v in horner for v in r[2:]),'private Horner cone')
 for r in rows:ck(not any(v in gone or v==idle for v in r[2:]),'no dangling erased value')
 hats=[w('edge_hat'+str(i)) for i in range(99)];cuts={hat:(constant(1) if i==98 else atom('h'+str(i))) for i,hat in enumerate(hats)}
 wanted={}
 for i in range(98):wanted=add(wanted,atom('h'+str(i)))
 wanted=add(wanted,constant(-98))
 ck(expand(parent['source'],J,cuts)==expand(rows,J,cuts)==wanted,'exact J specialization')
 cuts[Q]=atom('Q');wanted={}
 for i in range(98):
  power=constant(1) if i==0 else { (('Q',i),):1 }
  wanted=add(wanted,mul(add(atom('h'+str(i)),constant(-1)),power))
 oldpoly=expand(parent['source'],ctrl,cuts);newpoly=expand(rows,ctrl,cuts)
 ck(oldpoly==newpoly==wanted,'complete 98-slot controller polynomial')
 ck(expand(rows,w('r772'),{Q:atom('Q')})=={():1,**{(('Q',i),):1 for i in range(1,98)}},'paid repunit R98')
 p['edit']={'removed_rows':[r for r in parent['source'] if r[0] in gone],'modified_rows':list(edits.values()),'private_horner_rows':sorted(horner),'J_wire':J,'controller_word_wire':ctrl,'Q_wire':Q,'remaining_hat_values':hats[:98],'controller_polynomial_terms':len(wanted),'controller_polynomial_sha256':sha(enc(describe(wanted))),'parent_label_map':{n:w(n) for n in ['r105','r108','r774','selection__wn2','selection__R12','selection__R10a','selection__ga','selection__a4m5','selection__R15']}}
 return p

def whole_identity(parent,p,native_names,residual_names):
 cache={}
 def intern(k):
  if k not in cache:cache[k]=len(cache)
  return cache[k]
 def run(q,old):
  env={n:intern(('free',n)) for n in q['free']};val=lambda v:intern(('int',v)) if type(v)is int else env[v]
  if old:env['edge_hat98']=intern(('int',1))
  for n,o,a,b in q['source']:
   if n==p['edit']['J_wire']:env[n]=intern(('proved_J_sum',tuple(val(v) for v in p['edit']['remaining_hat_values'])))
   elif n==p['edit']['controller_word_wire']:env[n]=intern(('proved_controller_word',val(p['edit']['Q_wire']),tuple(val(v) for v in p['edit']['remaining_hat_values'])))
   else:env[n]=intern((o,val(a),val(b)))
  return env
 a,b=run(parent,True),run(p,False);exempt=set(p['edit']['private_horner_rows']);checked=0
 for n in a.keys()&b.keys():
  if n not in exempt:ck(a[n]==b[n],'all other supplied/paid expressions '+n);checked+=1
 ck(a[parent['output']]==b[p['output']],'entire IDLE pullback')
 w=labels(parent);native=['r107','r829','r823','r825','r827','r817']
 for n in native:ck(a[w(n)]==b[w(n)],'native input retained')
 for n in native_names+residual_names:
  v=w(n)
  if type(v)is str:ck(v in a and v in b and a[v]==b[v],'complete native/residual position '+n)
 newby={r[0]:r for r in p['source']}
 for row in parent['source']:
  if row[0] in b and row[0] not in exempt and row[0] not in [p['edit']['J_wire'],p['edit']['controller_word_wire']]:
   ck(row==newby[row[0]],'every other retained row literal')
 return {'all_ring_identity':'F_child=F_parent at edge_hat98=1','unchanged_nonhorner_expressions':checked,'native_inputs':6,'native_rows':len(native_names),'original_residual_positions':len(residual_names),'all_other_retained_rows_literal':True,'positive_forward_map':'insert the positive integer 1','reverse_scope':'ordinary-input projection by a fresh IDLE-free accepting history; not all common coordinates'}

def pure_q(p,Q):
 env={Q:{1:1}}
 for n,o,a,b in p['source']:
  if n==Q or any(type(v)is str and v not in env for v in [a,b]):continue
  aa={0:a} if type(a)is int else env[a];bb={0:b} if type(b)is int else env[b];out={}
  if o=='*':
   for i,x in aa.items():
    for j,y in bb.items():out[i+j]=out.get(i+j,0)+x*y
  else:
   out=dict(aa)
   for j,y in bb.items():out[j]=out.get(j,0)+(y if o=='+' else -y)
  env[n]={i:x for i,x in out.items() if x}
 return env

def degree(parent,p,s,seed):
 w=labels(parent);Q=w('r108');polys=pure_q(p,Q);mod=1000000007;env={}
 for i,n in enumerate(p['free']):
  fixed=n in p['fixed_numerals'];c=p['fixture_fixed_bindings'][n]%mod if fixed else ((i+3)**2+19*seed+5)%mod;env[n]=(0 if fixed else 1,c) if c else (-1,0)
 cuts={w(n):atom(v) for n,v in [('selection__wn2','X'),('selection__R12','a'),('selection__R10a','c'),('selection__ga','g'),('selection__a4m5','H')]}
 main=expand(p['source'],w('selection__R15'),cuts);X,a,c,g,H=[atom(n) for n in ['X','a','c','g','H']]
 y=add(add(X,mul(a,c)),mul(g,H));expected=add(mul(y,y),mul(add(mul(a,a),H),mul(c,c)),-1)
 ck(main==expected and len(main)==6,'full literal six-term main norm')
 aliases={'X':w('selection__wn2'),'a':w('selection__R12'),'c':w('selection__R10a'),'g':w('selection__ga'),'H':w('selection__a4m5')}
 def get(v):return env[v] if type(v)is str else ((0,v%mod) if v%mod else (-1,0))
 for n,o,a,b in p['source']:
  da,ca=get(a);db,cb=get(b)
  if o=='*':v=(-1,0) if min(da,db)<0 else (da+db,ca*cb%mod)
  else:
   d=max(da,db);v=(d,((ca if da==d else 0)+(cb if db==d else 0)*(1 if o=='+' else -1))%mod)
  if n in polys and n!=Q:
   pol=polys[n]
   if not pol:v=(-1,0)
   else:k=max(pol);dq,cq=env[Q];v=(k*dq,pol[k]*pow(cq,k,mod)%mod)
  if n==w('selection__R15'):
   terms=[]
   for mon,coeff in main.items():
    d=0;lc=coeff%mod
    for name,e in mon:
     nd,nc=get(aliases[name]);d+=nd*e;lc=lc*pow(nc,e,mod)%mod
    terms.append((d,lc,mon))
   top=max(d for d,c,m in terms);leaders=[t for t in terms if t[0]==top]
   ck(len(leaders)==1 and dict(leaders[0][2])=={'a':1,'c':1,'g':1,'H':1},'unique main leader');v=leaders[0][:2]
  if v==(0,0):v=(-1,0)
  ck(v[0]<0 or v[1]!=0,'unexplained leader cancellation '+n);env[n]=v
 d=472*s+1;factors=['first_unit','selection__R15','selection__P17','index_unit','linear_unit','strong_unit','joint_bound_unit'];degrees=[5*d-s+4,9*d-2*s+5,6*d+14,4*d-s+2,4*d-s+2,8*d-2*s+4,s]
 for n,target in zip(factors,degrees):ck(get(w(n))[0]==target,'native degree '+n)
 ck(get(Q)[0]==s and get(w('r817'))[0]==d,'packing scale degree');ck(get(p['output'])[0]==17760*s+67,'complete exact degree')
 return {'s':s,'native_factor_degrees':degrees,'native_degree':sum(degrees),'exact_full_degree':17760*s+67,'line_seed':seed,'modulus':mod,'full_leading_coefficient':get(p['output'])[1],'main_norm_terms':describe(main),'degree_proof':'uniform leaders in companion; finite nonzero leaders corroborate it'}

def evaluate(p,values,mod):
 env=dict(values)
 for n,o,a,b in p['source']:
  a=env[a] if type(a)is str else a;b=env[b] if type(b)is str else b;env[n]=(a*b if o=='*' else a+b if o=='+' else a-b)%mod
 return env

def build(root):
 for name,h in PINS.items():ck(sha((root/name).read_bytes())==h,'pin '+name)
 base=read(root/'matrix193_entry_flow_scout.json');charts=read(root/'matrix193_entry_controller_charts.json');atomic_receipt=read(root/'matrix193_atomic_context_packing.json');atomic=atomic_receipt['packets'][-1]
 for name,receipt in [('matrix193_entry_flow_scout',base),('matrix193_entry_controller_charts',charts),('matrix193_atomic_context_packing',atomic_receipt)]:ck(receipt['source_sha256']==PINS[name+'.py'],'parent source pin')
 ck(atomic['controller_edges'][-1]==[98,1,1,'IDLE'] and atomic['controller_edges'][1]==[1,0,1,'SWITCH'],'actual optional IDLE and compulsory switch')
 ck(all(98 not in g['edges'] for g in atomic['groups']),'IDLE activates no selection lane')
 parents=[base['packet'],*charts['packets']];packets=[]
 bp=base['packet'];start=bp['stage_counts']['packing'];native_names=[r[0] for r in bp['source'][start:start+63]];residual_names=[bp['source'][-62+2*i][0] for i in range(20)]
 for i,parent in enumerate(parents):
  p=transform(parent);p['full_identity']=whole_identity(parent,p,native_names,residual_names);s=[2,3,3,4][i];p['degree_checks']=[degree(parent,p,s,seed) for seed in [1,2]];p['ledger']['exact_degree']=17760*s+67
  records=[];rng=random.Random(1612+i)
  for mod in [1000000007,1000000009]:
   for j in range(4):
    values={n:rng.randrange(-23,24) for n in p['free']}
    if j%2==0:values.update(p['fixture_fixed_bindings'])
    child=evaluate(p,values,mod);old=evaluate(parent,{**values,'edge_hat98':1},mod)
    ck(child[p['output']]==old[parent['output']],'supplemental complete pullback')
    for n in old.keys()&child.keys():
     if n not in set(p['edit']['private_horner_rows']):ck(old[n]==child[n],'supplemental full nonhorner registers')
    records.append({'prime':mod,'case':j,'output':child[p['output']]})
  p['modular_checks']=records;packets.append(p)
 ck([p['ledger']['total'] for p in packets]==[1618,1615,1615,1612],'four literal full counts')
 return {'schema':'matrix193-idle-free-v1','pins':PINS,'source_sha256':sha(Path(__file__).read_bytes()),'packets':packets,'scope':{'predecessor_code_executed':False,'IDLE_hat_fixed_to':1,'input_projection_preserved':True,'common_witness_projection_equivalence_claimed':False,'new_giant_history_or_native_Pell_tuple':False,'new_diagnostic':False,'universal84_unchanged':True}}
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--write',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();r=build(a.root)
 if a.write:a.write.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:ck(equal(r,read(a.expect)),'type-exact receipt')
 print('PASS: four complete IDLE-free polynomials;1618/1615/1615/1612;full pullbacks;uniform degrees unchanged')
