#!/usr/bin/env python3
"""Fresh positive controller charts of the pinned composed matrix source.
Initial recursive transformer adapted from the new root controller-chart probe.
All frozen predecessor files are inert JSON/text, never imported or executed.
"""
import argparse,copy,hashlib,json,random
from collections import Counter
from pathlib import Path
PINS={'matrix193_composed_output_scout.py':'e8b2982bdf00a9be6e6e80a1b86c38f3536a5345c60adf3103e8f7356ed01317','matrix193_composed_output_scout.json':'a231b3ef66f0ab0f729bf50e40f87fad5a5d784e089249dbb4e93e11696a9e37','matrix193_composed_output_scout.md':'83711eab17b18f38c2bd47ddd3d803fde5adf339f7b5bbc0be2839a3bfeff748'}
def ck(v,m):
 if not v:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def parse(p):
 def obj(xs):
  d={}
  for k,v in xs:ck(k not in d,'duplicate JSON key');d[k]=v
  return d
 return json.loads(p.read_text(),object_pairs_hook=obj)
def exact(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def controller_pattern(p):
 by={r[0]:r for r in p['source']};EL,ES=p['ports']['raw_edges'];B=p['ports']['B'];J=p['ports']['J'];P=p['ports']['P'];e0,e1=p['ports']['edge_hats'][:2]
 ck(by[EL]==[EL,'-',e0,1] and by[ES]==[ES,'-',e1,1],'literal raw edges')
 pp=by[P];ck(pp[1]=='+' and pp[3]==1,'P plus one');product=by[pp[2]];ck(product[1]=='*' and product[3]==J,'P product');bm=product[2];ck(by[bm]==[bm,'-',B,1],'literal B minus one')
 left,right=p['comparisons'][18];lr=by[left];rr=by[right];ck(lr[1]=='+' and lr[3]==P and rr[1]=='*' and rr[2]==B,'flow outer')
 src=lr[2];dst=rr[3];ck(by[src]==[src,'-',dst,ES] and by[dst]==[dst,'-',J,EL],'flow source')
 left,right=p['comparisons'][19];ck(by[left]==[left,'*',bm,'population_quotient'],'population left');row=by[right];ck(row[1:] and row[1]=='-' and row[3]=='x','population subtraction');ck(by[row[2]]==[row[2],'+',EL,bm],'population right')
 tail=p['source'][-62:];res=[]
 for i,(a,b) in enumerate(p['comparisons']):ck(tail[2*i][1:]==['-',a,b] and tail[2*i+1][1:]==['*',tail[2*i][0],tail[2*i][0]],'literal squared residual');res.append(tail[2*i][0])
 return {'bm':bm,'EL':EL,'ES':ES,'edge0':e0,'edge1':e1,'J':J,'dst':dst,'src':src,'residuals':res}

# Small exact multivariate ring, with sorted exponent tuples.
def atom(n):return {((n,1),):1}
def con(n):return {():n} if n else {}
def add(a,b,sign=1):
 d=dict(a)
 for k,v in b.items():
  d[k]=d.get(k,0)+sign*v
  if not d[k]:del d[k]
 return d
def mul(a,b):
 d={}
 for x,u in a.items():
  for y,v in b.items():
   z=dict(x)
   for k,e in y:z[k]=z.get(k,0)+e
   z=tuple(sorted(z.items()));d[z]=d.get(z,0)+u*v
 return {k:v for k,v in d.items() if v}
def control_ring(pop,flow):
 b=atom('bm');j=atom('J');x=atom('x');u=atom('population_quotient');EL=add(x,mul(b,add(u,con(1),-1))) if pop else atom('EL');ES=add(con(1),mul(b,EL)) if flow else atom('ES')
 P=add(mul(b,j),con(1));fr=add(add(add(j,EL,-1),ES,-1),P);fr=add(fr,mul(add(b,con(1)),add(j,EL,-1)),-1)
 pr=add(mul(b,u),add(add(EL,b),x,-1),-1)
 ck(fr==add(add(con(1),mul(b,EL)),ES,-1),'flow exact reduced identity');ck(pr==add(add(mul(b,add(u,con(1),-1)),x),EL,-1),'population exact reduced identity')
 if flow:ck(not fr,'zero substituted flow residual')
 if pop:ck(not pr,'zero substituted population residual')
 return {'flow_residual_identically_zero':flow,'population_residual_identically_zero':pop,'ring':'Z[bm,J,x,population_quotient,remaining raw edges]'}

def transform(p,pop,flow):
 contract=controller_pattern(p);by={r[0]:r for r in p['source']};EL=contract['EL'];ES=contract['ES'];bm=contract['bm'];e0=contract['edge0'];e1=contract['edge1'];rows=[];cache={};memo={};free=[v for v in p['free'] if not ((pop and v==e0) or (flow and v==e1))]
 jm={n:atom(n) for n in p['ports']['edge_hats']}
 def jget(v):
  if type(v)is int:return con(v)
  if v not in jm:
   _,o,a,b=by[v];aa=jget(a);bb=jget(b);jm[v]=mul(aa,bb) if o=='*' else add(aa,bb,1 if o=='+' else -1)
  return jm[v]
 jexpected=con(-p['n'])
 for edge in p['ports']['edge_hats']:jexpected=add(jexpected,atom(edge))
 ck(jget(contract['J'])==jexpected,'literal total hat sum')
 zeros={contract['residuals'][18]} if flow else set()
 if pop:zeros.add(contract['residuals'][19])
 def op(o,a,b):
  if type(a)is int and type(b)is int:return a*b if o=='*' else a+b if o=='+' else a-b
  if o=='*' and (a==0 or b==0):return 0
  if o=='*' and a==1:return b
  if o=='*' and b==1:return a
  if o in ['+','-'] and b==0:return a
  if o=='+' and a==0:return b
  if o=='-' and a==b:return 0
  key=(o,a,b)
  if key not in cache:
   n='chart'+str(len(rows));rows.append([n,o,a,b]);cache[key]=n
  return cache[key]
 def get(n):
  if type(n)is int:return n
  if n in memo:return memo[n]
  if n in zeros:r=0
  elif pop and n==EL:r=op('+',op('*',get(bm),op('-',get('population_quotient'),1)),get('x'))
  elif pop and n==e0:r=op('+',get(EL),1)
  elif flow and n==ES:r=op('+',op('*',get(bm),get(EL)),1)
  elif flow and n==e1:r=op('+',get(ES),1)
  elif n in free:r=n
  else:
   _,o,a,b=by[n];r=op(o,get(a),get(b))
  memo[n]=r;return r
 output=get(p['output']);known=set(free);deps={}
 for n,o,a,b in rows:ck(n not in known and all(type(v)is int or v in known for v in [a,b]),'topology');known.add(n);deps[n]=(a,b)
 live=set();todo=[output]
 while todo:
  v=todo.pop()
  if type(v)is str and v not in live:live.add(v);todo.extend(deps.get(v,()))
 ck(known==live,'all rows and free ports live')
 ct=Counter(r[1] for r in rows);s=4 if pop and flow else 3;N=p['L']+p['m']+4;lm=max(r['length'] for r in p['extraction'])
 return {'name':p['name'],'chart':'both' if pop and flow else 'population' if pop else 'flow','free':free,'source':rows,'output':output,'map':memo,'witnesses':[v for v in p['witnesses'] if v in free],'fixed_numerals':p['fixed_numerals'],'fixture_fixed_bindings':p['fixture_fixed_bindings'],'population_chart':pop,'flow_chart':flow,'parent_contract':contract,'removed_residuals':sorted(zeros),'control_identity':control_ring(pop,flow),'degree_parameters':{'s':s,'N':N,'d':N*s+1,'longest_block':lm},'ledger':{'total':len(rows),'M':ct['*'],'A':ct['+']+ct['-'],'positive_witnesses':len(p['witnesses'])-int(pop)-int(flow),'residuals':20-int(pop)-int(flow),'all_live':True,'proved_exact_degree':(36*N+4*lm-8)*s+67}}

def pullback_identity(parent,p):
 # The small coefficient proof above certifies zero residuals and the two
 # raw-edge simplifications; all other nodes are checked by a fresh interner.
 ck(p['control_identity']==control_ring(p['population_chart'],p['flow_chart']),'control proof retained')
 cache={};nextid=[0]
 def getid(key):
  if key not in cache:cache[key]=nextid[0];nextid[0]+=1
  return cache[key]
 def literal(v):return ('int',v)
 def operation(o,a,b):
  if a[0]=='int' and b[0]=='int':return literal(a[1]*b[1] if o=='*' else a[1]+b[1] if o=='+' else a[1]-b[1])
  if o=='*' and (a==literal(0) or b==literal(0)):return literal(0)
  if o=='*' and a==literal(1):return b
  if o=='*' and b==literal(1):return a
  if o in ['+','-'] and b==literal(0):return a
  if o=='+' and a==literal(0):return b
  if o=='-' and a==b:return literal(0)
  return ('node',getid((o,a,b)))
 common={n:('free',n) for n in p['free']};new=dict(common)
 for n,o,a,b in p['source']:new[n]=operation(o,new[a] if type(a)is str else literal(a),new[b] if type(b)is str else literal(b))
 value=lambda v:new[v] if type(v)is str else literal(v)
 old=dict(common);special={};contract=p['parent_contract']
 for flag,hat,raw in [(p['population_chart'],contract['edge0'],contract['EL']),(p['flow_chart'],contract['edge1'],contract['ES'])]:
  if flag:
   old[hat]=value(p['map'][hat]);special[raw]=value(p['map'][raw]);ck(old[hat]==operation('+',special[raw],literal(1)),'positive hat=raw+1 identity')
 for n in p['removed_residuals']:special[n]=literal(0)
 checked=0
 for n,o,a,b in parent['source']:
  old[n]=special[n] if n in special else operation(o,old[a] if type(a)is str else literal(a),old[b] if type(b)is str else literal(b))
  if n in p['map']:ck(old[n]==value(p['map'][n]),'full mapped register '+n);checked+=1
 ck(old[parent['output']]==new[p['output']],'entire pullback output')
 return {'whole_polynomial_pullback':True,'mapped_parent_registers':checked,'certified_zero_residuals':len(p['removed_residuals']),'all_other_parent_rows_checked':True}

def main_norm_identity(parent):
 rows={r[0]:r for r in parent['source']};cuts={'selection__wn2':'X','selection__R12':'a','selection__R10a':'c','selection__ga':'g','selection__a4m5':'H'};memo={n:atom(v) for n,v in cuts.items()}
 def get(v):
  if type(v)is int:return con(v)
  if v not in memo:
   _,op,a,b=rows[v];aa=get(a);bb=get(b);memo[v]=mul(aa,bb) if op=='*' else add(aa,bb,1 if op=='+' else -1)
  return memo[v]
 X,a,c,g,H=[atom(v) for v in ['X','a','c','g','H']]
 terms=[mul(X,X),mul(con(2),mul(X,mul(a,c))),mul(con(2),mul(X,mul(g,H))),mul(con(2),mul(mul(a,c),mul(g,H))),mul(mul(g,g),mul(H,H)),mul(con(-1),mul(H,mul(c,c)))]
 want={}
 for t in terms:want=add(want,t)
 ck(get('selection__R15')==want,'actual main norm full cancellation')
 return {'terms':[[[[v,e] for v,e in mon],coef] for mon,coef in sorted(want.items())],'unique_maximal_term':'2*a*c*g*H'}

def q_polynomials(parent):
 Q=parent['ports']['Q'];env={Q:{1:1}}
 for n,o,a,b in parent['source']:
  if n==Q:continue
  if all(type(t)is int or t in env for t in [a,b]):
   aa={0:a} if type(a)is int and a else {} if type(a)is int else env[a];bb={0:b} if type(b)is int and b else {} if type(b)is int else env[b];r={}
   if o=='*':
    for i,x in aa.items():
     for j,y in bb.items():r[i+j]=r.get(i+j,0)+x*y
   else:
    r=dict(aa)
    for j,y in bb.items():r[j]=r.get(j,0)+(y if o=='+' else -y)
   env[n]={i:x for i,x in r.items() if x}
 return env

def leading_degree(parent,p,seed=0,mod=1000000007):
 pure={}
 for old,pol in q_polynomials(parent).items():
  if old in p['map'] and type(p['map'][old])is str:
   n=p['map'][old];ck(n not in pure or pure[n]==pol,'pure-Q alias');pure[n]=pol
 qname=p['map'][parent['ports']['Q']];main=p['map']['selection__R15'];env={};line={}
 for i,n in enumerate(p['free']):
  if n in p['fixed_numerals']:
   c=p['fixture_fixed_bindings'][n]%mod;env[n]=(0,c) if c else (-1,0)
  else:
   c=(i*i+3+17*seed)%mod;env[n]=(1,c);line[n]=c
 def get(x):return env[x] if type(x)is str else ((0,x%mod) if x%mod else (-1,0))
 for n,o,a,b in p['source']:
  da,ca=get(a);db,cb=get(b)
  if o=='*':v=(-1,0) if min(da,db)<0 else (da+db,ca*cb%mod)
  else:
   degree=max(da,db);lc=((ca if da==degree else 0)+(cb if db==degree else 0)*(1 if o=='+' else -1))%mod;v=(degree,lc)
  if n in pure and n!=qname:
   pol=pure[n]
   if not pol:v=(-1,0)
   else:
    d=max(pol);qd,qc=env[qname];v=(d*qd,pol[d]*pow(qc,d,mod)%mod)
  if p['population_chart'] and not p['flow_chart']:
   for label,start in [('dst',1),('src',2)]:
    if n==p['map'].get(p['parent_contract'][label]):
     names=parent['ports']['edge_hats'][start:];v=(1,sum(get(t)[1] for t in names)%mod)
  if n==main:
   vals=[get(p['map'].get(t,t)) for t in ['selection__R12','selection__R10a','selection__ga','selection__a4m5']];v=(sum(d for d,c in vals),2)
   for d,c in vals:v=(v[0],v[1]*c%mod)
  if v[0]==0 and v[1]==0:v=(-1,0)
  ck(v[0]<0 or v[1]!=0,'uncertified leading cancellation '+str((p['name'],p['chart'],n,o,a,b,[key for key,value in p['map'].items() if value==n],da,db)))
  env[n]=v
 par=p['degree_parameters'];s=par['s'];d=par['d'];expected=[5*d-s+4,9*d-2*s+5,6*d+14,4*d-s+2,4*d-s+2,8*d-2*s+4,s]
 names=['first_unit','selection__R15','selection__P17','index_unit','linear_unit','strong_unit','joint_bound_unit'];factors=[]
 for name,want in zip(names,expected):
  degree,lc=env[p['map'][name]];ck(degree==want,'factor exact degree '+name);factors.append({'factor':name,'degree':degree,'leading_coefficient_mod':lc})
 ck(env[qname][0]==s,'chart Q degree');ck(env[p['map'][parent['ports']['q']]][0]==d,'native q degree');ck(env[p['output']][0]==p['ledger']['proved_exact_degree'],'full leading degree')
 return {'modulus':mod,'seed':seed,'slope_recipe':'i*i+3+17*seed for each nonfixed free port index i','native_factors':factors,'native_product_degree':sum(expected),'full_degree':env[p['output']][0],'full_leading_coefficient_mod':env[p['output']][1],'proved_nonzero_pure_Q_overrides':len(pure),'main_norm_override':'independently expanded unique maximal term 2*a*c*g*H'}

def dense_degree(p):
 mod=1000000007;env={n:[v%mod] for n,v in p['fixture_fixed_bindings'].items()}
 for i,n in enumerate(p['free']):
  if n not in env:env[n]=[i+2,(i*i+3)%mod]
 for name,op,l,r in p['source']:
  a=env[l] if type(l)is str else [l%mod];b=env[r] if type(r)is str else [r%mod]
  if op=='*':
   c=[0]*(len(a)+len(b)-1)
   for i,u in enumerate(a):
    if u:
     for j,v in enumerate(b):
      if v:c[i+j]=(c[i+j]+u*v)%mod
  else:
   c=[0]*max(len(a),len(b))
   for i,u in enumerate(a):c[i]=u
   for i,v in enumerate(b):c[i]=(c[i]+v*(1 if op=='+' else -1))%mod
  while len(c)>1 and c[-1]==0:c.pop()
  env[name]=c
 out=env[p['output']];ck(len(out)-1==p['ledger']['proved_exact_degree'],'dense diagnostic degree')
 return {'degree':len(out)-1,'modulus':mod,'leading_coefficient':out[-1],'all_coefficients_sha256':sha(json.dumps(out,separators=(',',':')).encode())}

def evaluate(p,v,mod=None):
 env=dict(v)
 for n,o,a,b in p['source']:
  aa=env[a] if type(a)is str else a;bb=env[b] if type(b)is str else b;r=aa*bb if o=='*' else aa+bb if o=='+' else aa-bb;env[n]=r if mod is None else r%mod
 return env

def modular_checks(parent,p):
 out=[];rng=random.Random(1671+len(p['source']))
 for mod in [1000000007,1000000009]:
  for k in range(4):
   v={n:rng.randrange(-20,21) for n in p['free']}
   if k%2==0:v.update(p['fixture_fixed_bindings'])
   child=evaluate(p,v,mod);lift=dict(v)
   for flag,n in [(p['population_chart'],p['parent_contract']['edge0']),(p['flow_chart'],p['parent_contract']['edge1'])]:
    if flag:lift[n]=child[p['map'][n]]
   old=evaluate(parent,lift,mod)
   for n,t in p['map'].items():
    if n in old:ck(old[n]%mod==(child[t] if type(t)is str else t)%mod,'full modular pullback node')
   ck(old[parent['output']]==child[p['output']],'full modular pullback');out.append({'modulus':mod,'case':k,'output':child[p['output']]})
 return out

def build(root):
 for n,h in PINS.items():ck(sha((root/n).read_bytes())==h,'pin '+n)
 base=parse(root/'matrix193_composed_output_scout.json');ck(base['source_sha256']==PINS['matrix193_composed_output_scout.py'],'parent receipt/source pin');packets=[]
 for i,parent in enumerate(base['packets']):
  main_identity=main_norm_identity(parent)
  for pop,flow in [(False,True),(True,False),(True,True)]:
   p=transform(parent,pop,flow);p['whole_source_pullback']=pullback_identity(parent,p);p['main_norm_identity']=main_identity;p['retained_residual_wires']=[p['map'][r] for r in p['parent_contract']['residuals'] if r not in p['removed_residuals']];p['removed_hat_maps']={hat:p['map'][hat] for flag,hat in [(pop,p['parent_contract']['edge0']),(flow,p['parent_contract']['edge1'])] if flag};p['leading_degree_checks']=[leading_degree(parent,p,seed) for seed in [0,1]];p['modular_checks']=modular_checks(parent,p)
   aa=[r['products'][j]['coefficients'][0] for r in parent['extraction'] for j in [0,1]];ck(parent['padding']%2==0 and parent['padding']//2>max(map(abs,aa)),'uniform population tie margin');p['degree_tie_margin']={'half_padding':parent['padding']//2,'first_reverse_word_leaders':aa,'strictly_larger_than_all_absolute_leaders':True}
   if i==0:p['dense_diagnostic_degree']=dense_degree(p)
   packets.append(p)
 ck([p['ledger']['total'] for p in packets]==[298,300,295,1674,1676,1671],'all six literal counts');ck([p['ledger']['positive_witnesses'] for p in packets]==[50,50,49,145,145,144],'witness counts')
 return {'schema':'matrix193-positive-controller-charts-v1','pins':PINS,'source_sha256':sha(Path(__file__).read_bytes()),'scope':{'predecessor_code_executed':False,'source_parent':'composed1679, not the entry-shared1624 or separate flow identity source','positive_domain':'valid fixed recipe, x>=0, all supplied witnesses positive integers','positive_maps':'computed positive missing hats; inverse given by parent residual equalities','established_universal84_unchanged':True,'IDLE_removal_included':False,'new_giant_fixture_or_native_Pell_claim':False},'packets':packets}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--write',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();r=build(a.root)
 if a.write:a.write.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:ck(exact(r,parse(a.expect)),'exact typed receipt mismatch')
 print('PASS: six complete positive charts;actual1674/1676/1671;full pullbacks;degree53347/71107;three dense diagnostic degrees')
if __name__=='__main__':main()
