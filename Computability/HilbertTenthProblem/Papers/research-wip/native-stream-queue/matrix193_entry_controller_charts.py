#!/usr/bin/env python3
"""Fresh actual-table charts of the pinned entry-shared/reduced-flow source.
Transformer and small-ring code adapted as text from the positive-chart helper.
All frozen predecessor files are inert JSON/text, never imported or executed.
"""
import argparse,copy,hashlib,json,random
from collections import Counter
from pathlib import Path
PINS={'matrix193_entry_flow_scout.py': '0a34977902f9ada25c5007c2576d0aa2a1761bf4e8cd4d5bcad49344388a43bf', 'matrix193_entry_flow_scout.json': '321a8c77b63a62d131dc52073d85f27a1f1f5086a2e19e0e42dca2df398e88da', 'matrix193_entry_flow_scout.md': '5a6c5330e2d29a6149965ed671bedd1838c0114deb240d1e55992960ce3d32f2', 'matrix193_positive_controller_charts.py': 'b21efd94fab1ce963f39805f46721b5d69c39caf926711764d0a25a6ccbcb1a1', 'matrix193_positive_controller_charts.json': '73eeb092a3ae9f4a9186a7b05f910024c7839c5f76c09dab535ee5b92668ae12', 'matrix193_positive_controller_charts.md': 'e7fda47c1c60c168d65307edb78b77709b0b24c10827ace85d2e6b82e752f53c', 'matrix193_composed_output_scout.py': 'e8b2982bdf00a9be6e6e80a1b86c38f3536a5345c60adf3103e8f7356ed01317', 'matrix193_composed_output_scout.json': 'a231b3ef66f0ab0f729bf50e40f87fad5a5d784e089249dbb4e93e11696a9e37', 'matrix193_composed_output_scout.md': '83711eab17b18f38c2bd47ddd3d803fde5adf339f7b5bbc0be2839a3bfeff748'}
def ck(v,m):
 if not v:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def parse(p):
 def obj(xs):
  d={}
  for k,v in xs:ck(k not in d,'duplicate JSON key');d[k]=v
  return d
 return json.loads(p.read_text(),object_pairs_hook=obj,parse_constant=lambda x:(_ for _ in ()).throw(ValueError('nonfinite JSON')))
def exact(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def controller_pattern(p):
 by={r[0]:r for r in p['source']};EL,ES=p['ports']['raw_edges'];B=p['ports']['B'];J=p['ports']['J'];P=p['ports']['P'];e0,e1=p['ports']['edge_hats'][:2]
 ck(by[EL]==[EL,'-',e0,1] and by[ES]==[ES,'-',e1,1],'literal raw edges')
 pp=by[P];ck(pp[1]=='+' and pp[3]==1,'P plus one');product=by[pp[2]];ck(product[1]=='*' and product[3]==J,'P product');bm=product[2];ck(by[bm]==[bm,'-',B,1],'literal B minus one')
 left,right=p['comparisons'][18];lr=by[left]
 if right==ES:
  ck(lr[1]=='+' and lr[3]==1,'reduced flow plus one');ck(by[lr[2]]==[lr[2],'*',bm,EL],'reduced flow product');kind='reduced';dst=src=None
 else:
  rr=by[right];ck(lr[1]=='+' and lr[3]==P and rr[1]=='*' and rr[2]==B,'expanded flow outer')
  src=lr[2];dst=rr[3];ck(by[src]==[src,'-',dst,ES] and by[dst]==[dst,'-',J,EL],'expanded flow source');kind='expanded'
 left,right=p['comparisons'][19];ck(by[left]==[left,'*',bm,'population_quotient'],'population left');row=by[right];ck(row[1:] and row[1]=='-' and row[3]=='x','population subtraction');ck(by[row[2]]==[row[2],'+',EL,bm],'population right')
 tail=p['source'][-62:];res=[]
 for i,(a,b) in enumerate(p['comparisons']):ck(tail[2*i][1:]==['-',a,b] and tail[2*i+1][1:]==['*',tail[2*i][0],tail[2*i][0]],'literal squared residual');res.append(tail[2*i][0])
 return {'bm':bm,'EL':EL,'ES':ES,'edge0':e0,'edge1':e1,'J':J,'dst':dst,'src':src,'flow_form':kind,'residuals':res}

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

def parent_identity(new,old):
 # Four exact univariate identities plus the separately expanded flow identity
 # suffice; every remaining full-DAG node is interpreted with these proved cuts.
 ck(new['free']==old['free'] and new['witnesses']==old['witnesses'],'identical parent supplied interfaces')
 nc=controller_pattern(new);oc=controller_pattern(old);ck(nc['flow_form']=='reduced' and oc['flow_form']=='expanded','parent flow forms');control_ring(False,False)
 polys=[q_polynomials(p) for p in [new,old]];cuts=[{},{}];certs=[]
 for i,(nx,ox) in enumerate(zip(new['extraction'],old['extraction'])):
  ck(nx['length']==ox['length'],'same block length')
  for j,(np,op) in enumerate(zip(nx['products'],ox['products'])):
   ck(np['coefficients']==op['coefficients'],'same literal coefficient table');wanted={nx['length']-1-k:c for k,c in enumerate(np['coefficients']) if c};pn=polys[0][np['polynomial']];po=polys[1][op['polynomial']]
   ck(pn==po==wanted,'complete coefficient polynomial identity');token=('coefficient',i,j)
   cuts[0][np['polynomial']]=token;cuts[1][op['polynomial']]=token;certs.append({'new':np['polynomial'],'old':op['polynomial'],'degree':max(wanted),'nonzero_coefficients':len(wanted),'expanded_coefficients_sha256':sha(json.dumps(sorted(wanted.items()),separators=(',',':')).encode())})
 cache={}
 def operation(o,a,b):
  k=(o,a,b)
  if k not in cache:cache[k]=len(cache)
  return ('node',cache[k])
 envs=[]
 for p,cut,contract in zip([new,old],cuts,[nc,oc]):
  env={n:('free',n) for n in p['free']}
  def val(v):return env[v] if type(v)is str else ('int',v)
  for n,o,a,b in p['source']:
   if n in cut:env[n]=cut[n]
   elif n==contract['residuals'][18]:env[n]=operation('-',operation('+',operation('*',val(contract['bm']),val(contract['EL'])),('int',1)),val(contract['ES']))
   else:env[n]=operation(o,val(a),val(b))
  envs.append(env)
 ck(envs[0][new['ports']['Q']]==envs[1][old['ports']['Q']],'identical paid Q for coefficient cuts')
 for i in range(2):
  p=[new,old][i];contract=[nc,oc][i]
  ck(p['source'][-2][1:]==['*','eight_units',p['source'][-3][0]] and p['source'][-1][1:]==['-',p['source'][-2][0],1],'integer product-SOS finalizer')
 checks={}
 shared=(envs[0].keys() & envs[1].keys())-set(new['free'])
 for n in shared:ck(envs[0][n]==envs[1][n],'every shared parent register '+n)
 checks['all_common_paid_registers']=len(shared)
 native_start=new['stage_counts']['packing'];native_length=new['stage_counts']['native'];ck(native_length==63,'full native row count')
 native_names=[r[0] for r in new['source'][native_start:native_start+native_length]]
 for label,names in [('native_inputs',list(new['native_cut_bindings'].values())),('native_rows',native_names),('residuals',nc['residuals'])]:
  for n in names:ck(n in envs[1] and envs[0][n]==envs[1][n],'parent full cut '+n)
  checks[label]=len(names)
 ck(envs[0][new['output']]==envs[1][old['output']],'entire parent polynomial equality')
 return {'identity':'F_entry_flow1622 = F_composed1679 on identical supplied coordinates over every commutative ring','coefficient_expansions':certs,'flow_identity':control_ring(False,False),'full_dag_cut_checks':checks,'entire_output_identity':True}

def coordinate_polynomials(parent,p):
 by={r[0]:r for r in p['source']};memo={p['map'][parent['ports']['B']]:atom('B')}
 for n in ['x','population_quotient',parent['ports']['edge_hats'][0]]:
  if n in p['free']:memo[n]=atom(n)
 def get(v):
  if type(v)is int:return con(v)
  if v not in memo:
   _,o,a,b=by[v];aa=get(a);bb=get(b);memo[v]=mul(aa,bb) if o=='*' else add(aa,bb,1 if o=='+' else -1)
  return memo[v]
 b=add(atom('B'),con(1),-1);E=add(atom('x'),mul(b,add(atom('population_quotient'),con(1),-1))) if p['population_chart'] else add(atom(parent['ports']['edge_hats'][0]),con(1),-1)
 expected={}
 if p['population_chart']:expected[parent['ports']['edge_hats'][0]]=add(E,con(1))
 if p['flow_chart']:expected[parent['ports']['edge_hats'][1]]=add(con(2),mul(b,E))
 out={}
 for hat,pol in expected.items():
  ck(get(p['map'][hat])==pol,'literal complete missing-hat coordinate polynomial');out[hat]=[[[[v,e] for v,e in mon],c] for mon,c in sorted(pol.items())]
 return out

def build(root):
 for n,h in PINS.items():ck(sha((root/n).read_bytes())==h,'pin '+n)
 base=parse(root/'matrix193_entry_flow_scout.json');oldbase=parse(root/'matrix193_composed_output_scout.json');charts=parse(root/'matrix193_positive_controller_charts.json')
 for stem,r in [('matrix193_entry_flow_scout',base),('matrix193_composed_output_scout',oldbase),('matrix193_positive_controller_charts',charts)]:ck(r['source_sha256']==PINS[stem+'.py'],'receipt/source pin')
 parent=base['packet'];oldparent=oldbase['packets'][-1];same=parent_identity(parent,oldparent);packets=[]
 for i,(pop,flow) in enumerate([(False,True),(True,False),(True,True)]):
  p=transform(parent,pop,flow);p['whole_source_pullback']=pullback_identity(parent,p);p['retained_residual_wires']=[p['map'][r] for r in p['parent_contract']['residuals'] if r not in p['removed_residuals']];p['removed_hat_maps']={hat:p['map'][hat] for flag,hat in [(pop,p['parent_contract']['edge0']),(flow,p['parent_contract']['edge1'])] if flag};p['modular_checks']=modular_checks(parent,p)
  reference=charts['packets'][i+3];rebuilt=transform(oldparent,pop,flow)
  for key in ['free','witnesses','source','output','map','removed_residuals','degree_parameters']:ck(exact(rebuilt[key],reference[key]),'literal frozen reference chart '+key)
  refproof=pullback_identity(oldparent,rebuilt);p['coordinate_polynomials']=coordinate_polynomials(parent,p);ck(p['coordinate_polynomials']==coordinate_polynomials(oldparent,rebuilt),'identical exact coordinate maps')
  ck(p['free']==reference['free'] and p['witnesses']==reference['witnesses'],'identical chart supplied interfaces');ck(p['control_identity']==reference['control_identity'],'identical polynomial coordinate substitution')
  degree=reference['ledger']['proved_exact_degree'];ck(p['ledger']['proved_exact_degree']==degree,'exact degree transfer')
  p['degree_transfer']={'whole_polynomial_identity':'F_new_'+p['chart']+' = F_original_'+p['chart']+' on identical supplied coordinates','reference_chart_index':i+3,'reference_full_array_sha256':sha(json.dumps(reference['source'],separators=(',',':')).encode()),'reference_array_reconstructed_exactly':True,'reference_pullback_rechecked':refproof,'exact_degree':degree,'new_dense_expansion_claimed':False}
  p['coefficient_rows_retained']=sum(1 for row in parent['coefficient_component'] if row[0] in p['map']);ck(p['coefficient_rows_retained']==578,'complete entry component retained')
  p['ledger']['distinct_integer_literals']=len({v for row in p['source'] for v in row[2:] if type(v)is int});packets.append(p)
 ck([p['ledger']['total'] for p in packets]==[1619,1619,1616],'three actual literal counts');ck([p['ledger']['positive_witnesses'] for p in packets]==[145,145,144],'witness counts')
 return {'schema':'matrix193-entry-controller-charts-v1','pins':PINS,'source_sha256':sha(Path(__file__).read_bytes()),'scope':{'predecessor_code_executed':False,'source_copy':'positive-controller-chart transformer and exact-ring routines copied as text then adapted to reduced-flow parent','source_parent':'entry-shared reduced-flow1622 actual table only','positive_domain':'valid fixed recipe, x>=0, all supplied witnesses positive integers','positive_maps':'computed positive missing hats; inverse given by parent residual equalities','established_universal84_unchanged':True,'IDLE_removal_included':False,'new_giant_fixture_or_native_Pell_claim':False,'diagnostic_emitted_or_replayed':False},'parent_complete_identity':same,'packets':packets,'inherited_diagnostic':{'status':'not emitted, not replayed, no new diagnostic saving claimed','reference':'pinned original positive chart packet, first three entries'}}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--write',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();r=build(a.root)
 if a.write:a.write.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:ck(exact(r,parse(a.expect)),'exact typed receipt mismatch')
 print('PASS: three complete actual charts;1619/1619/1616;full pullbacks;exact degree53347/71107 transferred')
if __name__=='__main__':main()
