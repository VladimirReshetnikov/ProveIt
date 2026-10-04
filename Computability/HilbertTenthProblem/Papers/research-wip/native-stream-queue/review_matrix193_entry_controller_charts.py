#!/usr/bin/env python3
"""Independent chart-coordinate and complete-DAG audit; all parents are data."""
import argparse,hashlib,json
from collections import Counter
from pathlib import Path
AUTHOR_PINS={
 'matrix193_entry_controller_charts.py':'7c1e55ca1396958f234c2caf6c117702c4d69537cefcad51089498cb1e58f2bf',
 'matrix193_entry_controller_charts.json':'d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571',
 'matrix193_entry_controller_charts.md':'27245d944d03b1d31ad79470dfd5625798834b7a47c1a03dee319f198214d122'}
DEPENDENCY_PINS={
 'matrix193_entry_flow_scout.py':'0a34977902f9ada25c5007c2576d0aa2a1761bf4e8cd4d5bcad49344388a43bf',
 'matrix193_entry_flow_scout.json':'321a8c77b63a62d131dc52073d85f27a1f1f5086a2e19e0e42dca2df398e88da',
 'matrix193_entry_flow_scout.md':'5a6c5330e2d29a6149965ed671bedd1838c0114deb240d1e55992960ce3d32f2',
 'matrix193_positive_controller_charts.py':'b21efd94fab1ce963f39805f46721b5d69c39caf926711764d0a25a6ccbcb1a1',
 'matrix193_positive_controller_charts.json':'73eeb092a3ae9f4a9186a7b05f910024c7839c5f76c09dab535ee5b92668ae12',
 'matrix193_positive_controller_charts.md':'e7fda47c1c60c168d65307edb78b77709b0b24c10827ace85d2e6b82e752f53c',
 'matrix193_composed_output_scout.py':'e8b2982bdf00a9be6e6e80a1b86c38f3536a5345c60adf3103e8f7356ed01317',
 'matrix193_composed_output_scout.json':'a231b3ef66f0ab0f729bf50e40f87fad5a5d784e089249dbb4e93e11696a9e37',
 'matrix193_composed_output_scout.md':'83711eab17b18f38c2bd47ddd3d803fde5adf339f7b5bbc0be2839a3bfeff748'}
def ck(v,m):
 if not v:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def enc(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def read(p):
 def obj(xs):
  d={}
  for k,v in xs:ck(k not in d,'duplicate key');d[k]=v
  return d
 def bad(x):raise ValueError('nonfinite JSON')
 return json.loads(p.read_text(),object_pairs_hook=obj,parse_constant=bad)

class Terms:
 def __init__(self):self.keys={}
 def node(self,key):
  if key not in self.keys:self.keys[key]=len(self.keys)
  return ('node',self.keys[key])
 def constant(self,v):return ('integer',v)
 def free(self,v):return self.node(('free',v))
 def op(self,op,a,b):
  c=self.constant;zero=c(0);one=c(1)
  if a[0]==b[0]=='integer':return c(a[1]*b[1] if op=='*' else a[1]+b[1] if op=='+' else a[1]-b[1])
  if op=='*':
   if a==zero or b==zero:return zero
   if a==one:return b
   if b==one:return a
  if op in ['+','-'] and b==zero:return a
  if op=='+' and a==zero:return b
  if op=='-' and a==b:return zero
  if op in ['+','*'] and b<a:a,b=b,a
  return self.node((op,a,b))
 def evaluate(self,p,free=None,overrides=None):
  env={s:self.free(s) for s in p['free']} if free is None else dict(free);overrides=overrides or {}
  for n,op,l,r in p['source']:
   env[n]=overrides[n] if n in overrides else self.op(op,env[l] if type(l)is str else self.constant(l),env[r] if type(r)is str else self.constant(r))
  return env

def contract(parent):
 by={r[0]:r for r in parent['source']};EL,ES=parent['ports']['raw_edges'];e0,e1=parent['ports']['edge_hats'][:2]
 ck(by[EL]==[EL,'-',e0,1] and by[ES]==[ES,'-',e1,1],'literal raw hats')
 B=parent['ports']['B'];P=parent['ports']['P'];J=parent['ports']['J'];prod=by[P][2];bm=by[prod][2]
 ck(by[bm]==[bm,'-',B,1] and by[prod]==[prod,'*',bm,J] and by[P]==[P,'+',prod,1],'literal P=bm*J+1')
 fl,fr=parent['comparisons'][18];fp=by[fl][2]
 if fr==ES:
  ck(by[fl]==[fl,'+',fp,1] and by[fp]==[fp,'*',bm,EL],'reduced flow cone');kind='reduced'
 else:
  ck(by[fl]==[fl,'+',fp,P] and by[fr][1:3]==['*',B],'expanded flow outer')
  prior=by[fr][3];ck(by[fp]==[fp,'-',prior,ES] and by[prior]==[prior,'-',J,EL],'expanded flow difference');kind='expanded'
 pl,pr=parent['comparisons'][19];pr0=by[pr][2]
 ck(by[pl]==[pl,'*',bm,'population_quotient'] and by[pr]==[pr,'-',pr0,'x'] and by[pr0]==[pr0,'+',EL,bm],'population cone')
 tail=parent['source'][-62:];res=[]
 for i,(l,r) in enumerate(parent['comparisons']):
  ck(tail[2*i][1:]==['-',l,r] and tail[2*i+1][1:]==['*',tail[2*i][0],tail[2*i][0]],'all residual squares');res.append(tail[2*i][0])
 sums=[tail[2*i+1][0] for i in range(20)];current=sums[0]
 for row,term in zip(tail[40:59],sums[1:]):
  ck(row[1:]==['+',current,term],'full SOS sum');current=row[0]
 ck(tail[59][1:]==['+',current,1] and tail[60][1:]==['*','eight_units',tail[59][0]] and tail[61][1:]==['-',tail[60][0],1],'integer finalizer')
 return {'B':B,'bm':bm,'EL':EL,'ES':ES,'e0':e0,'e1':e1,'residuals':res,'flow_kind':kind}

def graph(p):
 known=set(p['free']);ck(len(known)==len(p['free']),'unique ports');deps={};counts=Counter()
 for n,op,l,r in p['source']:
  ck(n not in known and op in ['+','-','*'] and all(type(v)is int or v in known for v in (l,r)),'literal topology')
  known.add(n);deps[n]=(l,r);counts[op]+=1
 live=set();todo=[p['output']]
 while todo:
  v=todo.pop()
  if type(v)is str and v not in live:live.add(v);todo.extend(deps.get(v,()))
 ck(live==known,'all rows and free ports live')
 got=(len(p['source']),counts['*'],counts['+']+counts['-'],len(p['witnesses']))
 ck(got[:3]==(p['ledger']['total'],p['ledger']['M'],p['ledger']['A']),'literal paid count')
 ck(got[3]==p['ledger']['positive_witnesses'],'positive witness count')
 return {'total':got[0],'M':got[1],'A':got[2],'witnesses':got[3],'all_live':True}

def check_chart(parent,p,original):
 c=contract(parent);pop=p['population_chart'];flow=p['flow_chart'];T=Terms();env=T.evaluate(p)
 value=lambda v:env[v] if type(v)is str else T.constant(v)
 one=T.constant(1)
 removed={c['e0']} if pop else set()
 if flow:removed.add(c['e1'])
 ck(p['free']==[v for v in parent['free'] if v not in removed],'exact free projection')
 ck(p['witnesses']==[v for v in parent['witnesses'] if v not in removed],'exact witness projection')
 ck(p['fixed_numerals']==parent['fixed_numerals'] and p['fixture_fixed_bindings']==parent['fixture_fixed_bindings'],'unchanged fixed coefficient interface')
 # Reconstruct B from the actual unchanged parent cone without using an
 # author map or an assumption about either deleted edge coordinate.
 by={r[0]:r for r in parent['source']};memo={s:T.free(s) for s in p['free']}
 def get(v):
  if type(v)is int:return T.constant(v)
  if v not in memo:
   ck(v not in removed,'B independent of deleted hats');_,op,l,r=by[v];memo[v]=T.op(op,get(l),get(r))
  return memo[v]
 bm=get(c['bm']);ck(bm==value(p['map'][c['bm']]),'paid B-minus-one same polynomial')
 E=T.op('+',T.op('*',bm,T.op('-',T.free('population_quotient'),one)),T.free('x')) if pop else T.op('-',T.free(c['e0']),one)
 S=T.op('+',T.op('*',bm,E),one) if flow else T.op('-',T.free(c['e1']),one)
 free={s:T.free(s) for s in p['free']};special={};maps={}
 for flag,hat,raw,expr in [(pop,c['e0'],c['EL'],E),(flow,c['e1'],c['ES'],S)]:
  if flag:
   hat_expr=T.op('+',expr,one);ck(value(p['map'][hat])==hat_expr and value(p['map'][raw])==expr,'independently derived hat/raw chart')
   free[hat]=hat_expr;special[raw]=expr;maps[hat]=p['map'][hat]
 zeros=[]
 if flow:zeros.append(c['residuals'][18])
 if pop:zeros.append(c['residuals'][19])
 # Direct identities: r_flow=1+bm*E-S; r_pop=x+bm*(u-1)-E.
 # The substitutions above make the selected expressions identically zero.
 for n in zeros:special[n]=T.constant(0)
 ck(set(zeros)==set(p['removed_residuals']),'exact eliminated residuals')
 old=T.evaluate(parent,free,special);checked=0
 for n,v in p['map'].items():
  ck(n in old and old[n]==value(v),'every reached parent wire '+n);checked+=1
 ck(old[parent['output']]==env[p['output']],'entire parent pullback')
 ck(p['free']==original['free'] and p['witnesses']==original['witnesses'],'same coordinate interface as original chart')
 earlier=T.evaluate(original)
 for hat in removed:
  v=original['map'][hat];oldhat=earlier[v] if type(v)is str else T.constant(v)
  ck(oldhat==free[hat],'identical nonlinear substitution to original chart')
 ck(p['ledger']['proved_exact_degree']==original['ledger']['proved_exact_degree'],'exact degree via identical chart polynomial')
 native=parent['source'][parent['stage_counts']['packing']:parent['stage_counts']['packing']+63]
 for n in list(parent['native_cut_bindings'].values())+[r[0] for r in native]+c['residuals']:
  ck(n in p['map'] and old[n]==value(p['map'][n]),'full native/residual mapped register '+n)
 retained=[p['map'][n] for n in c['residuals'] if n not in zeros]
 ck(retained==p['retained_residual_wires'] and len(retained)==20-int(pop)-int(flow),'exact retained residual list')
 literals={v for r in p['source'] for v in r[2:] if type(v)is int}
 if 'distinct_integer_literals' in p['ledger']:ck(len(literals)==p['ledger']['distinct_integer_literals'],'literal count')
 return {'chart':p['chart'],'ledger':graph(p),'reached_parent_symbols':checked,'reached_paid_parent_registers':sum(n in by for n in p['map']),'removed_hats':sorted(removed),
         'removed_residuals':zeros,'all_ring_pullback':True,'same_original_chart_coordinate_map':True,
         'exact_degree_inherited':original['ledger']['proved_exact_degree'],
         'native_inputs':6,'native_rows':63,'residual_maps':20,'retained_residuals':len(retained),'integer_literals':len(literals),
         'positive_domain':'x>=0; valid fixed numerals; positive integer supplied witnesses; inverse uses integer SOS finalizer'}

# Dense coefficient vectors in one paid Q; independent of the author's sparse
# exponent dictionaries and source emitter.
def polynomial_cone(p):
 Q=p['ports']['Q'];env={Q:[0,1]}
 for n,op,l,r in p['source']:
  if n==Q or not all(type(v)is int or v in env for v in (l,r)):continue
  a=[l] if type(l)is int else env[l];b=[r] if type(r)is int else env[r]
  if op=='*':
   out=[0]*(len(a)+len(b)-1)
   for i,x in enumerate(a):
    for j,y in enumerate(b):out[i+j]+=x*y
  else:
   out=[0]*max(len(a),len(b))
   for i,x in enumerate(a):out[i]+=x
   for i,x in enumerate(b):out[i]+=x if op=='+' else -x
  while len(out)>1 and out[-1]==0:out.pop()
  env[n]=out
 return env

def parent_identity(new,old):
 ck(new['free']==old['free'] and new['witnesses']==old['witnesses'],'whole parent interface')
 cn=contract(new);co=contract(old);ck(cn['flow_kind']=='reduced' and co['flow_kind']=='expanded','two authenticated flow forms')
 T=Terms();cuts=[{},{}];records=[];dense=[polynomial_cone(new),polynomial_cone(old)]
 for bi,(nb,ob) in enumerate(zip(new['extraction'],old['extraction'])):
  ck(nb['length']==ob['length'],'block length')
  for ci,(np,op) in enumerate(zip(nb['products'],ob['products'])):
   nv=dense[0][np['polynomial']];ov=dense[1][op['polynomial']]
   wanted=list(reversed(np['coefficients']))
   while len(wanted)>1 and wanted[-1]==0:wanted.pop()
   ck(np['coefficients']==op['coefficients'] and nv==ov==wanted,'complete ordered coefficient identity')
   token=T.free('PROVED_COEFFICIENT_'+str((bi,ci)));cuts[0][np['polynomial']]=token;cuts[1][op['polynomial']]=token
   records.append({'entry_wire':np['polynomial'],'composed_wire':op['polynomial'],'degree':len(nv)-1,'nonzero':sum(v!=0 for v in nv),'dense_sha256':sha(enc(nv))})
 envs=[]
 for p,c,cut in zip((new,old),(cn,co),cuts):
  env={v:T.free(v) for v in p['free']}
  def val(v):return env[v] if type(v)is str else T.constant(v)
  for n,op,l,r in p['source']:
   if n in cut:env[n]=cut[n]
   elif n==c['residuals'][18]:
    env[n]=T.op('-',T.op('+',T.op('*',val(c['bm']),val(c['EL'])),T.constant(1)),val(c['ES']))
   else:env[n]=T.op(op,val(l),val(r))
  envs.append(env)
 ck(envs[0][new['ports']['Q']]==envs[1][old['ports']['Q']],'common paid Q proven before coefficient cuts')
 shared=(set(envs[0])&set(envs[1]))-set(new['free'])
 for n in shared:ck(envs[0][n]==envs[1][n],'common full parent register '+n)
 ck(new['native_cut_bindings']==old['native_cut_bindings'] and len(new['native_cut_bindings'])==6,'exact native input names')
 native_sets=[]
 for p in (new,old):
  ck(p['stage_counts']['native']==63,'native stage count');start=p['stage_counts']['packing'];native_sets.append(p['source'][start:start+63])
 ck(native_sets[0]==native_sets[1],'all 63 literal parent native rows')
 for n in list(new['native_cut_bindings'].values())+[r[0] for r in native_sets[0]]+cn['residuals']:
  ck(n in shared and envs[0][n]==envs[1][n],'full parent native/residual interface '+n)
 ck(envs[0][new['output']]==envs[1][old['output']],'entire parent polynomial equality')
 return {'all_ring_identity':True,'coefficient_polynomials':records,'all_common_paid_registers':len(shared),'paid_Q_identity':True,'native_rows':63,'native_inputs':6,'residuals':20}

# Independent exact six-variable expansion for the controller identities.
def ring_checks():
 z=(0,)*6
 def const(x):return {z:x} if x else {}
 def var(i):e=list(z);e[i]=1;return {tuple(e):1}
 def add(a,b,s=1):
  out=dict(a)
  for e,x in b.items():out[e]=out.get(e,0)+s*x
  return {e:x for e,x in out.items() if x}
 def mul(a,b):
  out={}
  for e,x in a.items():
   for f,y in b.items():g=tuple(i+j for i,j in zip(e,f));out[g]=out.get(g,0)+x*y
  return {e:x for e,x in out.items() if x}
 B,J,E0,S0,u,x=[var(i) for i in range(6)];one=const(1);b=add(B,one,-1);records=[]
 for pop,flow in [(False,False),(False,True),(True,False),(True,True)]:
  E=add(x,mul(b,add(u,one,-1))) if pop else E0;S=add(one,mul(b,E)) if flow else S0
  P=add(mul(b,J),one)
  expanded=add(add(add(add(J,E,-1),S,-1),P),mul(B,add(J,E,-1)),-1)
  reduced=add(add(one,mul(b,E)),S,-1);population=add(mul(b,u),add(add(E,b),x,-1),-1)
  ck(expanded==reduced,'expanded/reduced exact ring identity')
  if flow:ck(not reduced,'flow substitution identically zero')
  if pop:ck(not population,'population substitution identically zero')
  records.append({'population':pop,'flow':flow,'flow_terms':len(reduced),'population_terms':len(population)})
 return records

def boundary_checks():
 records=[]
 for pop,flow in [(False,True),(True,False),(True,True)]:
  count=0
  for B in [2,3,32]:
   for x in [0,1,7]:
    for u in [1,2,5]:
     for raw in [0,1,9]:
      E=x+(B-1)*(u-1) if pop else raw;S=1+(B-1)*E if flow else raw
      ck(E+1>0 and S+1>0,'positive integer reconstruction')
      if pop:ck((B-1)*u-(E+B-1-x)==0,'population boundary')
      if flow:ck(1+(B-1)*E-S==0,'flow boundary')
      count+=1
  records.append({'population':pop,'flow':flow,'arithmetic_component_cases':count,'includes_x_zero_u_one':True,'full_native_zeros_claimed':False})
 return records

def build(root,author_root):
 for directory,pins in [(root,DEPENDENCY_PINS),(author_root,AUTHOR_PINS)]:
  for name,digest in pins.items():ck(sha((directory/name).read_bytes())==digest,'pin '+name)
 author=read(author_root/'matrix193_entry_controller_charts.json')
 ck(author['pins']==DEPENDENCY_PINS and author['source_sha256']==AUTHOR_PINS['matrix193_entry_controller_charts.py'],'author provenance')
 p=read(root/'matrix193_entry_flow_scout.json')['packet'];old=read(root/'matrix193_composed_output_scout.json')['packets'][-1]
 originals=read(root/'matrix193_positive_controller_charts.json')['packets'][3:]
 ck(len(originals)==len(author['packets'])==3,'exact actual-only chart population')
 ring=ring_checks();whole=parent_identity(p,old);results=[];refs=[]
 for child,original in zip(author['packets'],originals):
  refs.append(check_chart(old,original,original));results.append(check_chart(p,child,original))
  ck(sum(row[0] in child['map'] for row in p['coefficient_component'])==578,'all coefficient rows represented')
  ck(child['degree_parameters']['N']==472 and child['degree_parameters']['longest_block']==194,'actual degree parameters')
  s=4 if child['chart']=='both' else 3
  ck(child['degree_parameters']['s']==s and child['ledger']['proved_exact_degree']==17760*s+67,'uniform exact degree formula')
 ck([(r['ledger']['total'],r['ledger']['M'],r['ledger']['A'],r['ledger']['witnesses']) for r in results]==[(1619,790,829,145),(1619,790,829,145),(1616,789,827,144)],'all emitted literal ledgers')
 return {'schema':'independent-entry-controller-charts-v1','review_source_sha256':sha(Path(__file__).read_bytes()),'author_pins':AUTHOR_PINS,'dependency_pins':DEPENDENCY_PINS,
         'parent_identity':whole,'exact_controller_ring_checks':ring,'new_charts':results,'original_full_chart_pullbacks':refs,'positive_boundary_components':boundary_checks(),
         'scope':{'old_code_executed_or_imported':False,'author_code_executed_or_imported':False,'complete_new_source_rows':4854,'actual_only':True,'giant_history_or_native_zero_materialized':False,'exact_degree_transferred_from_pinned_original_proof':True}}

def equal(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(equal(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(equal(x,y) for x,y in zip(a,b))
 return a==b
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--author-root',type=Path)
 group=ap.add_mutually_exclusive_group(required=True);group.add_argument('--write',type=Path);group.add_argument('--expect',type=Path);a=ap.parse_args()
 result=build(a.root,a.author_root or a.root)
 if a.write:a.write.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else:ck(equal(result,read(a.expect)),'exact typed receipt replay')
 print('PASS: independent 1619/1619/1616 arrays; coordinate pullbacks; full parent identity; 53347/71107 degree transfer')
if __name__=='__main__':main()
