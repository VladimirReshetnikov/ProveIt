#!/usr/bin/env python3
"""Fresh independent IDLE audit. All predecessor programs remain inert data."""
import argparse,hashlib,json,random
from collections import Counter
from pathlib import Path
AUTHOR={
 'matrix193_idle_free_scout.py':'33e6c22b35e6fd2c8735380f04433652686b0da20053c5446b139e8881f9ed94',
 'matrix193_idle_free_scout.json':'857f5af683abb1c27cba6335fd45cadbd0afc7f9c630bf312a27ea4c98aa23b7',
 'matrix193_idle_free_scout.md':'3502c8c69642ab3c90e5973a3668c896b34c23c0fdb88686338853573ac236d6'}
def ck(v,m):
 if not v:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def enc(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def read(p):
 def obj(pairs):
  d={}
  for k,v in pairs:ck(k not in d,'duplicate key');d[k]=v
  return d
 def bad(x):raise ValueError('nonfinite JSON')
 return json.loads(p.read_text(),object_pairs_hook=obj,parse_constant=bad)
def exact(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def labels(p):return (lambda v:p['map'].get(v,v)) if 'map' in p else (lambda v:v)
def graph(p):
 known=set(p['free']);ck(len(known)==len(p['free']),'unique free ports');deps={};ops=Counter()
 for n,o,a,b in p['source']:
  ck(n not in known and o in ['+','-','*'] and all(type(t)is int or t in known for t in (a,b)),'complete source topology')
  known.add(n);deps[n]=(a,b);ops[o]+=1
 live=set();todo=[p['output']]
 while todo:
  n=todo.pop()
  if type(n)is str and n not in live:live.add(n);todo.extend(deps.get(n,()))
 ck(known==live,'all paid rows and supplied ports live')
 return [len(p['source']),ops['*'],ops['+']+ops['-'],len(p['witnesses'])]

# Polynomial terms (Q exponent, hat number); hat -1 denotes a scalar.
# Only affine dependence on hats is permitted in these independently cut cones.
def ac(x):return {(0,-1):x} if x else {}
def aa(a,b,sign=1):
 d=dict(a)
 for k,v in b.items():d[k]=d.get(k,0)+sign*v
 return {k:v for k,v in d.items() if v}
def am(a,b):
 d={}
 for (e,h),v in a.items():
  for (f,j),w in b.items():
   ck(h==-1 or j==-1,'controller cone stays affine in formal hats')
   k=(e+f,max(h,j));d[k]=d.get(k,0)+v*w
 return {k:v for k,v in d.items() if v}
def affine_cone(rows,target,cuts):
 by={r[0]:r for r in rows};memo=dict(cuts)
 def get(v):
  if type(v)is int:return ac(v)
  if v not in memo:
   _,o,a,b=by[v];a=get(a);b=get(b);memo[v]=am(a,b) if o=='*' else aa(a,b,1 if o=='+' else -1)
  return memo[v]
 return get(target)

class Terms:
 def __init__(self):self.keys={}
 def node(self,key):
  if key not in self.keys:self.keys[key]=len(self.keys)
  return ('node',self.keys[key])
 def integer(self,v):return ('integer',v)
 def free(self,n):return self.node(('free',n))
 def op(self,o,a,b):return self.node((o,a,b))

def review_variant(parent,child,base,variant):
 w=labels(parent);idle='edge_hat98';by={r[0]:r for r in parent['source']}
 ck(idle in parent['witnesses'],'old positive IDLE coordinate')
 patterns=[['r104','+','r103',idle],['r105','-','r104',99],['r568','*',idle,'r108'],['r569','+','r568','edge_hat97'],['r570','*','r569','r108'],['r773','+','r772','r187'],['r774','-','r763','r773']]
 for n,o,a,b in patterns:
  ck(by[w(n)]==[w(n),o,w(a) if type(a)is str else a,w(b) if type(b)is str else b],'actual old cut row '+n)
 removed={w(n) for n in ('r104','r568','r569','r773')}
 replaced={w('r105'):[w('r105'),'-',w('r103'),98],w('r570'):[w('r570'),'*','edge_hat97',w('r108')],w('r774'):[w('r774'),'-',w('r763'),w('r772')]}
 expected=[replaced.get(r[0],r) for r in parent['source'] if r[0] not in removed]
 ck(expected==child['source'],'entire independently reconstructed source')
 for key in ['free','witnesses']:ck(child[key]==[v for v in parent[key] if v!=idle],'exact IDLE-only '+key+' difference')
 for key in ['fixed_numerals','fixture_fixed_bindings','output']:ck(child[key]==parent[key],'retained interface '+key)
 ck(child['variant']==variant,'variant label')
 horner={w('r'+str(i)) for i in range(568,764)};controller=w('r774');J=w('r105');Q=w('r108')
 for r in parent['source']:
  if r[0] not in horner and r[0]!=controller:ck(not any(t in horner for t in r[2:]),'private Horner region')
 hats=[w('edge_hat'+str(i)) for i in range(98)]
 cuts={v:{(0,i):1} for i,v in enumerate(hats)};cuts[idle]=ac(1)
 jsum={(0,i):1 for i in range(98)};jsum[(0,-1)]=-98
 for rows in [parent['source'],child['source']]:ck(affine_cone(rows,J,cuts)==jsum,'exact J expansion with actual hat cuts')
 cuts[Q]={(1,-1):1};ctrl={}
 for i in range(98):ctrl[(i,i)]=1;ctrl[(i,-1)]=-1
 for rows in [parent['source'],child['source']]:ck(affine_cone(rows,controller,cuts)==ctrl,'exact entire 98-slot controller expansion')
 ck(affine_cone(child['source'],w('r772'),{Q:{(1,-1):1}})=={(i,-1):1 for i in range(98)},'actual paid R98 cone')
 ck(affine_cone(parent['source'],w('r187'),{Q:{(1,-1):1}})=={(98,-1):1},'actual removed Q98 correction')
 T=Terms();envs=[]
 for p,old in [(parent,True),(child,False)]:
  env={n:T.free(n) for n in p['free']}
  if old:env[idle]=T.integer(1)
  def val(n):return env[n] if type(n)is str else T.integer(n)
  for n,o,a,b in p['source']:
   if n==J:env[n]=T.node(('PROVED_J',tuple(val(h) for h in hats)))
   elif n==controller:env[n]=T.node(('PROVED_CONTROLLER',val(Q),tuple(val(h) for h in hats)))
   else:env[n]=T.op(o,val(a),val(b))
  envs.append(env)
 old,new=envs;common=set(old)&set(new);checkable=common-horner
 for n in checkable:ck(old[n]==new[n],'full non-Horner retained expression '+n)
 ck(old[parent['output']]==new[child['output']],'entire output equality')
 # Authenticate all native rows and all original residual positions through
 # the real parent maps, including residuals already eliminated by a chart.
 start=base['stage_counts']['packing'];native=base['source'][start:start+63]
 ck(base['stage_counts']['native']==63 and len(base['comparisons'])==20,'complete base native and residual interface')
 residuals=[base['source'][-62+2*i][0] for i in range(20)]
 names=list(base['native_cut_bindings'].values())+[r[0] for r in native]+residuals
 for n in names:
  v=w(n)
  if type(v)is str:ck(v in checkable and old[v]==new[v],'retained native/residual position '+n)
  else:ck(v==0,'only proved-zero chart residual can be absent')
 ck(all(w(r[0]) in new for r in base['coefficient_component']),'complete 578-row coefficient component retained')
 actual=graph(child);ck(actual==[child['ledger']['total'],child['ledger']['M'],child['ledger']['A'],child['ledger']['positive_witnesses']],'literal ledger')
 ck(len({v for r in child['source'] for v in r[2:] if type(v)is int})==137,'exact integer literal count')
 return {'variant':variant,'literal_ledger':actual,'full_array_sha256':sha(enc(child['source'])),'private_horner_nodes':len(horner),'common_nonhorner_symbols':len(checkable),
         'J_terms':len(jsum),'controller_terms':len(ctrl),'R98_terms':98,'native_inputs':6,'native_rows':63,'original_residual_positions':20,'retained_coefficient_rows':578,'all_ring_output_identity':True,'all_live':True}

def evaluate(p,values,mod):
 env=dict(values)
 for n,o,a,b in p['source']:
  aa=env[a] if type(a)is str else a;bb=env[b] if type(b)is str else b
  env[n]=(aa*bb if o=='*' else aa+bb if o=='+' else aa-bb)%mod
 return env

def uniform_degree_data(base):
 # These literal guards are the source-specific parts of the uniform proof.
 groups=base['groups'];ck(len(groups)==170 and all(98 not in g['edges'] for g in groups),'IDLE selects no lane')
 ck(groups[-2]['edges']==[0] and groups[-1]['edges']==[1],'actual LOAD/SWITCH ordering')
 ck(all(1 not in g['edges'] for g in groups[:-1]),'independent SWITCH absent from both fixed blocks')
 C=base['padding'];coeffs=[pr['coefficients'][0] for b in base['extraction'] for pr in b['products']]
 ck(C>0 and C%2==0 and all(C//2>abs(a) for a in coeffs),'nonzero population degree-tie margin')
 ck(coeffs[-2:]==[-490,271],'actual Y leading coefficients')
 records=[]
 for s in [2,3,3,4]:
  d=472*s+1;native=[5*d-s+4,9*d-2*s+5,6*d+14,4*d-s+2,4*d-s+2,8*d-2*s+4,s]
  records.append({'Q_degree':s,'native_degrees':native,'native_degree_sum':sum(native),'maximum_residual_degree':387*s,'SOS_degree':774*s,'full_degree':sum(native)+774*s})
 return {'guards_checked':True,'leading_fixed_coefficients':coeffs,'uniform_degree_bookkeeping':records,'proof_scope':'quantified surviving-leading-form proof in review note; not a new dense full expansion'}

def build(root,author_root):
 for n,h in AUTHOR.items():ck(sha((author_root/n).read_bytes())==h,'author pin '+n)
 saved=read(author_root/'matrix193_idle_free_scout.json');ck(saved['source_sha256']==AUTHOR['matrix193_idle_free_scout.py'],'source self pin')
 deps=saved['pins'];ck(len(deps)==12,'exact dependency population')
 for n,h in deps.items():ck(sha((root/n).read_bytes())==h,'authenticated dependency '+n)
 base=read(root/'matrix193_entry_flow_scout.json')['packet'];charts=read(root/'matrix193_entry_controller_charts.json')['packets'];parents=[base,*charts]
 atomic=read(root/'matrix193_atomic_context_packing.json')['packets'][-1]
 ck(atomic['controller_edges'][-1]==[98,1,1,'IDLE'] and atomic['controller_edges'][1]==[1,0,1,'SWITCH'],'frozen controller boundary')
 ck(len(saved['packets'])==len(parents)==4,'exact four actual arrays')
 variants=['no_controller_chart','flow','population','both'];results=[];modular=[]
 rng=random.Random(761928)
 for i,(p,c,v) in enumerate(zip(parents,saved['packets'],variants)):
  results.append(review_variant(p,c,base,v))
  # Small new complete polynomial probes use independent seed/fields. They
  # are signed off-zero source checks, never accepting-history examples.
  for mod in [1000003,1000033]:
   values={n:rng.randrange(-31,32) for n in c['free']};values.update(c['fixture_fixed_bindings'])
   out=evaluate(c,values,mod)[c['output']];old=evaluate(p,{**values,'edge_hat98':1},mod)[p['output']]
   ck(out==old,'independent whole-source modular pullback');modular.append({'variant':v,'modulus':mod,'output':out})
 expected=[[1618,790,828,145],[1615,789,826,144],[1615,789,826,144],[1612,788,824,143]]
 ck([r['literal_ledger'] for r in results]==expected,'four complete counts')
 degrees=uniform_degree_data(base)
 ck([p['ledger']['exact_degree'] for p in saved['packets']]==[r['full_degree'] for r in degrees['uniform_degree_bookkeeping']],'claimed exact degrees match uniform proof')
 return {'schema':'independent-idle-free-review-v1','review_source_sha256':sha(Path(__file__).read_bytes()),'author_pins':AUTHOR,'dependency_pins':deps,'source_reviews':results,'degree_guards':degrees,'fresh_full_modular_checks':modular,
         'scope':{'author_or_predecessor_programs_executed_or_imported':False,'new_source_rows_checked':6460,'new_giant_or_native_fixture':False,'reverse_theorem':'ordinary-input projection only, via fresh IDLE-free positive completion','diagnostic_emitted_or_replayed':False}}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--author-root',type=Path)
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--write',type=Path);g.add_argument('--expect',type=Path);args=ap.parse_args()
 result=build(args.root,args.author_root or args.root)
 if args.write:args.write.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else:ck(exact(result,read(args.expect)),'type-sensitive exact receipt')
 print('PASS: independent four-array IDLE reconstruction; full all-ring identities; native interface; degree guards')
if __name__=='__main__':main()
