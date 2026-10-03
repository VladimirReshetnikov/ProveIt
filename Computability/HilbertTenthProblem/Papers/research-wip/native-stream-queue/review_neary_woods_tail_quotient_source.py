#!/usr/bin/env python3
"""Independent actual U9 tail-quotient source/degree/API review; standard library."""
import argparse,copy,hashlib,json,random,subprocess,sys,tempfile,types
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md': '47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b',
 '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b',
 '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90',
 'binary_tag_parameterized_compressed_compiler.py': '13da39c3292f8e19f7881f4543fa704c42edec12f29bd10b06f2df555385c0df',
 'group_projective_tail_quotient_shift.json': 'a422e7a65df26e626f3c36f97a53a68805b86806be3dc35d35e7d49a17b80b27',
 'group_projective_tail_quotient_shift.md': 'a1e1e67df618f6f809c2e85a409509b288337f62cd1af35cfc6ca950e0efa92a',
 'group_projective_tail_quotient_shift.py': '08248ad763113a6a2e60168edfd058b92be4e14b2f7932fa1be66eb406a70610',
 'native_binary_positive_scale.md': 'd958feffa5d82ede3096d8c792fbf861385f2c7c011057c587663ead4ad2ce97',
 'native_controller_binary_selector56.md': '97fcdc7188f968f2ac3e315249b0e0a15dcc787c10451924ad3f2551c8bb376c',
 'neary_woods_universal_history_scale257.md': 'dcc467b4b00a013c315856a271307459b694b69d4bd2a66c925312a042247e42',
 'neary_woods_universal_history_units260.md': '73d3787dcc10acc037f80699ec3f8bde1fb721613abac5ce489762aab339057c',
 'neary_woods_universal_initial_bound254.md': '9e1a0fd5559dc72420a5123eb4f67753576f7b06d93aff6b7b650cd40dba1f90',
 'neary_woods_universal_joint_and_coupled.md': '02333114dd0cc4396d0a82098e71fde02cc76654c5b5751041f1237732d77868',
 'neary_woods_universal_native_bound254.md': '93b723d6cbbe42e07a9e57979105cffa08f332f4e8d028e5b0aa34890e189952',
 'neary_woods_universal_product_scale253.json': 'a32b58aee2baf3d6d1a66489784f9cc9f5ab2bac296b9a7eb0a116785a3eef1b',
 'neary_woods_universal_product_scale253.md': '9b3b0566dd1365d9acf4b97b6b290b951d56eb51392e85e48f06f83b1604434f',
 'neary_woods_universal_product_scale253.py': 'eb3e8f41f79f69199bd7b620a2b8908e60915b3976898def9d59c25d92a4675e',
 'neary_woods_universal_u9_tag_chain.json': 'b4d78b1be42f6e8c16180311ce371c486d75f9de646b4d78edaf0bcd2491b727',
 'neary_woods_universal_u9_tag_chain.py': '36794dccbad7de48eebcc10ff95311a451205828b1e13f2e2415997246b5d1b8'}
AUTHOR={'neary_woods_universal_tail_quotient253.json': '48d604caf52af6cc6e37f77614787b1a02a549b03c1f5acdb53a5a7277c7504f',
 'neary_woods_universal_tail_quotient253.md': '328b9a3d62a989f78cd3c7b388eba01800a9d92e7cb8df6ac58184df9982653b',
 'neary_woods_universal_tail_quotient253.py': '291b3e22c7d1f8db99cb55c3f2e3bc6e83f92e377d44028bf8e56f1c39d7cf50'}
def need(ok,msg):
 if not ok:raise ValueError(msg)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def sha(b):return hashlib.sha256(b).hexdigest()
def pins(root,manifest):
 out={}
 for n,h in manifest.items():
  b=(Path(root)/n).read_bytes();need(sha(b)==h,'Pinned blob '+n);out[n]=b
 return out
def numeric(rows,v):
 e=dict(v)
 for n,o,a,b in rows:
  a=e[a]if type(a)is str else a;b=e[b]if type(b)is str else b;e[n]=a+b if o=='+'else a-b if o=='-'else a*b
 return e

def ledger(rows,free,outputs,fixed=()):
 known=set(free);defs={};degree={x:0 if x in fixed else 1 for x in free}
 for row in rows:
  need(type(row)is list and len(row)==4,'literal row');n,o,a,b=row
  need(type(n)is str and n not in known and o in('+','-','*'),'fresh exact gate')
  need(all(type(x)is int or type(x)is str and x in known for x in(a,b)),'source closure')
  da=degree[a]if type(a)is str else 0;db=degree[b]if type(b)is str else 0
  degree[n]=da+db if o=='*'else max(da,db);known.add(n);defs[n]=(a,b)
 live=set();stack=list(outputs)
 while stack:
  x=stack.pop()
  if type(x)is int or x in live:continue
  live.add(x);stack.extend(defs.get(x,()))
 need(set(defs)|set(free)<=live,'all paid rows/coordinates live')
 M=sum(r[1]=='*'for r in rows)
 return M,len(rows)-M,max(degree[x]if type(x)is str else 0 for x in outputs)
class RingDAG:
 # Linear combinations of opaque product atoms. Addition normalizes exact
 # coefficients; multiplication extracts scalar signs but never expands sums.
 def __init__(self):self.ids={('one',):0}
 def node(self,key):
  if key not in self.ids:self.ids[key]=len(self.ids)
  return self.ids[key]
 def val(self,x):return ((0,x),)if type(x)is int and x else()if type(x)is int else((self.node(('var',x)),1),)
 def scale(self,e,c):return tuple((k,v*c)for k,v in e)if c else()
 def add(self,a,b,sign=1):
  e=dict(a)
  for n,c in b:e[n]=e.get(n,0)+sign*c
  return tuple(sorted((n,c)for n,c in e.items()if c))
 def mul(self,a,b):
  if not a or not b:return()
  if len(a)==1 and a[0][0]==0:return self.scale(b,a[0][1])
  if len(b)==1 and b[0][0]==0:return self.scale(a,b[0][1])
  sa=-1 if a[0][1]<0 else 1;sb=-1 if b[0][1]<0 else 1
  a=self.scale(a,sa);b=self.scale(b,sb)
  if a>b:a,b=b,a
  return((self.node(('mul',a,b)),sa*sb),)
 def run(self,rows,free,replacements=None):
  e={n:self.val(n)for n in free};e.update(replacements or{})
  for n,o,a,b in rows:
   a=e[a]if type(a)is str else self.val(a);b=e[b]if type(b)is str else self.val(b)
   e[n]=self.mul(a,b)if o=='*'else self.add(a,b,1 if o=='+'else -1)
  return e


def smadd(a,b,s=1):
 r=dict(a)
 for k,v in b.items():r[k]=r.get(k,0)+s*v
 return{k:v for k,v in r.items()if v}
def smmul(a,b):
 r={}
 for u,x in a.items():
  for v,y in b.items():
   k=tuple(i+j for i,j in zip(u,v));r[k]=r.get(k,0)+x*y
 return{k:v for k,v in r.items()if v}
def scalar(n):return{(0,0,0,0):n}if n else{}
def main_identity():
 X,a,c,g=[{tuple(int(j==i)for j in range(4)):1}for i in range(4)];ac=smmul(a,c);H=smadd(smmul(scalar(4),a),scalar(3));Delta=smadd(smmul(a,a),H);d=smadd(smadd(X,ac),g)
 original=smadd(smmul(d,d),smmul(Delta,smmul(c,c)),-1);u=smadd(X,g);new=smadd(smmul(u,smadd(smmul(scalar(2),ac),u)),smmul(H,smmul(c,c)),-1)
 need(original==new,'independent exact main factorization (X+gamma)*(2ac+X+gamma)-Hc²')
 return len(original)

def full_coefficients(p,weights,prime,constants):
 def trim(v):
  while len(v)>1 and v[-1]==0:v.pop()
  return v
 def add(a,b,sgn=1):
  n=max(len(a),len(b));r=[0]*n
  for i,v in enumerate(a):r[i]=v
  for i,v in enumerate(b):r[i]=(r[i]+sgn*v)%prime
  return trim(r)
 def mul(a,b):
  if len(a)>len(b):a,b=b,a
  r=[0]*(len(a)+len(b)-1)
  for i,x in enumerate(a):
   if x:
    for j,y in enumerate(b):r[i+j]+=x*y
  return trim([x%prime for x in r])
 e={n:[0,w%prime]for n,w in weights.items()};e.update({n:[v%prime]for n,v in constants.items()})
 for n,o,a,b in p['source']:
  a=e[a]if type(a)is str else[a%prime];b=e[b]if type(b)is str else[b%prime];e[n]=mul(a,b)if o=='*'else add(a,b,1 if o=='+'else -1)
 return e

FACTORS=['geo__R15','geo__P17','geo__first_unit','and__R15','and__P17','and__first_unit','geo__f_square_minus_one','and__f_square_minus_one','geo__index_unit','and__index_unit','geo__linear_unit','and__linear_unit','mask_repunit_unit','history_upper_unit','history_global_unit','lower_history_unit']
FACTOR_DEGREES=[14,40,9,138,344,78,24,190,6,61,6,61,4,2,2,3]
FIXED=['history_radix','lower_constant','lower_difference','production_offset','recoder_radix','repunit_divisor','terminal_offset','terminal_scale','upper_constant','upper_difference','upper_offset']

def normal_rows(rows):
 def at(x):
  if type(x)is dict:
   need(set(x)=={'fixed_numeral'}and type(x['fixed_numeral'])is str and x['fixed_numeral']in FIXED,'exact named compiler numeral leaf')
   return '@fixed:'+x['fixed_numeral']
  need(type(x)in(str,int),'exact gate operand type');return x
 return[[n,o,at(a),at(b)]for n,o,a,b in rows]

def independent_child(old):
 rows=copy.deepcopy(old['source']);idx=next(i for i,r in enumerate(rows)if r[0]=='and__bs_X_bound')
 need(rows[idx]==['and__bs_X_bound','+','factored_pack_inner','and__bound_beta'],'literal old beta shift')
 rows[idx]=['and__bs_X_bound','+','factored_pack_Z','and__bound_beta'];return rows

def shape(old,child):
 rows=normal_rows(old['source']);new=normal_rows(child);defs={n:(o,a,b)for n,o,a,b in rows};vars=old['parameters']+old['auxiliaries'];constants=['@fixed:'+n for n in FIXED]
 need(len(rows)==253 and len(old['auxiliaries'])==43 and 'x'in old['parameters']and all(n.startswith('program_')for n in old['parameters']if n!='x'),'saved complete ordinary-input/program/witness interface')
 need(rows[-1]==['lower_unit_output','-','lower_history_product',1]and rows[-2]==['lower_history_product','*','history_unit_product_1','lower_history_unit'],'one literal final subtraction')
 need([n for n,o,a,b in rows if 'and__bound_beta'in(a,b)]==['and__bs_X_bound']and[n for n,o,a,b in rows if 'and__bs_X_bound'in(a,b)]==['and__wn2'],'all beta/restored-X consumers')
 expected={'factored_pack_q_minus_one':('-','and__q',1),'factored_pack_q_plus_one':('+','and__q',1),'factored_pack_Z':('*','factored_pack_q_minus_one','and__F3'),'factored_pack_B':('+','and__padded_B','factored_pack_Z'),'factored_pack_scaled_B':('*','factored_pack_q_plus_one','factored_pack_B'),'factored_pack_inner':('+','factored_pack_A_plus_one','factored_pack_scaled_B'),'and__bs_packed':('*','factored_pack_q_minus_one','factored_pack_inner'),'and__wn2':('*','and__bs_X_bound','and__q'),'and__normalized_strong_Q':('*','and__A','and__ic22'),'and__f_square_minus_one':('-','and__L16','and__normalized_strong_Q'),'and__R16':('*','and__A','and__normalized_strong_Q')}
 need(all(defs[n]==v for n,v in expected.items()),'actual packed shift/index and normalized strong ports')
 deps={n:{n}for n in vars+constants}
 for n,o,a,b in rows:deps[n]=(deps[a]if type(a)is str else set())|(deps[b]if type(b)is str else set())
 need('and__bound_beta'not in deps['factored_pack_Z']|deps['factored_pack_inner'],'both offset expressions independent of beta')
 ring=RingDAG();ne=ring.run(new,vars+constants);pull=ring.add(ring.add(ring.val('and__bound_beta'),ne['factored_pack_Z']),ne['factored_pack_inner'],-1);oe=ring.run(rows,vars+constants,{'and__bound_beta':pull})
 need(all(oe[n]==ne[n]for n,o,a,b in new),'all253 computed gates under actual affine pullback without author cuts')
 need(oe['lower_history_product']==ne['lower_history_product']and oe[old['output']]==ne[old['output']],'full comparison and final polynomial identity')
 return rows,new,vars,constants

def upper_bound(rows,vars,constants,child=True):
 actual={n:(o,a,b)for n,o,a,b in rows};d={n:1 for n in vars};d.update({n:0 for n in constants})
 for pref in('geo__','and__'):
  X,a,c,g,H=[pref+x for x in('wn2','R12','R10a','gam','a4m5')]
  ex={pref+'cam2':('*',c,a),pref+'D1':('+',X,pref+'cam2'),pref+'R14':('+',pref+'D1',g),pref+'L15':('*',pref+'R14',pref+'R14'),pref+'a_square':('*',a,a),H:('+',pref+'a4',3),pref+'a4':('*',4,a),g:('*',pref+'ga',H),pref+'A':('+',pref+'a_square',H),pref+'c2':('*',c,c),pref+'Ac2':('*',pref+'A',pref+'c2'),pref+'R15':('-',pref+'L15',pref+'Ac2')}
  need(all(actual[n]==v for n,v in ex.items()),'literal independent main factorization cone '+pref)
 for n,o,a,b in rows:
  da=d[a]if type(a)is str else 0;db=d[b]if type(b)is str else 0
  if n in('geo__R15','and__R15'):
   pref=n[:-3];X,a,c,g,H=[pref+x for x in('wn2','R12','R10a','gam','a4m5')];u=max(d[X],d[g]);d[n]=max(u+max(d[a]+d[c],u),d[H]+2*d[c])
  else:d[n]=da+db if o=='*'else max(da,db)
 expected=FACTOR_DEGREES if child else[14,40,9,168,404,93,24,220,6,76,6,76,4,2,2,3]
 need(d['lower_unit_output']==(982 if child else 1147)and[d[n]for n in FACTORS]==expected,'complete bound with degree-one program parameters')
 return d

# Source premises for a uniform exact leading-form argument, not merely a
# numeric specialization. Compiler numerals are constants; programs remain
# degree-one variables. The native factor leaders are products of nonzero
# factors, and the upper-history factor has a unique Ufinal coefficient.
def uniform_leading_shapes(rows,d):
 D={n:(o,a,b)for n,o,a,b in rows}
 require={
 'Q':('+','modulus',1),'modulus':('*','@fixed:repunit_divisor','load__r'),
 'B':('*','@fixed:recoder_radix','Q'),'Bm1':('-','B',1),
 'duration_multiple':('*','Bm1','duration_quotient'),'duration_J':('+','duration_multiple','program_duration_bound'),
 'repunit_product':('*','Bm1','duration_J'),'repunit_P':('+','repunit_product',1),
 'scale':('*','input_bound','repunit_P'),'joint16B':('*',16,'B'),'fusion_low_q':('*','joint16B','scale'),
 'hist__B__3':('*','hist__height_slack','@fixed:history_radix'),
 'hist__P__10':('+','hist__global_bound','hist__global_sum__14'),
 'hist__P2__51':('*','hist__P__10','hist__P__10'),'hist__P3__78':('*','hist__P2__51','hist__P__10'),
 'hist__P6__80':('*','hist__P3__78','hist__P3__78'),'hist__P7__81':('*','hist__P6__80','hist__P__10'),
 'hist__P9__86':('*','hist__P7__81','hist__P2__51'),'hist__top_history__87':('*','hist__B__3','hist__P9__86'),
 'and__q':('*','fusion_low_q','hist__top_history__87'),
 'hist__range_second_history__56':('*','hist__H_V','hist__P__10'),'hist__range_histories__57':('+','hist__H_U','hist__range_second_history__56'),
 'hist__range_region__82':('*','hist__P7__81','hist__range_histories__57'),
 'hist__common_joined__83':('+','hist__controller_region__79','hist__range_region__82'),
 'hist__joined_Z__96':('+','hist__common_joined__83','hist__unhat_pack__74'),
 'fusion_high_Z':('*','fusion_low_q','hist__joined_Z__96'),'and__F3':('+','fusion_low_F3','fusion_high_Z'),
 'geometry_index':('*','@fixed:repunit_divisor','duration_J'),'geo__geometry_X_bound':('+','geometry_index','geo__bound_beta'),
 'geo__wn2':('*','geo__geometry_X_bound','Q'),
 'hist__U_terminal__40':('*','hist__P__10','hist__Ufinal'),'hist__U_rhs__41':('+','hist__H_U','hist__U_terminal__40'),
 'hist__U_update__36':('*','hist__B__3','hist__linear_constant__168'),'history_upper_unit':('-','hist__U_rhs__41','hist__U_update__36'),
 'hist__P_product__9':('*','hist__Bm1__8','hist__J__7'),'history_global_unit':('-','hist__P__10','hist__P_product__9'),
 'load__prefix_data':('*','program_A','load__r'),'load__data_delta':('*','program_B','z'),'load__data_body':('+','load__prefix_data','load__data_delta'),
 'load__data_counter_scale':('*','load__data_body','Q'),'load__before_tail':('+','load__data_counter_scale','load__counter_frame'),'load__tag_input':('+','load__before_tail','program_E'),
 'hist__V_lhs__39':('+','hist__V_update__38','load__tag_input'),'lower_history_unit':('-','hist__V_rhs__43','hist__V_lhs__39')}
 need(all(D[n]==v for n,v in require.items()),'all actual closed outer leading-form premises')
 need(d['hist__controller_region__79']<d['hist__range_region__82']and d['hist__unhat_pack__74']<d['hist__range_region__82']and d['fusion_low_F3']<d['fusion_high_Z'],'unique positive F3 leading cone')
 need(d['load__counter_frame']<d['load__data_counter_scale']and d['hist__V_rhs__43']<d['load__tag_input']and d['hist__V_update__38']<d['load__tag_input'],'unique lower history degree3 loader cone')
 need(d['and__q']==15 and d['and__F3']==14 and[d['and__'+n]for n in('wn2','R12','R10a')]==[44,60,17],'actual outer/native degree interface')
 # Literal nondependence makes P*Ufinal the unique Ufinal term in the upper
 # history leader, for every admissible compiler coefficient tuple.
 deps={}
 for n,o,a,b in rows:
  deps[n]=set()
  for v in(a,b):
   if type(v)is str:deps[n]|=deps.get(v,{v})
 need('hist__Ufinal'not in deps['hist__P__10']|deps['hist__U_update__36'],'upper history unique free Ufinal monomial')
 return len(require)

def expected_packet_parent(entry,merged,blobs):
 import ast
 p=copy.deepcopy(entry);old=p.pop('ledger');p.pop('source_sha256')
 tree=ast.parse(blobs['binary_tag_parameterized_compressed_compiler.py']);found=[ast.literal_eval(n.value)for n in tree.body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='NUMERALS'for t in n.targets)]
 need(len(found)==1 and sorted(found[0])==FIXED,'all eleven actual compiler numeral recipes')
 fixed=json.loads(blobs['neary_woods_universal_u9_tag_chain.json'])['fixed_recipe']
 p.update(merged=merged,saved_parent_index=15 if merged else 7,comparisons=[['lower_history_product',1]],unit_factors=FACTORS,domains={'parameters':'positive integers; program parameters fixed on valid shifted program slices','auxiliaries':'positive integers'},fixed_numeral_recipes=found[0],fixed_u9_recipe=fixed,historical_parent_ledger=old)
 need(old['normalized_prefixes']==old['positive_scale_prefixes']==['geo__','and__']and old['bound_is_program_E']is merged,'actual selected parent mode and normalized scales')
 need(old['factor_partition']==[list(range(16))]and old['partition_anchor']==0,'actual one-group full factor schedule')
 return p

def verify(root,artifacts):
 blobs=pins(root,PINS);ab=pins(artifacts,AUTHOR);saved=json.loads(ab['neary_woods_universal_tail_quotient253.json']);parents=json.loads(blobs['neary_woods_universal_product_scale253.json'])
 need(saved['source_sha256']==AUTHOR['neary_woods_universal_tail_quotient253.py']and exact(saved['pins'],PINS),'independent author and all parent pins')
 need(len(saved['forms'])==2 and[f['packet']['saved_parent_index']for f in saved['forms']]==[7,15],'exact maintained two-source scope')
 path=Path(artifacts)/'neary_woods_universal_tail_quotient253.py';mod=types.ModuleType('_review_u9_tail_public');mod.__file__=str(path);exec(compile(ab[path.name],str(path),'exec'),mod.__dict__)
 counts=dict(complete_sources=0,whole_graph_identities=0,all_register_identities=0,all_factor_identities=0,paid_live_gates=0,full_coefficient_expansions=0,full_gate_degree_checks=0,numeric_cases=0,rational_cases=0,numeric_register_identities=0,guards=0,copy_checks=0,strict_pin_checks=0,main_expansion_terms=main_identity(),uniform_leading_shape_premises=0)
 rng=random.Random(982253);forms=[]
 for merged,record in zip((False,True),saved['forms']):
  p=record['packet'];entry=parents['canonical_sources'][15 if merged else 7];old=expected_packet_parent(entry,merged,blobs)
  need(exact(mod.canonical_parent(merged=merged,root=root),old),'independent canonical parent packet')
  rows=independent_child(old);need(rows==p['source'],'every literal child source row independently rebuilt')
  oldrows,new,variables,constants=shape(old,rows);deg=upper_bound(new,variables,constants);olddeg=upper_bound(oldrows,variables,constants,False);counts['uniform_leading_shape_premises']+=uniform_leading_shapes(new,deg)
  need(all(exact(p[k],old[k])for k in old if k!='source'),'all unchanged parent metadata and coordinate interfaces')
  need(len(p['parameters'])==(5 if merged else 6)and p['parameters']==['x','program_A','program_B','program_T','program_E']+([]if merged else['program_bound']),'all supplied program parameters explicitly retained')
  need(p['source'][0]==['program_duration_bound','+','program_E'if merged else'program_bound','program_duration_gap'],'literal selected duration layout')
  M,A,_=ledger(new,variables+constants,[p['output']],constants);cm,ca,_=ledger(new[:-1],variables+constants,['lower_history_product'],constants)
  need((M,A,cm,ca)==(132,121,132,120),'full paid source/certificate ledgers')
  want=dict(operations=253,M=132,A=121,certificate_operations=252,certificate_M=132,certificate_A=120,comparisons=1,witnesses=43,supplied_parameters=len(p['parameters']),fixed_numeral_roles=11,all_gates_live=True)
  need(exact(p['ledger'],want)and exact(p['parent_pins'],PINS),'actual ledger and copied provenance')
  wantdegree=dict(degree_upper_bound=982,exact_degree_claimed=False,supplied_coordinate_degree=1,fixed_numeral_degree=0,factor_degree_bounds=dict(zip(FACTORS,FACTOR_DEGREES)),joint_ports={n:deg[n]for n in('and__q','and__F3','factored_pack_Z','factored_pack_inner','and__wn2','and__sn2','and__R12','and__R10a')},main_norm_cancellations=['geo__R15','and__R15'])
  need(exact(p['degree'],wantdegree),'truthful upper-only symbolic-program degree metadata')
  wantmap={'signed_pullback':'and__bound_beta_old=and__bound_beta+factored_pack_Z-factored_pack_inner','positive_forward_on_parent_zeros':True,'positive_inverse_only_after_native_recovery':True,'same_coordinate_polynomial_identity':False,'all_value_signed_graph_identity':True,'positive_zero_bijection_on_valid_shifted_program_slices':True,'normalized_to_ordinary_lemma_conversion':'i_ordinary=Delta*i_normalized; not a coordinate bijection claim','X_gt_r_assumed_before_typing':False}
  need(exact(p['tail_projection'],wantmap)and p['source_scope']=='Exactly two saved normalized and positive-scale layouts7/15; one actual U9 program recipe; no partition census. Computation time remains unbounded.','active map/theorem scope metadata')
  D={n:(o,a,b)for n,o,a,b in new}
  def factors(n):
   if n in FACTORS:return[n]
   need(n in D and D[n][0]=='*','literal unsquared product spine');return factors(D[n][1])+factors(D[n][2])
  need(sorted(factors('lower_history_product'))==sorted(FACTORS),'exact all sixteen factor occurrences')
  counts['all_register_identities']+=253;counts['all_factor_identities']+=16;counts['whole_graph_identities']+=1;counts['paid_live_gates']+=253;counts['complete_sources']+=1
  coefficient_cases=[]
  for case,prime in enumerate((1000000007,1000000009)):
   weights={n:i+2+case for i,n in enumerate(sorted(variables))};fixed={n:i+2+case for i,n in enumerate(constants)}
   polys=full_coefficients({'source':new},weights,prime,fixed);output=polys[p['output']]
   need(len(output)-1==982 and output[-1]!=0,'full coefficient polynomial attains982 in diagnostic specialization')
   need(all(len(polys[n])-1==deg[n]for n,o,a,b in new),'all literal coefficient degrees attain independent symbolic upper bounds')
   need([len(polys[n])-1 for n in FACTORS]==FACTOR_DEGREES,'all actual unit polynomial degrees')
   coefficient_cases.append(dict(modulus=prime,weights=weights,fixed_diagnostic_values={n[7:]:v for n,v in fixed.items()},degree=len(output)-1,leading_coefficient=output[-1],coefficient_sha256=sha(json.dumps(output,separators=(',',':')).encode())))
   counts['full_coefficient_expansions']+=1;counts['full_gate_degree_checks']+=253
  need(exact(mod.build(merged=merged,root=root),p)and exact(mod.rewrite(old,root=root),p)and exact(mod.checked(p,root=root),p),'actual public canonical APIs')
  need(mod.polynomial_source(p,root=root)==(p['source'],p['output'])and exact(mod.degree_bound(p,root=root),p['degree']),'literal public polynomial and degree exports')
  for case in range(20):
   v={n:rng.randrange(1,4)if case<6 else rng.randrange(-2,4)for n in variables};c={n:rng.randrange(1,4)if case<6 else rng.randrange(-2,4)for n in FIXED}
   if case>=16:v={n:Fraction(x,3)for n,x in v.items()};c={n:Fraction(x,3)for n,x in c.items()};counts['rational_cases']+=1
   allv=dict(v);allv.update({'@fixed:'+n:x for n,x in c.items()});ne=numeric(new,allv);pv=dict(v);pv['and__bound_beta']+=ne['factored_pack_Z']-ne['factored_pack_inner'];allold=dict(pv);allold.update({'@fixed:'+n:x for n,x in c.items()});oe=numeric(oldrows,allold)
   need(all(ne[n]==oe[n]for n,o,a,b in new),'every exact numeric register after signed pullback');counts['numeric_register_identities']+=253;counts['numeric_cases']+=1
   product=1
   for name in FACTORS:product*=ne[name]
   need(product-1==ne[p['output']],'complete product-minus-one finalizer numeric identity')
   if case<16:need(mod.evaluate(p,v,c,signed=case>=6,root=root)==ne[p['output']]and exact(mod.integer_pullback(p,v,c,root=root),pv),'actual integer evaluator and diagnostic numeral interface')
  v={n:1 for n in variables};c={n:1 for n in FIXED};allv=dict(v);allv.update({'@fixed:'+n:x for n,x in c.items()});ne=numeric(new,allv);inv=1+ne['factored_pack_Z']-ne['factored_pack_inner']
  need(inv<0 and ne[p['output']]!=0,'off-zero signed inverse diagnostic is not a false-zero claim')
  def reject(fn):
   try:fn()
   except(ValueError,TypeError,KeyError,FileNotFoundError):counts['guards']+=1
   else:raise ValueError('malformed call accepted')
  for bad in(None,{},dict(p,merged=1),dict(p,degree={}),dict(p,source=p['source'][:-1])):reject(lambda bad=bad:mod.checked(bad,root=root))
  for flag in(None,1,0,'yes',1.0):reject(lambda flag=flag:mod.build(merged=flag,root=root))
  for parent_mode in(False,True):
   base=old if parent_mode else p;mutations=[]
   z=copy.deepcopy(base);z['source'][7][2]=16.0;mutations.append(z)
   z=copy.deepcopy(base);z['source'][0][2]='program_T';mutations.append(z)
   z=copy.deepcopy(base);z['comparisons'][0][1]=True;mutations.append(z)
   z=copy.deepcopy(base);z['fixed_numeral_recipes']['history_radix']='1';mutations.append(z)
   z=copy.deepcopy(base);z['source'][206][2]='factored_pack_Z'if parent_mode else'factored_pack_inner';mutations.append(z)
   for z in mutations:reject(lambda z=z,parent_mode=parent_mode:mod.rewrite(z,root=root)if parent_mode else mod.checked(z,root=root))
  for val in(True,1.0,Fraction(1,1),0,-1):reject(lambda val=val:mod.evaluate(p,dict(v,x=val),c,root=root))
  for nums in({},dict(c,extra=1),dict(c,history_radix=True),dict(c,history_radix=0),dict(c,history_radix=1.0)):reject(lambda nums=nums:mod.evaluate(p,v,nums,root=root))
  for signed in(1,None,'yes'):reject(lambda signed=signed:mod.evaluate(p,v,c,signed=signed,root=root))
  for maker in(lambda:mod.build(merged=merged,root=root),lambda:mod.rewrite(old,root=root),lambda:mod.checked(p,root=root)):
   for key in('source','parent_pins','degree','fixed_numeral_recipes','fixed_u9_recipe','tail_projection'):
    z=maker();z[key].clear();need(exact(mod.build(merged=merged,root=root),p),'fresh packet deep copies');counts['copy_checks']+=1
  src,out=mod.polynomial_source(p,root=root);src.clear();need(mod.polynomial_source(p,root=root)[0]==p['source'],'polynomial source copy');counts['copy_checks']+=1
  dg=mod.degree_bound(p,root=root);dg.clear();need(exact(mod.degree_bound(p,root=root),p['degree']),'degree copy');counts['copy_checks']+=1
  forms.append(dict(saved_parent_index=p['saved_parent_index'],merged=merged,ledger=want,degree_metadata=wantdegree,independent_exact_total_degree=982,independent_exact_degree_scope='All supplied program parameters and witnesses variable; fixed actual compiler numeral recipes degreezero; not a fixed-program specialization claim',coefficient_cases=coefficient_cases,offzero_signed_inverse_negative=True))
 # Every public entrypoint authenticates every parent/proof path on each call.
 p=saved['forms'][-1]['packet'];old=expected_packet_parent(parents['canonical_sources'][15],True,blobs);v={n:1 for n in p['parameters']+p['auxiliaries']};c={n:1 for n in FIXED}
 entries=[lambda r:mod.canonical_parent(root=r),lambda r:mod.build(root=r),lambda r:mod.rewrite(old,root=r),lambda r:mod.checked(p,root=r),lambda r:mod.polynomial_source(p,root=r),lambda r:mod.degree_bound(p,root=r),lambda r:mod.evaluate(p,v,c,root=r),lambda r:mod.integer_pullback(p,v,c,root=r)]
 with tempfile.TemporaryDirectory(prefix='u9_tail_source_review_')as td:
  rr=Path(td)/'Papers'/'research-wip'/'native-stream-queue';rr.mkdir(parents=True)
  for name,b in blobs.items():q=rr/name;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
  need(exact(mod.build(root=rr),p),'relocated source reconstruction')
  for name,b in blobs.items():
   q=rr/name;q.write_bytes(b+b'\n')
   for entry in entries:reject(lambda entry=entry:entry(rr));counts['strict_pin_checks']+=1
   q.write_bytes(b)
 proc=subprocess.run([sys.executable,'-O',str(path),'--root',str(root)],capture_output=True,text=True);need(proc.returncode!=0 and'Run without -O'in proc.stderr,'optimized mode rejected');counts['guards']+=1
 return dict(schema='independent-u9-tail-source-review-v1',status='PASS',review_source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTHOR,parent_pins=PINS,counts=counts,forms=forms,scope={'maintained_claim':'two complete253 sources; upper982, exact_degree_claimed=False','program_parameters':'all supplied program parameters remain degree-one polynomial variables','compiler_numerals':'eleven fixed recipe ports degreezero; diagnostic evaluations do not instantiate their recipes','independent_exact_degree':'982 uniformly in actual fixed compiler numeral coefficients, with all supplied program parameters variable; proof in note, supported by44 literal outer shape premises per source and complete coefficient diagnostics','native_positive_zero_proof':'separate mathematical review; no new bootstrap or full Pell materialization here','historical_modules_imported':False,'author_verifier_called':False})

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',required=True);ap.add_argument('--artifacts',default=str(Path(__file__).resolve().parent));ap.add_argument('--output');ap.add_argument('--expect');args=ap.parse_args();r=verify(args.root,args.artifacts)
 if args.expect:need(exact(r,json.loads(Path(args.expect).read_text())),'exact typed review receipt')
 if args.output:Path(args.output).write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':'PASS','counts':r['counts'],'forms':[(f['saved_parent_index'],f['ledger']['operations'],f['degree_metadata']['degree_upper_bound'])for f in r['forms']]},sort_keys=True))
if __name__=='__main__':main()
