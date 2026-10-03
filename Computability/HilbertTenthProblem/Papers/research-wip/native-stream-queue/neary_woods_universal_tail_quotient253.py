#!/usr/bin/env python3
"""Two saved complete U9 sources with a smaller private native quotient offset.
No historical builders imported. Fixed numeral recipes remain literal leaves.
"""
import argparse, ast, copy, hashlib, json, random
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__: raise RuntimeError('Run without -O')
PINS = {'neary_woods_universal_product_scale253.py': 'eb3e8f41f79f69199bd7b620a2b8908e60915b3976898def9d59c25d92a4675e', 'neary_woods_universal_product_scale253.json': 'a32b58aee2baf3d6d1a66489784f9cc9f5ab2bac296b9a7eb0a116785a3eef1b', 'neary_woods_universal_product_scale253.md': '9b3b0566dd1365d9acf4b97b6b290b951d56eb51392e85e48f06f83b1604434f', 'group_projective_tail_quotient_shift.py': '08248ad763113a6a2e60168edfd058b92be4e14b2f7932fa1be66eb406a70610', 'group_projective_tail_quotient_shift.json': 'a422e7a65df26e626f3c36f97a53a68805b86806be3dc35d35e7d49a17b80b27', 'group_projective_tail_quotient_shift.md': 'a1e1e67df618f6f809c2e85a409509b288337f62cd1af35cfc6ca950e0efa92a', 'neary_woods_universal_native_bound254.md': '93b723d6cbbe42e07a9e57979105cffa08f332f4e8d028e5b0aa34890e189952', 'native_binary_positive_scale.md': 'd958feffa5d82ede3096d8c792fbf861385f2c7c011057c587663ead4ad2ce97', 'neary_woods_universal_history_units260.md': '73d3787dcc10acc037f80699ec3f8bde1fb721613abac5ce489762aab339057c', 'neary_woods_universal_initial_bound254.md': '9e1a0fd5559dc72420a5123eb4f67753576f7b06d93aff6b7b650cd40dba1f90', 'neary_woods_universal_history_scale257.md': 'dcc467b4b00a013c315856a271307459b694b69d4bd2a66c925312a042247e42', 'neary_woods_universal_joint_and_coupled.md': '02333114dd0cc4396d0a82098e71fde02cc76654c5b5751041f1237732d77868', 'binary_tag_parameterized_compressed_compiler.py': '13da39c3292f8e19f7881f4543fa704c42edec12f29bd10b06f2df555385c0df', 'neary_woods_universal_u9_tag_chain.py': '36794dccbad7de48eebcc10ff95311a451205828b1e13f2e2415997246b5d1b8', 'neary_woods_universal_u9_tag_chain.json': 'b4d78b1be42f6e8c16180311ce371c486d75f9de646b4d78edaf0bcd2491b727', 'native_controller_binary_selector56.md': '97fcdc7188f968f2ac3e315249b0e0a15dcc787c10451924ad3f2551c8bb376c', '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b', '../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md': '47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b'}
FACTORS = ('geo__R15','geo__P17','geo__first_unit','and__R15','and__P17','and__first_unit','geo__f_square_minus_one','and__f_square_minus_one','geo__index_unit','and__index_unit','geo__linear_unit','and__linear_unit','mask_repunit_unit','history_upper_unit','history_global_unit','lower_history_unit')
BETA='and__bound_beta'; CUT='and__bs_X_bound'; Z='factored_pack_Z'; S='factored_pack_inner'

def need(c,m):
 if not c: raise ValueError(m)
def sha(b): return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b): return False
 if type(a)is dict: return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)in(list,tuple): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def stable(v): return json.dumps(v,sort_keys=True,separators=(',',':'))
def authenticate(root):
 root=Path(__file__).resolve().parent if root is None else Path(root)
 for n,h in PINS.items(): need(sha((root/n).read_bytes())==h,'source pin: '+n)
 return root

def canonical_parent(*,merged=True,root=None):
 need(type(merged)is bool,'exact merged flag');root=authenticate(root)
 data=json.loads((root/'neary_woods_universal_product_scale253.json').read_text())
 entry=copy.deepcopy(data['canonical_sources'][15 if merged else 7]);old=entry.pop('ledger');entry.pop('source_sha256')
 need(old['normalized_prefixes']==old['positive_scale_prefixes']==['geo__','and__'] and old['bound_is_program_E']is merged,'canonical normalized source')
 need(old['factor_partition']==[list(range(16))] and old['partition_anchor']==0,'actual one-group product')
 tree=ast.parse((root/'binary_tag_parameterized_compressed_compiler.py').read_text())
 recipes=[ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='NUMERALS' for t in n.targets)]
 need(len(recipes)==1 and len(recipes[0])==11,'actual fixed numeral recipes')
 fixed=json.loads((root/'neary_woods_universal_u9_tag_chain.json').read_text())['fixed_recipe']
 entry.update(merged=merged,saved_parent_index=15 if merged else 7,comparisons=[['lower_history_product',1]],unit_factors=list(FACTORS),domains={'parameters':'positive integers; program parameters fixed on valid shifted program slices','auxiliaries':'positive integers'},fixed_numeral_recipes=recipes[0],fixed_u9_recipe=fixed,historical_parent_ledger=old)
 return entry

def literal_guard(p):
 rows=p['source'];d={n:(o,a,b) for n,o,a,b in rows}
 expected={CUT:('+',S,BETA),Z:('*','factored_pack_q_minus_one','and__F3'),S:('+','factored_pack_A_plus_one','factored_pack_scaled_B'),'factored_pack_scaled_B':('*','factored_pack_q_plus_one','factored_pack_B'),'factored_pack_B':('+','and__padded_B',Z),'factored_pack_q_minus_one':('-','and__q',1),'factored_pack_q_plus_one':('+','and__q',1),'and__bs_packed':('*','factored_pack_q_minus_one',S),'and__wn2':('*',CUT,'and__q'),'and__normalized_strong_Q':('*','and__A','and__ic22'),'and__R16':('*','and__A','and__normalized_strong_Q'),'and__f_square_minus_one':('-','and__L16','and__normalized_strong_Q')}
 need(all(d.get(n)==v for n,v in expected.items()),'literal packing/normalized source')
 need([n for n,o,a,b in rows if BETA in(a,b)]==[CUT],'private supplied quotient')
 need([n for n,o,a,b in rows if CUT in(a,b)]==['and__wn2'],'private quotient sum')
 need(rows[-1]==['lower_unit_output','-','lower_history_product',1],'complete paid finalizer')
 def flatten(n):
  if n in FACTORS: return [n]
  need(n in d and d[n][0]=='*','literal factor product');return flatten(d[n][1])+flatten(d[n][2])
 need(Counter(flatten('lower_history_product'))==Counter(FACTORS),'all sixteen actual factors')
 return d

def ledger(p):
 known=set(p['parameters']+p['auxiliaries']);deps={};counts=Counter();fixed=set()
 need(len(known)==len(p['parameters'])+len(p['auxiliaries']),'unique supplied coordinates')
 def operand(v):
  if type(v)is int:return True
  if type(v)is str:return v in known
  if type(v)is dict and set(v)=={'fixed_numeral'} and type(v['fixed_numeral'])is str and v['fixed_numeral'] in p['fixed_numeral_recipes']:
   fixed.add(v['fixed_numeral']);return True
  return False
 for n,o,a,b in p['source']:
  need(type(n)is str and n not in known and o in('+','-','*') and operand(a) and operand(b),'closed typed paid DAG')
  known.add(n);deps[n]=(a,b);counts['M' if o=='*' else 'A']+=1
 todo=[p['output']];live=set();free=set()
 while todo:
  n=todo.pop()
  if type(n)is not str:continue
  if n not in deps:free.add(n);continue
  if n not in live:live.add(n);todo.extend(deps[n])
 need(live==set(deps) and free==set(p['parameters']+p['auxiliaries']),'all gates/coordinates live')
 need(fixed==set(p['fixed_numeral_recipes']),'all fixed numeral roles retained')
 return dict(operations=len(deps),M=counts['M'],A=counts['A'],certificate_operations=len(deps)-1,certificate_M=counts['M'],certificate_A=counts['A']-1,comparisons=1,witnesses=len(p['auxiliaries']),supplied_parameters=len(p['parameters']),fixed_numeral_roles=len(fixed),all_gates_live=True)

def degree_internal(p):
 d={n:1 for n in p['parameters']+p['auxiliaries']};rows=p['source'];actual={n:(o,a,b) for n,o,a,b in rows}
 for pre in ('geo__','and__'):
  X,A,c,G,H=[pre+s for s in('wn2','R12','R10a','gam','a4m5')]
  expected={pre+'R15':('-',pre+'L15',pre+'Ac2'),pre+'L15':('*',pre+'R14',pre+'R14'),pre+'R14':('+',pre+'D1',G),pre+'D1':('+',X,pre+'cam2'),pre+'cam2':('*',c,A),pre+'A':('+',pre+'a_square',H),pre+'a_square':('*',A,A),H:('+',pre+'a4',3),pre+'a4':('*',4,A),G:('*',pre+'ga',H),pre+'Ac2':('*',pre+'A',pre+'c2'),pre+'c2':('*',c,c)}
  need(all(actual.get(n)==v for n,v in expected.items()),'main norm expansion '+pre)
 at=lambda v:d[v] if type(v)is str else 0
 for n,o,a,b in rows:
  if n in('geo__R15','and__R15'):
   pre=n[:-3];X,A,c,G,H=[d[pre+s] for s in('wn2','R12','R10a','gam','a4m5')]
   # Exact polynomial expansion X²+2Xac+2XG+2acG+G²-Hc²;
   # this cancellation holds at every tuple, not only at native zeros.
   d[n]=max(2*X,X+A+c,X+G,A+c+G,2*G,H+2*c)
  else:d[n]=at(a)+at(b) if o=='*' else max(at(a),at(b))
 return dict(degree_upper_bound=d[p['output']],exact_degree_claimed=False,supplied_coordinate_degree=1,fixed_numeral_degree=0,factor_degree_bounds={n:d[n] for n in FACTORS},joint_ports={n:d[n] for n in('and__q','and__F3',Z,S,'and__wn2','and__sn2','and__R12','and__R10a')},main_norm_cancellations=['geo__R15','and__R15'])

def rewrite(parent,*,root=None):
 need(type(parent)is dict and type(parent.get('merged'))is bool,'parent descriptor')
 need(exact(parent,canonical_parent(merged=parent['merged'],root=root)),'exact canonical parent')
 literal_guard(parent);p=copy.deepcopy(parent)
 p['source']=[[n,o,Z,b] if n==CUT else [n,o,a,b] for n,o,a,b in p['source']]
 p['parent_pins']=copy.deepcopy(PINS);p['ledger']=ledger(p);p['degree']=degree_internal(p)
 p['tail_projection']={'signed_pullback':'and__bound_beta_old=and__bound_beta+factored_pack_Z-factored_pack_inner','positive_forward_on_parent_zeros':True,'positive_inverse_only_after_native_recovery':True,'same_coordinate_polynomial_identity':False,'all_value_signed_graph_identity':True,'positive_zero_bijection_on_valid_shifted_program_slices':True,'normalized_to_ordinary_lemma_conversion':'i_ordinary=Delta*i_normalized; not a coordinate bijection claim','X_gt_r_assumed_before_typing':False}
 p['source_scope']='Exactly two saved normalized and positive-scale layouts7/15; one actual U9 program recipe; no partition census. Computation time remains unbounded.'
 need(p['ledger']['operations']==253 and p['ledger']['M']==132 and p['ledger']['A']==121 and p['ledger']['witnesses']==43,'complete current ledger')
 need(p['degree']['degree_upper_bound']==982 and parent['historical_parent_ledger']['polynomial']['degree_upper_bound']==1147,'current/parent degree bounds')
 return p

def build(*,merged=True,root=None):return rewrite(canonical_parent(merged=merged,root=root),root=root)
def checked(p,*,root=None):
 need(type(p)is dict and type(p.get('merged'))is bool,'child descriptor')
 expected=build(merged=p['merged'],root=root);need(exact(p,expected),'canonical child');return expected
def polynomial_source(p,*,root=None):
 p=checked(p,root=root);return copy.deepcopy(p['source']),p['output']
def degree_bound(p,*,root=None):return checked(p,root=root)['degree']
def execute(rows,values,numerals):
 e=dict(values)
 def at(v):return e[v] if type(v)is str else numerals[v['fixed_numeral']] if type(v)is dict else v
 for n,o,a,b in rows:
  a,b=at(a),at(b);e[n]=a*b if o=='*' else a+b if o=='+' else a-b
 return e
def inputs(p,v,c,signed):
 need(type(signed)is bool and type(v)is dict and set(v)==set(p['parameters']+p['auxiliaries']),'exact values')
 need(all(type(z)is int for z in v.values()),'exact supplied integers')
 need(type(c)is dict and set(c)==set(p['fixed_numeral_recipes']) and all(type(z)is int for z in c.values()),'exact diagnostic numeral values')
 if not signed:need(min(v.values())>0 and min(c.values())>0,'positive values')
def evaluate(p,values,numerals,*,signed=False,root=None):
 p=checked(p,root=root);inputs(p,values,numerals,signed);return execute(p['source'],values,numerals)[p['output']]
def integer_pullback(p,values,numerals,*,root=None):
 p=checked(p,root=root);inputs(p,values,numerals,True);e=execute(p['source'],values,numerals);v=dict(values);v[BETA]+=e[Z]-e[S];return v

def whole_graph_proof(parent,p):
 changed=[[a,b] for a,b in zip(parent['source'],p['source']) if a!=b]
 need(len(parent['source'])==len(p['source'])==253 and changed==[[[CUT,'+',S,BETA],[CUT,'+',Z,BETA]]],'literal sole operand edit')
 # (beta+Z-S)+S=beta+Z in independent formal coordinates.
 affine=(1,1,-1);old=tuple(x+y for x,y in zip(affine,(0,0,1)));need(old==(1,1,0),'formal local identity')
 table={}
 def intern(k):
  if k not in table:table[k]=len(table)
  return table[k]
 def graph(rows):
  e={n:intern(('supplied',n)) for n in p['parameters']+p['auxiliaries']}
  at=lambda v:e[v] if type(v)is str else intern(('literal',stable(v)))
  for n,o,a,b in rows:e[n]=intern(('proved_quotient_cut',)) if n==CUT else intern((o,at(a),at(b)))
  return e
 a,b=graph(parent['source']),graph(p['source'])
 need(all(a[n]==b[n] for n,o,x,y in p['source']),'all complete graph identities under affine cut')
 need(all(a[n]==b[n] for n in FACTORS) and a[p['output']]==b[p['output']],'all factors and full output')
 return dict(changed_rows=changed,whole_register_identities=253,factor_identities=16,full_polynomial_identity_under_signed_pullback=True,complete_finalizer_retained=True)

def verify(root):
 counts=Counter();forms=[];rng=random.Random(253982)
 for merged in(False,True):
  old=canonical_parent(merged=merged,root=root);p=build(merged=merged,root=root);proof=whole_graph_proof(old,p)
  need(degree_internal(old)['degree_upper_bound']==1147,'independent old upper bound')
  names=p['parameters']+p['auxiliaries'];fixed=list(p['fixed_numeral_recipes'])
  for i in range(24):
   v={n:rng.randrange(1,4) if i<8 else rng.randrange(-2,3) for n in names};c={n:rng.randrange(1,4) if i<8 else rng.randrange(-2,3) for n in fixed}
   if i>=20:v={n:Fraction(k,3) for n,k in v.items()};c={n:Fraction(k,3) for n,k in c.items()};counts['rational_identities']+=1
   b=execute(p['source'],v,c);w=dict(v);w[BETA]+=b[Z]-b[S];a=execute(old['source'],w,c)
   need(all(a[n]==b[n] for n,o,x,y in p['source']),'all register numeric identities');counts['complete_numeric_identities']+=1
   need(b[p['output']]==__import__('functools').reduce(lambda x,y:x*y,(b[n] for n in FACTORS),1)-1,'literal complete product finalizer');counts['factor_numeric_identities']+=16
  v={n:1 for n in names};c={n:1 for n in fixed};e=execute(p['source'],v,c);pv=integer_pullback(p,v,c,root=root)
  need(pv[BETA]==1+e[Z]-e[S]<0 and e[p['output']]!=0,'formal inverse not unconditionally positive')
  for bad in(None,{},dict(p,degree={}),dict(p,merged=1)):
   try:checked(bad,root=root)
   except (ValueError,TypeError):counts['rejections']+=1
   else:raise ValueError('bad child accepted')
  for bad in(1,0,None,'true'):
   try:build(merged=bad,root=root)
   except ValueError:counts['rejections']+=1
   else:raise ValueError('bad mode accepted')
  for key in('parent_pins','source','fixed_numeral_recipes','degree'):
   q=build(merged=merged,root=root);q[key].clear();need(exact(build(merged=merged,root=root),p),'defensive copy');counts['copy_checks']+=1
  forms.append(dict(packet=p,whole_graph_proof=proof,offzero_signed_boundary={'all_supplied_and_numerals':1,'restored_beta':pv[BETA],'child_nonzero':True}))
 # Positive padded fields, with nondyadic scales allowed before native typing.
 for _ in range(384):
  fs=[b+16*rng.randrange(32) for b in(1,4,2,8)];q=sum(fs)+1;r=sum(f*q**i for i,f in enumerate(fs));Z0=(q-1)*fs[3];A=fs[1]+fs[3];B=fs[2]+fs[3];s=A+1+(q+1)*(B+Z0)
  X=q*(rng.randrange(1,5)+Z0);Y=q*(2*rng.randrange(1,5)+1)
  need(r==(q-1)*s and s>Z0>0 and r<q**3*(fs[3]+1),'source packing')
  need(X*Y>2*r+3 and Y*(X+1)>2*r+3 and X>=16,'bootstrap without X>r');counts['pretyping_fields']+=1
 for t in range(4,11):
  q=1<<t
  for _ in range(16):
   total=q//16-1;cuts=sorted([0,total]+[rng.randrange(total+1) for j in range(3)]);fs=[b+16*(v-u) for b,u,v in zip((1,4,2,8),cuts,cuts[1:])];r=sum(f*q**i for i,f in enumerate(fs));s=r//(q-1)
   need(sum(fs)==q-1 and r%16==1 and r.bit_count()>=t and (r-2).bit_count()>=t+2,'population sign exclusion')
   need(q<r and s<r and 2*r+1-t>=r+1,'canonical inverse exponential margin');counts['population_inverse_cases']+=1
 # Local normalized-to-ordinary polynomial identities, independent of zeros.
 for a in range(1,7):
  delta=(a+2)**2-1
  for i in range(1,5):
   c=2*i+1;f=a+i;rho=i*c*c;ns=f*f-delta*rho*rho
   need((delta*rho)**2-delta*(f*f-1)==-delta*(ns-1),'ordinary strong consequence')
   need(delta*(delta*rho*rho)==(delta*rho)**2,'actual auxiliary coefficient');counts['normalization_identities']+=1
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),pins=copy.deepcopy(PINS),forms=forms,counts=dict(counts),scope='Two actual saved normalized/scaled U9 complete sources only; upper982, no exact-degree claim; full signed polynomial map and positive-zero bijection on inherited valid shifted program/input slices. Diagnostic numeral evaluations do not materialize compiler constants or full native zeros. No historical builders or partition search.')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);args=ap.parse_args();r=verify(args.root)
 if args.expect:need(exact(r,json.loads(args.expect.read_text())),'exact saved receipt')
 if args.output:args.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':r['status'],'counts':r['counts'],'forms':[(x['packet']['saved_parent_index'],x['packet']['ledger']['operations'],x['packet']['degree']['degree_upper_bound']) for x in r['forms']]}))
if __name__=='__main__':main()
