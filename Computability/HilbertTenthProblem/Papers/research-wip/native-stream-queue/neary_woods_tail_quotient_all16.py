#!/usr/bin/env python3
"""Bounded all16 saved U9 quotient-offset transfer; no historical imports.
Eight eligible native bases, each at two duration interfaces. CLI receipt only.
"""
import argparse,ast,copy,hashlib,json,random
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'neary_woods_universal_product_scale253.py': 'eb3e8f41f79f69199bd7b620a2b8908e60915b3976898def9d59c25d92a4675e', 'neary_woods_universal_product_scale253.json': 'a32b58aee2baf3d6d1a66489784f9cc9f5ab2bac296b9a7eb0a116785a3eef1b', 'neary_woods_universal_product_scale253.md': '9b3b0566dd1365d9acf4b97b6b290b951d56eb51392e85e48f06f83b1604434f', 'group_projective_tail_quotient_shift.py': '08248ad763113a6a2e60168edfd058b92be4e14b2f7932fa1be66eb406a70610', 'group_projective_tail_quotient_shift.json': 'a422e7a65df26e626f3c36f97a53a68805b86806be3dc35d35e7d49a17b80b27', 'group_projective_tail_quotient_shift.md': 'a1e1e67df618f6f809c2e85a409509b288337f62cd1af35cfc6ca950e0efa92a', 'neary_woods_universal_native_bound254.md': '93b723d6cbbe42e07a9e57979105cffa08f332f4e8d028e5b0aa34890e189952', 'native_binary_positive_scale.md': 'd958feffa5d82ede3096d8c792fbf861385f2c7c011057c587663ead4ad2ce97', 'neary_woods_universal_history_units260.md': '73d3787dcc10acc037f80699ec3f8bde1fb721613abac5ce489762aab339057c', 'neary_woods_universal_initial_bound254.md': '9e1a0fd5559dc72420a5123eb4f67753576f7b06d93aff6b7b650cd40dba1f90', 'neary_woods_universal_history_scale257.md': 'dcc467b4b00a013c315856a271307459b694b69d4bd2a66c925312a042247e42', 'neary_woods_universal_joint_and_coupled.md': '02333114dd0cc4396d0a82098e71fde02cc76654c5b5751041f1237732d77868', 'binary_tag_parameterized_compressed_compiler.py': '13da39c3292f8e19f7881f4543fa704c42edec12f29bd10b06f2df555385c0df', 'neary_woods_universal_u9_tag_chain.py': '36794dccbad7de48eebcc10ff95311a451205828b1e13f2e2415997246b5d1b8', 'neary_woods_universal_u9_tag_chain.json': 'b4d78b1be42f6e8c16180311ce371c486d75f9de646b4d78edaf0bcd2491b727', 'native_controller_binary_selector56.md': '97fcdc7188f968f2ac3e315249b0e0a15dcc787c10451924ad3f2551c8bb376c', '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b', '../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md': '47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b', 'neary_woods_universal_tail_quotient253.py': '291b3e22c7d1f8db99cb55c3f2e3bc6e83f92e377d44028bf8e56f1c39d7cf50', 'neary_woods_universal_tail_quotient253.json': '48d604caf52af6cc6e37f77614787b1a02a549b03c1f5acdb53a5a7277c7504f', 'neary_woods_universal_tail_quotient253.md': '328b9a3d62a989f78cd3c7b388eba01800a9d92e7cb8df6ac58184df9982653b', 'review_neary_woods_tail_quotient_math.py': 'c2d8d1c5dfaa7e8dba42fa579e22f8b7f591ad3e27faf0ac73a02e79dc36c22b', 'review_neary_woods_tail_quotient_math.json': 'a4628a89462a1073be7c50c4aa5b119c66e80b7e5cdb6803be19c16c6839e8f3', 'review_neary_woods_tail_quotient_math.md': '4efffe5d793992c4e2fc3dc9112482cda55780ab7746b2d5e98d0b3275eedda5'}
OLD_DEGREES=[960,967,1002,1013,1122,1129,1140,1147]
NEW_DEGREES=[795,802,837,848,957,964,975,982]
OPS=[259,256,258,255,258,255,257,253]
MULS=[132,131,133,132,133,132,134,132]
BETA='and__bound_beta';CUT='and__bs_X_bound';Z='factored_pack_Z';S='factored_pack_inner'
BASE_FACTORS=['geo__R15','geo__P17','geo__first_unit','and__R15','and__P17','and__first_unit']
TAIL_FACTORS=['geo__index_unit','and__index_unit','geo__linear_unit','and__linear_unit','mask_repunit_unit','history_upper_unit','history_global_unit','lower_history_unit']
def need(c,m):
 if not c:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)in(list,tuple):return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def stable(v):return json.dumps(v,sort_keys=True,separators=(',',':'))
def authenticate(root):
 root=Path(root)
 for name,digest in PINS.items():need(sha((root/name).read_bytes())==digest,'pin '+name)
 return root

def inventory(entry,index):
 need(type(index)is int and 0<=index<16,'saved index')
 rows=entry['source'];d={n:(o,a,b)for n,o,a,b in rows};old=entry['ledger'];base=index%8
 need(len(rows)==OPS[base]and len(entry['auxiliaries'])==(43 if base%2 else 44),'saved whole source and coordinates')
 normalized=[p for p in('geo__','and__')if p+'normalized_strong_Q'in d]
 expected_normalized=[p for j,p in enumerate(('geo__','and__'))if base&(2<<j)]
 need(normalized==expected_normalized==old['normalized_prefixes'],'actual normalized modes')
 scaled=['and__']
 if d['geo__wn2']==('*','geo__geometry_X_bound','Q'):scaled.insert(0,'geo__')
 else:need(d['geo__wn2']==('*','geo__w','Q'),'literal unprojected geometry X')
 need(scaled==(['geo__','and__']if base%2 else['and__'])==old['positive_scale_prefixes'],'actual scale modes')
 expected_params=['x','program_A','program_B','program_T','program_E']+(['program_bound']if index<8 else[])
 need(entry['parameters']==expected_params and old['bound_is_program_E']is(index>=8),'actual duration interface')
 need(d['program_duration_bound']==('+','program_E'if index>=8 else'program_bound','program_duration_gap'),'paid duration gap')
 factors=BASE_FACTORS+[p+'f_square_minus_one'for p in normalized]+TAIL_FACTORS
 ordinary=[]
 for pre in('geo__','and__'):
  if pre in normalized:
   need(d[pre+'normalized_strong_Q']==('*',pre+'A',pre+'ic22')and d[pre+'R16']==('*',pre+'A',pre+'normalized_strong_Q')and d[pre+'f_square_minus_one']==('-',pre+'L16',pre+'normalized_strong_Q'),'actual normalized coefficient')
  else:
   need(d[pre+'R16']==('*',pre+'A',pre+'f_square_minus_one')and d[pre+'f_square_minus_one']==('-',pre+'L16',1),'actual ordinary coefficient')
   ordinary.append([pre+'ic22',pre+'R16'])
  if pre=='geo__'and pre not in scaled:ordinary.append(['geo__geometry_X_bound','geo__wn2'])
 actual_ordinary=[[a,b]for n,o,a,b in rows if n.startswith('loader_residual_')]
 need(actual_ordinary==ordinary,'complete actual ordinary constraints, in order')
 def flatten(n):
  if n in factors:return[n]
  need(type(n)is str and n in d and d[n][0]=='*','literal complete factor product')
  return flatten(d[n][1])+flatten(d[n][2])
 need(Counter(flatten('lower_history_product'))==Counter(factors),'all retained factor occurrences')
 need(list(old['degree']['factor_degree_bounds'])==factors,'parent factor metadata matches literal product')
 need(old['factor_partition']==[list(range(len(factors)))]and old['partition_anchor']==0,'saved single anchor only')
 start=next(i for i,row in enumerate(rows)if row[0].startswith('loader_residual_')or row[0]=='lower_unit_output')
 expected=[]
 for j,(a,b)in enumerate(ordinary):
  expected.extend([[f'loader_residual_{j}','-',a,b],[f'loader_square_{j}','*',f'loader_residual_{j}',f'loader_residual_{j}']])
  if j:expected.append([f'loader_sum_{j}','+',f'loader_square_0'if j==1 else f'loader_sum_{j-1}',f'loader_square_{j}'])
 if ordinary:
  last='loader_square_0'if len(ordinary)==1 else f'loader_sum_{len(ordinary)-1}'
  expected.extend([['loader_positive','+',last,1],['loader_scaled','*','lower_history_product','loader_positive'],['loader_output','-','loader_scaled',1]])
 else:expected=[['lower_unit_output','-','lower_history_product',1]]
 need(rows[start:]==expected and entry['output']==expected[-1][0],'entire paid SOS/anchor finalizer')
 need(start==old['certificate']['operations']and len(ordinary)+1==old['certificate']['equations'],'actual certificate boundary')
 return dict(native_base=base,merged_duration=index>=8,normalized_prefixes=normalized,positive_scale_prefixes=scaled,factor_ports=factors,ordinary_comparisons=ordinary,comparisons=[['lower_history_product',1]]+ordinary,certificate_boundary=start,finalizer_source=expected,finalizer_formula='product(factors)*(1+sum(ordinary_residual^2))-1')

def change(rows):
 d={n:(o,a,b)for n,o,a,b in rows}
 req={CUT:('+',S,BETA),Z:('*','factored_pack_q_minus_one','and__F3'),S:('+','factored_pack_A_plus_one','factored_pack_scaled_B'),'factored_pack_scaled_B':('*','factored_pack_q_plus_one','factored_pack_B'),'factored_pack_B':('+','and__padded_B',Z),'factored_pack_q_minus_one':('-','and__q',1),'factored_pack_q_plus_one':('+','and__q',1),'and__bs_packed':('*','factored_pack_q_minus_one',S),'and__wn2':('*',CUT,'and__q')}
 need(all(d.get(n)==v for n,v in req.items()),'literal packing/quotient cut')
 need([n for n,o,a,b in rows if BETA in(a,b)]==[CUT]and[n for n,o,a,b in rows if CUT in(a,b)]==['and__wn2'],'private quotient consumers')
 return[[n,o,Z,b]if n==CUT else copy.deepcopy([n,o,a,b])for n,o,a,b in rows]

def graph(rows,params,aux,numerals,roots):
 known=set(params+aux);defs={};constants=set();M=0
 def op(v):
  if type(v)is int:return True
  if type(v)is str:return v in known
  if type(v)is dict and set(v)=={'fixed_numeral'}and type(v['fixed_numeral'])is str and v['fixed_numeral']in numerals:
   constants.add(v['fixed_numeral']);return True
  return False
 for n,o,a,b in rows:
  need(type(n)is str and n not in known and o in('+','-','*')and op(a)and op(b),'complete typed DAG')
  known.add(n);defs[n]=(o,a,b);M+=o=='*'
 def closure(roots):
  live=set();free=set();todo=list(roots)
  while todo:
   n=todo.pop()
   if type(n)is not str:continue
   if n not in defs:free.add(n);continue
   if n not in live:live.add(n);todo.extend(defs[n][1:])
  return live,free
 live,free=closure([rows[-1][0]])
 need(live==set(defs)and free==set(params+aux)and constants==set(numerals),'all paid gates/supplied coordinates/fixed roles live')
 core,_=closure(roots);core_rows=[copy.deepcopy(row)for row in rows if row[0]in core]
 need(all(n in core for n in roots if type(n)is str),'all requested core ports paid')
 return dict(operations=len(rows),M=M,A=len(rows)-M,all_gates_live=True,witnesses=len(aux),supplied_parameters=len(params),fixed_numeral_roles=len(constants)),core_rows

def degrees(rows,params,aux,inv):
 d={n:1 for n in params+aux};defs={n:(o,a,b)for n,o,a,b in rows}
 for pre in('geo__','and__'):
  X,a,c,g,H=[pre+n for n in('wn2','R12','R10a','gam','a4m5')]
  req={pre+'R15':('-',pre+'L15',pre+'Ac2'),pre+'L15':('*',pre+'R14',pre+'R14'),pre+'R14':('+',pre+'D1',g),pre+'D1':('+',X,pre+'cam2'),pre+'cam2':('*',c,a),pre+'A':('+',pre+'a_square',H),pre+'a_square':('*',a,a),H:('+',pre+'a4',3),pre+'a4':('*',4,a),g:('*',pre+'ga',H),pre+'Ac2':('*',pre+'A',pre+'c2'),pre+'c2':('*',c,c)}
  need(all(defs[n]==v for n,v in req.items()),'all-value main norm expansion '+pre)
 at=lambda v:d[v]if type(v)is str else 0
 for n,o,a,b in rows:
  if n in('geo__R15','and__R15'):
   pre=n[:-3];X,a,c,g,H=[d[pre+s]for s in('wn2','R12','R10a','gam','a4m5')]
   d[n]=max(2*X,X+a+c,X+g,a+c+g,2*g,H+2*c)
  else:d[n]=at(a)+at(b)if o=='*'else max(at(a),at(b))
 fs={n:d[n]for n in inv['factor_ports']};rs=[max(at(a),at(b))for a,b in inv['ordinary_comparisons']]
 expected=sum(fs.values())+2*max(rs,default=0)
 need(d[rows[-1][0]]==expected,'full degree includes unit anchor and every residual square')
 return dict(degree_upper_bound=expected,exact_degree_claimed=False,factor_degree_bounds=fs,ordinary_residual_degree_bounds=rs,anchor_degree_bound=sum(fs.values()),SOS_degree_bound=2*max(rs,default=0),supplied_coordinate_degree=1,fixed_numeral_degree=0)

def identity(old,new,free,inv):
 changed=[[a,b]for a,b in zip(old,new)if a!=b]
 need(len(old)==len(new)and changed==[[[CUT,'+',S,BETA],[CUT,'+',Z,BETA]]],'exact single operand edit')
 # Formal (beta+Z-S)+S=beta+Z. The private occurrence audit lifts it.
 need(tuple(x+y for x,y in zip((1,1,-1),(0,0,1)))==(1,1,0),'local affine identity')
 table={}
 def intern(t):
  if t not in table:table[t]=len(table)
  return table[t]
 def run(rows):
  e={n:intern(('coordinate',n))for n in free}
  def at(v):return e[v]if type(v)is str else intern(('literal',stable(v)))
  for n,o,a,b in rows:e[n]=intern(('proved_beta_cut',))if n==CUT else intern((o,at(a),at(b)))
  return e
 oe,ne=run(old),run(new)
 need(all(oe[n]==ne[n]for n,o,a,b in new),'all full register expressions')
 need(all(oe[n]==ne[n]for n in inv['factor_ports']),'all native and outer factors')
 need(all((oe[a]if type(a)is str else a)==(ne[a]if type(a)is str else a)and(oe[b]if type(b)is str else b)==(ne[b]if type(b)is str else b)for a,b in inv['comparisons']),'all actual comparison operands')
 return dict(changed_rows=changed,whole_register_identities=len(new),factor_identities=len(inv['factor_ports']),comparison_identities=len(inv['comparisons']),full_signed_graph_identity=True,same_coordinate_polynomial_identity=False)

def execute(rows,v,c):
 e=dict(v)
 at=lambda x:e[x]if type(x)is str else c[x['fixed_numeral']]if type(x)is dict else x
 for n,o,a,b in rows:
  a,b=at(a),at(b);e[n]=a*b if o=='*'else a+b if o=='+'else a-b
 return e

def verify(root):
 root=authenticate(root);parent=json.loads((root/'neary_woods_universal_product_scale253.json').read_text());saved=parent['canonical_sources']
 need(type(saved)is list and len(saved)==16,'exact sixteen saved sources')
 tree=ast.parse((root/'binary_tag_parameterized_compressed_compiler.py').read_text());vals=[ast.literal_eval(n.value)for n in tree.body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='NUMERALS'for t in n.targets)]
 need(len(vals)==1 and len(vals[0])==11,'literal fixed numeral recipes');numerals=vals[0]
 fixed_recipe=json.loads((root/'neary_woods_universal_u9_tag_chain.json').read_text())['fixed_recipe']
 pair_receipt=json.loads((root/'neary_woods_universal_tail_quotient253.json').read_text());pair_sources={z['packet']['saved_parent_index']:z['packet']['source']for z in pair_receipt['forms']}
 rng=random.Random(16253982);forms=[];counts=Counter()
 for index,old in enumerate(saved):
  inv=inventory(old,index);rows=change(old['source']);free=old['parameters']+old['auxiliaries'];base=index%8
  deg=degrees(rows,old['parameters'],old['auxiliaries'],inv);before=degrees(old['source'],old['parameters'],old['auxiliaries'],inv)
  need(before['degree_upper_bound']==OLD_DEGREES[base]and deg['degree_upper_bound']==NEW_DEGREES[base],'all old/new degree bounds')
  need(exact(before['factor_degree_bounds'],old['ledger']['degree']['factor_degree_bounds']),'old factor bounds reproduced')
  roots=inv['factor_ports']+[v for ab in inv['ordinary_comparisons']for v in ab]
  led,core=graph(rows,old['parameters'],old['auxiliaries'],numerals,roots)
  need(led['operations']==OPS[base]and led['M']==MULS[base],'entire literal paid count')
  cend=inv['certificate_boundary'];certificate=rows[:cend];coreM=sum(row[1]=='*'for row in core)
  led.update(certificate_operations=cend,certificate_M=sum(row[1]=='*'for row in certificate),certificate_A=sum(row[1]!='*'for row in certificate),comparisons=len(inv['comparisons']),finalizer_operations=len(rows)-cend)
  core_ledger=dict(operations=len(core),M=coreM,A=len(core)-coreM,scope='dependency closure of all factors and ordinary operand ports; excludes grouping and finalizer')
  need(core_ledger['A']==120 and core_ledger['operations']==235+len(inv['normalized_prefixes']),'current paid core formula')
  need(cend==len(core)+len(inv['factor_ports'])-1,'every factor product multiplication paid')
  proof=identity(old['source'],rows,free,inv);counts['whole_register_identities']+=len(rows);counts['factor_identities']+=len(inv['factor_ports']);counts['comparison_identities']+=len(inv['comparisons']);counts['complete_forms']+=1
  for j in range(12):
   v={n:rng.randrange(1,4)if j<4 else rng.randrange(-2,3)for n in free};c={n:rng.randrange(1,4)if j<4 else rng.randrange(-2,3)for n in numerals}
   if j>=10:v={n:Fraction(k,3)for n,k in v.items()};c={n:Fraction(k,3)for n,k in c.items()};counts['rational_cases']+=1
   ce=execute(rows,v,c);pv=dict(v);pv[BETA]+=ce[Z]-ce[S];pe=execute(old['source'],pv,c)
   need(all(ce[n]==pe[n]for n,o,a,b in rows),'every actual register under signed map');counts['numeric_full_identities']+=1
   prod=1
   for n in inv['factor_ports']:prod*=ce[n]
   residuals=[(ce[a]if type(a)is str else a)-(ce[b]if type(b)is str else b)for a,b in inv['ordinary_comparisons']]
   need(ce[old['output']]==prod*(1+sum(x*x for x in residuals))-1,'actual full anchor/SOS value');counts['numeric_finalizers']+=1
  v={n:1 for n in free};c={n:1 for n in numerals};ce=execute(rows,v,c);beta=1+ce[Z]-ce[S]
  need(beta<0 and ce[old['output']]!=0,'off-zero inverse sign boundary');counts['negative_offzero_inverse_cases']+=1
  if index in pair_sources:need(exact(rows,pair_sources[index]),'overlap matches frozen two-source successor');counts['frozen_overlap_matches']+=1
  forms.append(dict(saved_parent_index=index,inventory=inv,source=rows,output=old['output'],parameters=copy.deepcopy(old['parameters']),auxiliaries=copy.deepcopy(old['auxiliaries']),domains={'parameters':'positive; program coefficients fixed on inherited valid shifted U9 slices','auxiliaries':'strictly positive'},fixed_numeral_recipes=copy.deepcopy(numerals),fixed_u9_recipe=copy.deepcopy(fixed_recipe),ledger=led,degree=deg,core_source=core,core_ledger=core_ledger,source_sha256=sha(stable(rows).encode()),historical_parent_ledger=copy.deepcopy(old['ledger']),signed_pullback='beta_parent=beta_child+factored_pack_Z-factored_pack_inner',positive_zero_bijection_scope='same valid shifted U9 program/input slice; inverse positive after native recovery; beta only',whole_graph_proof=proof,offzero_inverse_beta=beta))
 for i in range(8):
  a,b=forms[i],forms[i+8]
  need(a['source'][1:]==b['source'][1:]and a['source'][0][0]==b['source'][0][0]=='program_duration_bound','two interfaces differ only at actual paid duration source')
  need(exact(a['degree'],b['degree'])and exact(a['core_ledger'],b['core_ledger']),'paired interface ledgers')
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),pins=copy.deepcopy(PINS),forms=forms,counts=dict(counts),scope='All16 actual saved canonical product_scale253 sources: eight eligible joint-positive-scale bases times two duration interfaces. No other partitions or unprojected joint bases. Degree bounds only, all supplied parameters degree1 and compiler numerals degree0. Bounded source/receipt CLI, no maintained hostile-packet API; no historical builder imported.')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);args=ap.parse_args();r=verify(args.root)
 if args.expect:need(exact(r,json.loads(args.expect.read_text())),'exact typed saved receipt')
 if args.output:args.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps(dict(status=r['status'],counts=r['counts'],frontier_scope='sixteen saved sources; no optimization census')))
if __name__=='__main__':main()
