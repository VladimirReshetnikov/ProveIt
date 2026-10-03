#!/usr/bin/env python3
"""Two complete Nielsen fixed-table sources: top mask1 and eight-lane range.
Bounded pinned standard-library CLI; reads saved sources, executes no ancestors.
"""
import argparse,copy,hashlib,json,random
from collections import Counter
from fractions import Fraction
from pathlib import Path
PINS={'group_macro_automaton_sharing.py': 'f9d660c3309c030c98c8209f2b8a708a6731eedf62234d459ed4fa3f1db2af48', 'group_macro_automaton_sharing.json': '8e7044b66bebbacc0f89721807369607146b57bb67b14d1ddb9c4e05586a681b', 'group_macro_automaton_sharing.md': 'e253a396f999e8045bb1c4ee223602907f8ea003b7b7f3d93218cb425ffd5585', 'group_projective_label_aligned_lanes.py': 'cbecb51a164f7e4272a293fc2cb6e549838ec153b693399487e3ee0b4dd8c9a5', 'group_projective_label_aligned_lanes.json': '232fbc5d9409da72f7f8b0335316920c93cb435bbcbb43ce122b3b8c17477008', 'group_projective_label_aligned_lanes.md': '66221327c058b335febda310bb81b656b7c7095fb4463d633f60de9cd8213edb', 'group_projective_tail_quotient_shift.py': '08248ad763113a6a2e60168edfd058b92be4e14b2f7932fa1be66eb406a70610', 'group_projective_tail_quotient_shift.json': 'a422e7a65df26e626f3c36f97a53a68805b86806be3dc35d35e7d49a17b80b27', 'group_projective_tail_quotient_shift.md': 'a1e1e67df618f6f809c2e85a409509b288337f62cd1af35cfc6ca950e0efa92a', 'group_projective_idle_free_paths.md': '0cc8b21be7fca0cc5763ba3862f6888f94669259ca26beb0050cd5f8ef1ec9e9', 'group_projective_reindexed_edge_geometry.md': 'ceadd45bebece376f9cbaa5e7be1740f35510a55211819376fa335ad719152d3', 'group_sparse_macro_flow.py': '74604c1a9d1071a823e0df3388d2c89eb639cf3e088a39fa7fff3eae5113238a', 'group_sparse_macro_flow.md': '4e4356902a52de1464c91ac5aea2a654900492b74ee252d9ea22a34e5dd6febc', 'group_projective_shared_flow_target.py': 'eea982ef140ac046f9fe857747fdde82a51bedc78f22306558941ab839eeacf0', 'group_projective_shared_flow_target.md': '17bc108499565d3cbc5a6c55ca9395693c8fcce5c72069f5080560702424d1e4', 'group_projective_shared_selector_pack.md': 'b29225304b4a3b96c922df5645ca7060adc60c3074ed20e561a8e074dc411d66', 'group_projective_port_bias_folding.md': 'e699bb645378ced31c62dd9bb702eb6ed0ea93be8b6ee91e1cdc859b27e3c706', 'group_projective_zero_mortality6.md': 'c0f3cb53d8a189dd7b98e0deb892a75e64426e8ac480ee049f945ed09e896bc2', '../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md': '47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b', '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', 'group_projective_coupled_linear_unit.md': '15fa0737a82996a8ea5c28aa62cbbe798ac5e06e4a3323c4dcaa01c9cd6286c7', 'group_projective_joint_bound_unit.md': '3f33f4d7c04137409688b011859578924a4d1571d46d37bf1ca7ebd81a230a1e', 'group_projective_joint_first_norm.md': 'da7f6baaedaecae3166cfed050d2e913d26b280cc3332ca04bf0e8983417e9cb', 'group_projective_output_bound_obstruction.md': 'b478f73d003a62ed530ba329c01f875be7a5da2202b746d89ccd50f8f50aa56b', 'group_projective_padded_program_margin.md': 'a4ad4487f682d250f3a9ae84cc8f4182b21d2e216fa0d53624f7368abd028952', 'group_projective_product_radix_scale.json': '1403987d49c3613b3ca6cdc1f1794d16199af9020c9c88fd53c49981f95db9a7', 'group_projective_product_radix_scale.md': 'f342dbc1da849a7c74cc7043becad6d218582adeefffa55dec558a28b1e47b39', 'group_projective_product_radix_scale.py': 'd33e8aa3bff7559c72768be7116f0328ebad0cf65190115101457a71a0e25965', 'group_projective_shifted_X_quotient.md': '4f76dda46f9385a769da0c809292b466d352be2a6f2d39c5e70519bdeda37e00', 'group_projective_strong_unit_product.md': '06978175efe47f59bf497f8882b3138692abead1458c58de6a53af92b4f83605', 'native_controller_binary_selector56.md': '97fcdc7188f968f2ac3e315249b0e0a15dcc787c10451924ad3f2551c8bb376c', 'group_projective_shared_macro_automaton.json': '284da792cce620169ebca9cae7ee77488b56fe0f68c47cf12059af5d0e980497', 'group_projective_shared_macro_automaton.md': '5933851785599c3c83bbddc28f1dbe2e43c7db17ed256a87a5dd293117bc9eb6', 'group_projective_shared_macro_automaton.py': '2cbbc82d18e0e175d3c7f44707fdc16c2bf899aaad5deafa44c0975cf0b96bf7', 'group_projective_inverse_macro_sharing.py': 'c23f1cff1ccf1d7ad004c29670cf08926e05790eb02baeaddf4c691bd9b02957', 'group_projective_inverse_macro_sharing.json': '4f02c041fcb8db78849c5d95c2b23cabab615c88e42ef648f9c8377d876fb09b', 'group_projective_inverse_macro_sharing.md': '8ba6acdfcbf932c2814b44de590ac456ae223d7d686d19d72d54e17e2e0c8ac0', 'group_projective_unit_top_mask.py': '1b96e1908e35f95598230c658d42d83d83cb24dc1dea48726f948353011738d3', 'group_projective_unit_top_mask.json': 'a7544f40ce74ee67088fbfa1d753a04cf921cac6f04486dd7f6d83a39befa2e2', 'group_projective_unit_top_mask.md': 'e0898d1fc20f2f4c1abff21d33f90382aeac4f6b24c648624f0e54d59a3619b2'}
P='controller__geometry_power'
FACTORS=['first_unit','selection__R15','selection__P17','index_unit','linear_unit','strong_unit','joint_bound_unit']
RT=(2,3,6,7);BMAC=(1,5)*5;AMAC=RT+BMAC
def need(c,m):
 if not c:raise ValueError(m)

def sha(b):return hashlib.sha256(b).hexdigest()

def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b

def execute(rows,v):
 e=dict(v)
 for n,o,a,b in rows:
  a=e[a]if type(a)is str else a;b=e[b]if type(b)is str else b;e[n]=a*b if o=='*'else a+b if o=='+'else a-b
 return e

def ledger(rows,free,roots):
 d={n:1 for n in free};defs={};M=0
 for n,o,a,b in rows:
  need(n not in d and o in('+','-','*'),'fresh gate');need(all(type(v)is int or type(v)is str and v in d for v in(a,b)),'closure')
  da=d[a]if type(a)is str else 0;db=d[b]if type(b)is str else 0;d[n]=da+db if o=='*'else max(da,db);defs[n]=(a,b);M+=o=='*'
 seen=set();used=set();todo=list(roots)
 while todo:
  n=todo.pop()
  if type(n)is int:continue
  if n not in defs:used.add(n)
  elif n not in seen:seen.add(n);todo.extend(defs[n])
 need(seen==set(defs)and used==set(free),'full source liveness')
 return dict(operations=len(rows),M=M,A=len(rows)-M,degree_upper=max(d[n]if type(n)is str else 0 for n in roots))

def poly_atom(v):return {(v,):1}if type(v)is str else({():v}if v else{})

def poly_op(op,a,b):
 out=Counter()
 if op=='*':
  for u,c in a.items():
   for v,d in b.items():out[tuple(sorted(u+v))]+=c*d
 else:
  out.update(a)
  for v,d in b.items():out[v]+=d if op=='+'else-d
 return {m:c for m,c in out.items()if c}

def path_for_word(edges,word):
 states={0:[]}
 for label in word:
  nxt={}
  for st,path in sorted(states.items()):
   for i,(a,b,l)in enumerate(edges):
    if a==st and l==label and b not in nxt:nxt[b]=path+[i]
  states=nxt
 need(0 in states,'actual accepting control path');return states[0]

def authenticate(root):
 blobs={}
 for name,h in PINS.items():
  path=Path(root)/name
  if not path.exists():path=Path(__file__).resolve().parent/name
  data=path.read_bytes();need(sha(data)==h,'pin '+name);blobs[name]=data
 return blobs

def exact_degree(p):
 rows=p['source'];defs={n:(o,a,b)for n,o,a,b in rows};X,A,c,g,H='selection__wn2','selection__R12','selection__R10a','selection__gam','selection__a4m5'
 expected={'selection__R15':('-','selection__L15','selection__Ac2'),'selection__L15':('*','selection__R14','selection__R14'),'selection__R14':('+','selection__D1',g),'selection__D1':('+',X,'selection__cam2'),'selection__cam2':('*',c,A),'selection__A':('+','selection__a_square',H),'selection__a_square':('*',A,A),H:('+','selection__a4',3),'selection__a4':('*',4,A),g:('*','selection__ga',H),'selection__Ac2':('*','selection__A','selection__c2'),'selection__c2':('*',c,c)}
 need(all(defs[n]==v for n,v in expected.items()),'literal guarded main norm cone')
 prime=1000000007;rng=random.Random(714);weights={n:rng.randrange(1,100)for n in sorted(p['free'])};env={n:(1,w)for n,w in weights.items()}
 def add(a,b,sign=1):
  d=max(a[0],b[0]);return d,((a[1]if a[0]==d else 0)+sign*(b[1]if b[0]==d else 0))%prime
 def mul(a,b):return a[0]+b[0],a[1]*b[1]%prime
 for n,o,a,b in rows:
  av=env[a]if type(a)is str else(0,a%prime);bv=env[b]if type(b)is str else(0,b%prime)
  if n=='selection__R15':
   xx,aa,cc,gg,hh=[env[v]for v in(X,A,c,g,H)]
   terms=[mul(xx,xx),mul((0,2),mul(mul(xx,aa),cc)),mul((0,2),mul(xx,gg)),mul((0,2),mul(mul(aa,cc),gg)),mul(gg,gg),mul((0,-1),mul(hh,mul(cc,cc)))]
   z=terms[0]
   for term in terms[1:]:z=add(z,term)
  else:z=mul(av,bv)if o=='*'else add(av,bv,1 if o=='+'else-1)
  env[n]=z
 target=73+2*(29*p['a_scale']+7*p['m']+106)
 need(env['joint_outer_output'][0]==target and env['joint_outer_output'][1]!=0,'attained complete fixed-numeral target degree')
 need(sum(env[n][0]for n in FACTORS)+6==target,'actual seven factors and outer degree')
 return dict(exact_degree=target,guarded_upper=target,naive_upper=p['ledger']['degree_upper'],factor_degrees={n:env[n][0]for n in FACTORS},prime=prime,weights=weights,nonzero_full_leader=env['joint_outer_output'][1],scope='All supplied coordinates including x have degree1; fixed24,13 and all compiler numerals degree0.')

def outer_history(p,x):
 need(x>0 and x%5==2,'sufficient accepted residue class')
 u=24*x+13;exponent=(u-1)//5;word=RT+BMAC*exponent
 # Same physical word is A B^(exponent-1) and the Nielsen word Rtilde B^exponent.
 need(exponent>=1 and word==AMAC+BMAC*(exponent-1),'explicit accepted macro decomposition')
 path=path_for_word(p['edges'],word);state=[1,u,1,u];states=[list(state)]
 for label in word:
  k=(label-1)//2;state=list(state);state[k]+=(1 if label%2 else-1)*state[k^1];states.append(state)
 need(state==[0,1,0,1],'actual ordinary-input accepting endpoint')
 D=128
 while D<=max(u,1+max(abs(v)for st in states for v in st)):D*=2
 B=16*D;t=len(word);pv=B**t;J=sum(B**i for i in range(t));v={'x':x,'height_slack':D-u}
 for k in range(4):v['H'+str(k)]=sum((st[k]+D-1)*B**i for i,st in enumerate(states[:-1]))
 for label in range(1,9):v['Zhat'+str(label-1)]=1+sum((states[i][((label-1)//2)^1]+D-1)*B**i for i,l in enumerate(word)if l==label)
 for edge in range(len(p['edges'])):v['controller__edge_hat'+str(edge+1)]=1+sum(B**i for i,j in enumerate(path)if j==edge)
 v['selection__bound_global']=pv+1-sum(v['H'+str(i)]for i in range(4))-sum(v['Zhat'+str(i)]for i in range(8));need(min(v.values())>0 and B>p['m'],'genuine positive outer values and actual radix margin')
 defs={n:(o,a,b)for n,o,a,b in p['source']};env=dict(v)
 def value(a):
  if type(a)is int:return a
  if a not in env:
   o,b,c=defs[a];bv,cv=value(b),value(c);env[a]=bv*cv if o=='*'else bv+cv if o=='+'else bv-cv
  return env[a]
 need(value(P)==pv and value(p['cuts']['computed_J'])==J,'genuine duration and repunit')
 need(value(p['cuts']['controller__flow_left'])==value(p['cuts']['controller__flow_right']),'genuine chronological controller')
 H,M,Z=[value(n)for n in ('range_H','range_M','range_Z')];q=value('selection__q');Q=q//16
 need(H&M==Z and max(H,M,Z)<Q and q==32*B*pv**p['a_scale'],'full joined AND/product scale')
 fields=[16*(Q-H-M+Z)-15,16*(H-Z)+4,16*(M-Z)+2,16*Z+8]
 need(min(fields)>0 and sum(fields)==q-1,'all four positive native fields')
 for k in range(4):need(value('history__left'+str(k))==value('history__right'+str(k)),'complete genuine endpoint equation')
 need(value('joint_bound_unit')==1,'actual positive global bound slack')
 return dict(x=x,u=u,word=[int(l)for l in word],edge_path=path,duration=t,D=D,B=B,P_bit_length=pv.bit_length(),q_bit_length=q.bit_length(),native_truth_fields_positive=True,all_five_outer_residuals_zero=True,joint_bound_unit=1,native_positive_extension='inherited theorem, not materialized',full_native_pell_zero_materialized=False)


def rewrite(parent,separate):
 defs={r[0]:r for r in parent['source']}
 need(defs['range_Bminus_shift']==['range_Bminus_shift','*','range_body_scale',2]and[r[0]for r in parent['source']if'range_Bminus_shift'in r[2:]]==['range_M'],'private paid2*T2 cone')
 need(defs['range_M']==['range_M','+','range_Mbody','range_Bminus_shift'],'literal top-mask consumer')
 need(defs['range_mask8']==['range_mask8','*','range_cell','controller__origin_mask'],'literal reused range mask')
 need(defs['joint_scale']==['joint_scale','*','controller__lane_power3','controller__flow_185']and defs['range_body_scale']==['range_body_scale','*','joint_scale','controller__flow_185'],'actual P32/range scale consumers')
 need(not any(o=='*'and {a,b}=={parent['cuts']['computed_J'],'controller__lane_repunit2'}for n,o,a,b in parent['source']),'no already-paid J times R8 product')
 rows=[]
 for n,o,a,b in parent['source']:
  if n=='range_Bminus_shift':continue
  if separate and n=='range_mask8':
   rows.append(['range_origin8','*',parent['cuts']['computed_J'],'controller__lane_repunit2']);b='range_origin8'
  if separate and n=='range_body_scale':b='controller__lane_power3'
  if n=='range_M':b='range_body_scale'
  rows.append([n,o,a,b])
 return dict(source=rows,free=copy.deepcopy(parent['free']),parameters=['x'],auxiliaries=copy.deepcopy(parent['auxiliaries']),domains=copy.deepcopy(parent['domains']),comparisons=copy.deepcopy(parent['comparisons']),edges=copy.deepcopy(parent['edges']),positions=copy.deepcopy(parent['positions']),cuts=copy.deepcopy(parent['cuts']),m=32,a_scale=48 if separate else 72,range_lanes=8 if separate else 32,top_mask=1,output='joint_outer_output',graph='nielsen',packing=parent['packing'],flow=parent['flow'])

def scalar_polynomials(p):
 # Independent formal P/J/D/B and already-proved physical/controller ports.
 ports={P:'p',p['cuts']['computed_J']:'j','B':'b','D':'d','selection__Hbatch':'h','selection__Mbatch':'m','selection__Zbatch':'z',p['cuts']['controller__edge_word']:'c'}
 defs={n:(o,a,b)for n,o,a,b in p['source']};memo={}
 def value(v):
  if type(v)is int:return poly_atom(v)
  if v in ports:return poly_atom(ports[v])
  if v not in memo:
   o,a,b=defs[v];memo[v]=poly_op(o,value(a),value(b))
  return memo[v]
 def power(k):return {tuple(['p']*k):1}
 def add(*terms):
  r={}
  for q in terms:r=poly_op('+',r,q)
  return r
 def mul(a,b):return poly_op('*',a,b)
 V={k:poly_atom(k)for k in ['p','j','b','d','h','m','z','c']}
 rep=lambda n:add(*[power(i)for i in range(n)])
 origin=mul(V['j'],rep(32));origin_range=mul(V['j'],rep(p['range_lanes']));T=power(40);T2=power(p['a_scale']);cell=add(mul(poly_atom(2),V['d']),poly_atom(-1));range_mask=mul(cell,origin_range)
 wanted={'controller__origin_mask':origin,'joint_scale':T,'range_body_scale':T2,'range_mask8':range_mask,'range_H':add(V['h'],mul(power(8),V['c']),mul(T,V['h']),mul(V['b'],T2)),'range_M':add(V['m'],mul(power(8),origin),mul(T,range_mask),T2),'range_Z':add(V['z'],mul(power(8),V['c']),mul(T,V['h'])),'selection__q':mul(poly_atom(32),mul(V['b'],T2))}
 if p['range_lanes']==8:wanted['range_origin8']=origin_range
 for n,q in wanted.items():need(value(n)==q,'complete changed scalar polynomial '+n)
 return dict(exact_polynomial_count=len(wanted),coefficient_terms=sum(map(len,wanted.values())),ports=list(wanted))

def complete_interface(parent,child):
 # The literal source changes only these three polynomial ports and one new
 # private origin8 gate; compare every common register after proving the ports.
 intern={}
 def node(k):
  if k not in intern:intern[k]=len(intern)
  return intern[k]
 cuts={'range_mask8','range_body_scale','range_M'}
 def run(rows):
  e={n:node(('v',n))for n in parent['free']}
  for n,o,a,b in rows:
   av=e[a]if type(a)is str else node(('c',a));bv=e[b]if type(b)is str else node(('c',b));e[n]=node(('cut',n))if n in cuts else node((o,av,bv))
  return e
 a,b=run(parent['source']),run(child['source']);common=set(a)&set(b)-set(parent['free'])
 need(all(a[k]==b[k]for k in common),'every retained register under the proved scalar interface')
 need(a['joint_outer_output']==b['joint_outer_output'],'complete output under changed interface')
 need(parent['comparisons']==child['comparisons'],'every comparison retained')
 # The literal five residuals and their finalizer operands are untouched.
 pa={r[0]:r for r in parent['source']};ch={r[0]:r for r in child['source']}
 finals=[n for n in pa if n.startswith('joint_outer_')]
 need(len(finals)==17 and all(pa[n]==ch[n]for n in finals),'all seventeen literal finalizer instructions')
 return dict(complete_retained_register_identities=len(common),comparisons=6,finalizer_gates=17,whole_interface_identity=True,same_tuple_full_polynomial_identity=False)

def numeric_interface(parent,p,case):
 rng=random.Random(671+case);values={n:rng.randrange(-1,3)for n in p['free']}
 if case>=4:values={n:Fraction(v,3)for n,v in values.items()}
 e=execute(p['source'],values);P0=e[P];J=e[p['cuts']['computed_J']];B=e['B'];D=e['D'];h=e['selection__Hbatch'];m=e['selection__Mbatch'];z=e['selection__Zbatch'];c=e[p['cuts']['controller__edge_word']]
 rep=lambda k:sum(P0**i for i in range(k));T=P0**40;T2=P0**p['a_scale']
 need(e['range_H']==h+P0**8*c+T*h+B*T2,'entire H')
 need(e['range_M']==m+P0**8*J*rep(32)+T*(2*D-1)*J*rep(p['range_lanes'])+T2,'entire M')
 need(e['range_Z']==z+P0**8*c+T*h and e['selection__q']==32*B*T2,'entire Z/q')
 res=[e[a]-(e[b]if type(b)is str else b)for a,b in p['comparisons']]
 need(e[p['output']]==e['eight_units']*(1+sum(v*v for i,v in enumerate(res)if i!=4))-1,'complete paid finalizer')
 if p['range_lanes']==32:
  old=execute(parent['source'],values);q=e['selection__q'];delta=16*T2*(q*q-1)
  need(e['index_unit']-old['index_unit']==delta,'exact changed index unit')
  others=1
  for name in FACTORS:
   if name!='index_unit':need(e[name]==old[name],'unchanged six unit factors');others*=e[name]
  need(e[p['output']]-old[p['output']]==delta*others*e['joint_outer_positive'],'full same-coordinate correction, not identity')
 return dict(rational=case>=4)

def range_typing_checks():
 count=0
 for B in(16,32,64):
  D=B//16
  for t in(1,2,3):
   P0=B**t;J=sum(B**i for i in range(t));cell=2*D-1;R8=sum(P0**i for i in range(8));R32=sum(P0**i for i in range(32));small=cell*J*R8;large=cell*J*R32
   need(large%P0**8==small,'low8 exact typed mask')
   for H in(0,1,P0-1,P0**7,P0**8-1,small):
    need(H<P0**8 and(H&large)==(H&small),'complete typed low-eight mask equivalence');count+=1
 return count

def verify(root):
 blobs=authenticate(root);parent_receipt=json.loads(blobs['group_projective_inverse_macro_sharing.json']);parent=parent_receipt['packets']['nielsen']
 need(parent['ledger']['operations']==371 and len(parent['edges'])==28 and parent['m']==32 and parent['ledger']['exact_degree']==4909,'actual frozen Nielsen complete source')
 counts=Counter();packets={};outer=[]
 for separate in(False,True):
  p=rewrite(parent,separate);tag='separate8'if separate else'reused32';p['ledger']=ledger(p['source'],p['free'],[p['output']]);p['scalar_proof']=scalar_polynomials(p);p['interface_proof']=complete_interface(parent,p);p['degree_certificate']=exact_degree(p)
  p['ledger'].update(naive_degree_upper=p['ledger']['degree_upper'],degree_upper=p['degree_certificate']['exact_degree'],exact_degree=p['degree_certificate']['exact_degree'],certificate_operations=len(p['source'])-17,finalizer_operations=17,comparisons=6,positive_witnesses=len(p['auxiliaries']))
  need((len(p['source']),p['ledger']['M'],p['ledger']['A'],p['ledger']['exact_degree'])==((371,150,221,3517)if separate else(370,149,221,4909)),'two complete current ledgers/degrees')
  counts['complete_sources']+=1;counts['paid_live_gates']+=len(p['source']);counts['exact_scalar_polynomials']+=p['scalar_proof']['exact_polynomial_count'];counts['retained_register_identities']+=p['interface_proof']['complete_retained_register_identities'];counts['whole_comparisons']+=6;counts['exact_degree_certificates']+=1
  for case in range(6):r=numeric_interface(parent,p,case);counts['complete_numeric_outputs']+=1;counts['rational_outputs']+=r['rational']
  for x in(2,7):r=outer_history(p,x);r['variant']=tag;outer.append(r);counts['genuine_accepting_outer_histories']+=1
  packets[tag]=p
 counts['typed_range_mask_equivalences']=range_typing_checks()
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),pins=copy.deepcopy(PINS),counts=dict(counts),historical_parent=dict(operations=371,M=150,A=221,exact_degree=4909,source_sha256=sha(json.dumps(parent['source'],separators=(',',':')).encode())),packets=packets,accepting_outer_histories=outer,matrix_language=copy.deepcopy(parent_receipt['matrix_language']),scope='Two actual complete Nielsen fixed-table sources with top mask1. Full370/exact4909 and full371/exact3517; same positive outer-coordinate projection via typing and fresh native extension, not a same-tuple identity or zero-fiber bijection. Proper nonempty ordinary-input predicate inherited; no numerical universal bound.')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'exact typed receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status=r['status'],counts=r['counts'],ledgers={k:p['ledger']for k,p in r['packets'].items()})))
if __name__=='__main__':main()
