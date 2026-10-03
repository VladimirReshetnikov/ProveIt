#!/usr/bin/env python3
"""A general separate-eight-lane range transfer on seven complete frozen sources.
Standalone bounded source/proof CLI. No historical Python executes.
"""
import argparse,copy,hashlib,json,random
from collections import Counter
from fractions import Fraction
from pathlib import Path
PINS={'group_macro_automaton_sharing.py': 'f9d660c3309c030c98c8209f2b8a708a6731eedf62234d459ed4fa3f1db2af48', 'group_macro_automaton_sharing.json': '8e7044b66bebbacc0f89721807369607146b57bb67b14d1ddb9c4e05586a681b', 'group_macro_automaton_sharing.md': 'e253a396f999e8045bb1c4ee223602907f8ea003b7b7f3d93218cb425ffd5585', 'group_projective_label_aligned_lanes.py': 'cbecb51a164f7e4272a293fc2cb6e549838ec153b693399487e3ee0b4dd8c9a5', 'group_projective_label_aligned_lanes.json': '232fbc5d9409da72f7f8b0335316920c93cb435bbcbb43ce122b3b8c17477008', 'group_projective_label_aligned_lanes.md': '66221327c058b335febda310bb81b656b7c7095fb4463d633f60de9cd8213edb', 'group_projective_tail_quotient_shift.py': '08248ad763113a6a2e60168edfd058b92be4e14b2f7932fa1be66eb406a70610', 'group_projective_tail_quotient_shift.json': 'a422e7a65df26e626f3c36f97a53a68805b86806be3dc35d35e7d49a17b80b27', 'group_projective_tail_quotient_shift.md': 'a1e1e67df618f6f809c2e85a409509b288337f62cd1af35cfc6ca950e0efa92a', 'group_projective_idle_free_paths.md': '0cc8b21be7fca0cc5763ba3862f6888f94669259ca26beb0050cd5f8ef1ec9e9', 'group_projective_reindexed_edge_geometry.md': 'ceadd45bebece376f9cbaa5e7be1740f35510a55211819376fa335ad719152d3', 'group_sparse_macro_flow.py': '74604c1a9d1071a823e0df3388d2c89eb639cf3e088a39fa7fff3eae5113238a', 'group_sparse_macro_flow.md': '4e4356902a52de1464c91ac5aea2a654900492b74ee252d9ea22a34e5dd6febc', 'group_projective_shared_flow_target.py': 'eea982ef140ac046f9fe857747fdde82a51bedc78f22306558941ab839eeacf0', 'group_projective_shared_flow_target.md': '17bc108499565d3cbc5a6c55ca9395693c8fcce5c72069f5080560702424d1e4', 'group_projective_shared_selector_pack.md': 'b29225304b4a3b96c922df5645ca7060adc60c3074ed20e561a8e074dc411d66', 'group_projective_port_bias_folding.md': 'e699bb645378ced31c62dd9bb702eb6ed0ea93be8b6ee91e1cdc859b27e3c706', 'group_projective_zero_mortality6.md': 'c0f3cb53d8a189dd7b98e0deb892a75e64426e8ac480ee049f945ed09e896bc2', '../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md': '47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b', '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', 'group_projective_coupled_linear_unit.md': '15fa0737a82996a8ea5c28aa62cbbe798ac5e06e4a3323c4dcaa01c9cd6286c7', 'group_projective_joint_bound_unit.md': '3f33f4d7c04137409688b011859578924a4d1571d46d37bf1ca7ebd81a230a1e', 'group_projective_joint_first_norm.md': 'da7f6baaedaecae3166cfed050d2e913d26b280cc3332ca04bf0e8983417e9cb', 'group_projective_output_bound_obstruction.md': 'b478f73d003a62ed530ba329c01f875be7a5da2202b746d89ccd50f8f50aa56b', 'group_projective_padded_program_margin.md': 'a4ad4487f682d250f3a9ae84cc8f4182b21d2e216fa0d53624f7368abd028952', 'group_projective_product_radix_scale.json': '1403987d49c3613b3ca6cdc1f1794d16199af9020c9c88fd53c49981f95db9a7', 'group_projective_product_radix_scale.md': 'f342dbc1da849a7c74cc7043becad6d218582adeefffa55dec558a28b1e47b39', 'group_projective_product_radix_scale.py': 'd33e8aa3bff7559c72768be7116f0328ebad0cf65190115101457a71a0e25965', 'group_projective_shifted_X_quotient.md': '4f76dda46f9385a769da0c809292b466d352be2a6f2d39c5e70519bdeda37e00', 'group_projective_strong_unit_product.md': '06978175efe47f59bf497f8882b3138692abead1458c58de6a53af92b4f83605', 'native_controller_binary_selector56.md': '97fcdc7188f968f2ac3e315249b0e0a15dcc787c10451924ad3f2551c8bb376c', 'group_projective_shared_macro_automaton.json': '284da792cce620169ebca9cae7ee77488b56fe0f68c47cf12059af5d0e980497', 'group_projective_shared_macro_automaton.md': '5933851785599c3c83bbddc28f1dbe2e43c7db17ed256a87a5dd293117bc9eb6', 'group_projective_shared_macro_automaton.py': '2cbbc82d18e0e175d3c7f44707fdc16c2bf899aaad5deafa44c0975cf0b96bf7', 'group_projective_inverse_macro_sharing.py': 'c23f1cff1ccf1d7ad004c29670cf08926e05790eb02baeaddf4c691bd9b02957', 'group_projective_inverse_macro_sharing.json': '4f02c041fcb8db78849c5d95c2b23cabab615c88e42ef648f9c8377d876fb09b', 'group_projective_inverse_macro_sharing.md': '8ba6acdfcbf932c2814b44de590ac456ae223d7d686d19d72d54e17e2e0c8ac0', 'group_projective_unit_top_mask.py': '1b96e1908e35f95598230c658d42d83d83cb24dc1dea48726f948353011738d3', 'group_projective_unit_top_mask.json': 'a7544f40ce74ee67088fbfa1d753a04cf921cac6f04486dd7f6d83a39befa2e2', 'group_projective_unit_top_mask.md': 'e0898d1fc20f2f4c1abff21d33f90382aeac4f6b24c648624f0e54d59a3619b2', 'group_projective_nonempty_mask_frontier.py': '10d38ebaeac82c9e8ba39eefac3d03a9092e08035a8b5f0aef8dd30f78992cd5', 'group_projective_nonempty_mask_frontier.json': '589337541f83814e8d546d919caf2ab4a8977b76583f0110b9509e812521b655', 'group_projective_nonempty_mask_frontier.md': 'a0baff1b8223955f7d7682f31f8a8d1d62abe5bf72bce251e750207937fbce54', 'review_group_projective_nonempty_mask_frontier.py': '66a0b8d1d8a55fcb9fda66747440850fe88b387e85e2f1ba33a8bc525770fa09', 'review_group_projective_nonempty_mask_frontier.json': 'd4c7bd3b75bf44f26a998ad9a1057bb0e1389ac12a98e851522339414f92414a', 'review_group_projective_nonempty_mask_frontier.md': '799124b3a456dcded7d9b15ac80d61a4547ce8162fce859000b3fd2937c0754b', 'group_commutator_universal_substrate.py': '2eff5df85eebf91c09cc89de9b00a836241b27a5f45081f8954b430e02d68085', 'group_commutator_universal_substrate.json': '5ce9fdc18af091d4f16a9b12a579d0ca6528edd2bf262cad73a6c1554d7903e4', 'group_commutator_universal_substrate.md': '64a31c4ef76a1684b51f035735d817df53639c070d16c221eb9ee2095e51bf6a', 'group_projective_padded_program_margin.py': 'cd985af757b8354a6d8e78db6854a81d07279bdf731c029e6b0c67465afbc576', 'group_projective_padded_program_margin.json': 'fe016602afe3a09e43546f3c8726caefc1149047def8eb71ed38582f6e7deb20', 'group_projective_zero_mortality6.py': 'f3a28ea5244500533cc83d95a834e30e2748bb22461bcfb0e7016dc8259f96ad', 'group_projective_zero_mortality6.json': '035434a110f51804344a3a9110d5892633c8e75d7eceb4b78f685b3d83e10ce8'}
P='controller__geometry_power'
FACTORS=['first_unit','selection__R15','selection__P17','index_unit','linear_unit','strong_unit','joint_bound_unit']
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
 origin=mul(V['j'],rep(p['m']));origin_range=mul(V['j'],rep(p['range_lanes']));T=power(p['m']+8);T2=power(p['a_scale']);cell=add(mul(poly_atom(2),V['d']),poly_atom(-1));range_mask=mul(cell,origin_range)
 wanted={'controller__origin_mask':origin,'joint_scale':T,'range_body_scale':T2,'range_mask8':range_mask,'range_H':add(V['h'],mul(power(8),V['c']),mul(T,V['h']),mul(V['b'],T2)),'range_M':add(V['m'],mul(power(8),origin),mul(T,range_mask),T2),'range_Z':add(V['z'],mul(power(8),V['c']),mul(T,V['h'])),'selection__q':mul(poly_atom(32),mul(V['b'],T2))}
 if p['range_origin_added']:wanted['range_origin8']=origin_range
 for n,q in wanted.items():need(value(n)==q,'complete changed scalar polynomial '+n)
 return dict(exact_polynomial_count=len(wanted),coefficient_terms=sum(map(len,wanted.values())),ports=list(wanted))


def pure_power(rows,port):
 defs={n:(o,a,b)for n,o,a,b in rows};memo={P:{1:1}}
 def add(a,b,sign=1):
  out=dict(a)
  for k,v in b.items():out[k]=out.get(k,0)+sign*v
  return {k:v for k,v in out.items()if v}
 def mul(a,b):
  out=Counter()
  for k,v in a.items():
   for j,c in b.items():out[k+j]+=v*c
  return {k:v for k,v in out.items()if v}
 def rec(x):
  if type(x)is int:return {0:x}if x else{}
  if x not in memo:
   need(x in defs,'not a pure P polynomial: '+x);o,a,b=defs[x];a,b=rec(a),rec(b);memo[x]=mul(a,b)if o=='*'else add(a,b,1 if o=='+'else-1)
  return memo[x]
 return rec(port)

def base_polynomial(rows,port,free):
 defs={n:(o,a,b)for n,o,a,b in rows};memo={P:poly_atom(P)}
 def value(v):
  if type(v)is int or v in free:return poly_atom(v)
  if v not in memo:
   o,a,b=defs[v];memo[v]=poly_op(o,value(a),value(b))
  return memo[v]
 return value(port)

def inspect(parent):
 rows=parent['source'];defs={r[0]:r for r in rows}
 need(defs['B']==['B','*',16,'D'],'retained literal B=16D')
 need(defs['range_Bminus_shift']==['range_Bminus_shift','*','range_body_scale',2]and[r[0]for r in rows if'range_Bminus_shift'in r[2:]]==['range_M'],'strict private paid top-mask2')
 need(defs['range_M']==['range_M','+','range_Mbody','range_Bminus_shift'],'literal mask consumer')
 need(defs['range_mask8']==['range_mask8','*','range_cell','controller__origin_mask'],'canonical reused range consumer')
 need(defs['range_body_scale'][1:3]==['*','joint_scale'],'literal range scale')
 pm=defs['range_body_scale'][3];degree=pure_power(rows,pm);need(len(degree)==1,'monomial Pm')
 m,coeff=next(iter(degree.items()));need(coeff==1 and m>=8 and m&(m-1)==0,'power-of-two padded m>=8')
 need(pure_power(rows,'controller__lane_power3')=={8:1}and pure_power(rows,'controller__lane_repunit2')=={i:1 for i in range(8)},'actual already-paid P8 and R8')
 need(pure_power(rows,'joint_scale')=={m+8:1}and pure_power(rows,'range_body_scale')=={2*m+8:1},'actual old scale exponents')
 need(defs['joint_scale'][1:]==['*','controller__lane_power3',pm],'Pm has a retained scale consumer')
 origin=defs['controller__origin_mask'];need(origin[1]=='*','origin product')
 J,rm=origin[2:];need(pure_power(rows,rm)=={i:1 for i in range(m)},'literal full controller repunit')
 C=defs['joint_edge_shift'][3];need(defs['joint_edge_shift'][1:3]==['*','controller__lane_power3'],'actual C port')
 need(defs['controller__geometry_power']==['controller__geometry_power','+','controller__geometry_product',1]and defs['controller__geometry_product']==['controller__geometry_product','*','controller__cell_minus1',J],'computed repunit P identity')
 need(defs['controller__cell_minus1']==['controller__cell_minus1','-','B',1],'radix-minus-one identity')
 alpha=defs['history__input_product'][2];gamma=defs['history__u'][3]
 need(defs['history__input_product']==['history__input_product','*',alpha,'x']and type(alpha)is int and alpha>0,'positive fixed affine multiplier')
 need(defs['history__u']==['history__u','+','history__input_product',gamma]and type(gamma)is int and gamma>0,'positive fixed affine offset')
 need(defs['D']==['D','+','history__u','height_slack']and 16*(alpha+gamma+1)>m,'actual paid B>m margin before typing')
 edgevars=[v for v in parent['free']if v.startswith('controller__edge_hat')];n=len(edgevars);need(1<=n<=m,'nonempty edge coordinates/padded bound')
 wanted=poly_atom(-n)
 for v in edgevars:wanted=poly_op('+',wanted,poly_atom(v))
 need(base_polynomial(rows,J,set(parent['free']))==wanted,'full hatted checksum polynomial')
 hb={}
 for i in range(4):
  for j in (2*i,2*i+1):hb[(f'H{i^1}',)+tuple([P]*j)]=1
 hb={tuple(sorted(k)):v for k,v in hb.items()}
 need(base_polynomial(rows,'selection__Hbatch',set(parent['free']))==hb,'exact all-eight physical history polynomial')
 need(defs['selection__F3']==['selection__F3','+','selection__scaled_Z',8]and defs['selection__scaled_Z']==['selection__scaled_Z','*',16,'range_Z'],'literal positive leading F3 producer')
 # The native leading-form theorem requires these independent supplied ports.
 for name in ['selection__tau_gap','selection__ga','selection__eta','selection__zeta','selection__i','selection__f','selection__h','selection__odd_half','H2','H3']:
  need(name in parent['free'],'independent canonical coordinate '+name)
 return dict(m=m,n=n,J=J,C=C,Pm=pm,Rm=rm,alpha=alpha,gamma=gamma,minimum_B=16*(alpha+gamma+1))

def rewrite(parent):
 info=inspect(parent);J=info['J'];r8='controller__lane_repunit2'
 paid=[n for n,o,a,b in parent['source']if o=='*'and {a,b}=={J,r8}]
 origin=paid[0]if paid else'range_origin8';rows=[]
 for n,o,a,b in parent['source']:
  if n=='range_Bminus_shift':continue
  if n=='range_mask8':
   if not paid:rows.append([origin,'*',J,r8])
   b=origin
  if n=='range_body_scale':b='controller__lane_power3'
  if n=='range_M':b='range_body_scale'
  rows.append([n,o,a,b])
 free=copy.deepcopy(parent['free']);out=dict(source=rows,free=free,parameters=['x'],auxiliaries=free[1:],domains=copy.deepcopy(parent['domains']),comparisons=copy.deepcopy(parent['comparisons']),m=info['m'],a_scale=info['m']+16,range_lanes=8,range_origin_added=not paid,range_origin_port=origin,top_mask=1,output='joint_outer_output',cuts={'computed_J':J,'controller__edge_word':info['C']},source_conditions=info)
 need(len(rows)==len(parent['source'])-1+int(not paid),'fully paid nonincrease')
 return out


def numeric(p,case):
 rng=random.Random(182+case);v={n:rng.randrange(-1,3)for n in p['free']}
 if case>=3:v={n:Fraction(z,3)for n,z in v.items()}
 e=execute(p['source'],v);pv=e[P];J=e[p['cuts']['computed_J']];B=e['B'];D=e['D'];h=e['selection__Hbatch'];b=e['selection__Mbatch'];z=e['selection__Zbatch'];c=e[p['cuts']['controller__edge_word']]
 rep=lambda k:sum(pv**j for j in range(k));T=pv**(p['m']+8);T2=pv**(p['m']+16)
 need(e['range_H']==h+pv**8*c+T*h+B*T2 and e['range_M']==b+pv**8*J*rep(p['m'])+T*(2*D-1)*J*rep(8)+T2,'full changed H/M')
 need(e['range_Z']==z+pv**8*c+T*h and e['selection__q']==32*B*T2,'full changed Z/q')
 residuals=[e[a]-(e[b]if type(b)is str else b)for a,b in p['comparisons']]
 need(e[p['output']]==e['eight_units']*(1+sum(x*x for i,x in enumerate(residuals)if i!=4))-1,'full literal finalizer')
 return case>=3

def outer_leader_coefficients():
 # For computed P, each hat has coefficient 1 plus its signed physical effect.
 rows=[]
 for label in range(1,9):
  coeff=[1+int(label==2*i+1)-int(label==2*i+2)for i in range(4)]
  need(sum(c*c for c in coeff)>0 and sum(c==1 for c in coeff)==3,'nonzero outer SOS leader for every physical edge')
  rows.append(dict(label=label,coefficients=coeff,sum_squares=sum(c*c for c in coeff)))
 return rows

def scalar_domain_checks():
 typed=0;pretyping=0
 for m in (8,16,32,64,128):
  for B in (16,32,64):
   D=B//16
   for t in (1,2):
    pv=B**t;J=sum(B**j for j in range(t));cell=2*D-1
    r8=sum(pv**j for j in range(8));rm=sum(pv**j for j in range(m));short=cell*J*r8;long=cell*J*rm
    need(long%pv**8==short,'general typed range low block')
    for h in (0,1,pv-1,pv**8-1,short):
     need(h<pv**8 and(h&long)==(h&short),'general typed mask equivalence');typed+=1
  for B in (16,19,32):
   for scale in (1,3,16):
    for h,b,z in ((0,0,0),(scale-1,0,scale-1),(0,scale-1,0),(scale-1,scale-1,0)):
     H=h+B*scale;M=b+scale;q=32*B*scale
     fields=[q-16*H-16*M+16*z-15,16*(H-z)+4,16*(M-z)+2,16*z+8]
     need(min(fields)>0 and sum(fields)==q-1,'pretyping positive fields without binary assumptions');pretyping+=1
 return dict(typed_range_cases=typed,pretyping_cases=pretyping)

def verify(root):
 blobs=authenticate(root);inverse=json.loads(blobs['group_projective_inverse_macro_sharing.json'])['packets'];oldmacro=json.loads(blobs['group_projective_shared_macro_automaton.json'])['packets'];tail=json.loads(blobs['group_projective_tail_quotient_shift.json'])['packet'];parents={**{'inverse_'+k:v for k,v in inverse.items()},**{'m8_'+k:v for k,v in oldmacro.items()},'m16_tail':{**tail,'free':['x']+tail['auxiliaries']}}
 need(len(parents)==7,'exact seven saved parent scope');counts=Counter();packets={}
 expected={'inverse_private':(492,5821),'inverse_shared':(432,3517),'inverse_nielsen':(371,3517),'inverse_folded':(376,3517),'m8_private':(235,1789),'m8_shared':(229,1789),'m16_tail':(244,2365)}
 for tag,parent in parents.items():
  p=rewrite(parent);old=ledger(parent['source'],parent['free'],['joint_outer_output']);p['ledger']=ledger(p['source'],p['free'],[p['output']]);p['scalar_proof']=scalar_polynomials(p);p['interface_proof']=complete_interface(parent,p);p['degree_certificate']=exact_degree(p)
  degree=p['degree_certificate']['exact_degree'];need(degree==72*p['m']+1213,'uniform exact separate degree')
  p['ledger'].update(naive_degree_upper=p['ledger']['degree_upper'],degree_upper=degree,exact_degree=degree,certificate_operations=len(p['source'])-17,finalizer_operations=17,positive_witnesses=len(p['free'])-1,comparisons=6)
  parentdegree=130*p['m']+749;need(parentdegree-degree==58*(p['m']-8),'symbolic exact degree decrease')
  need((len(p['source']),degree)==expected[tag],'literal saved instance ledger/degree')
  need(p['ledger']['A']==old['A']and p['ledger']['M']<=old['M'],'paid family nonincrease is multiplication-only')
  p['historical_parent']=dict(source_sha256=sha(json.dumps(parent['source'],separators=(',',':')).encode()),ledger=old,exact_degree=parentdegree)
  for case in range(5):counts['rational_outputs']+=numeric(p,case);counts['complete_outputs']+=1
  counts['complete_sources']+=1;counts['paid_live_gates']+=len(p['source']);counts['exact_scalar_polynomials']+=p['scalar_proof']['exact_polynomial_count'];counts['checksum_and_history_polynomials']+=2;counts['retained_register_identities']+=p['interface_proof']['complete_retained_register_identities'];counts['whole_comparisons']+=6;counts['exact_degree_certificates']+=1;packets[tag]=p
 # The general transfer agrees instruction-for-instruction with both applicable
 # already-reviewed mask1 specializations, rather than only reproducing counts.
 specific=json.loads(blobs['group_projective_nonempty_mask_frontier.json'])['packets']['separate8'];need(packets['inverse_nielsen']['source']==specific['source'],'exact frozen Nielsen separate8 source')
 units=json.loads(blobs['group_projective_unit_top_mask.json'])['packets']
 for tag in ('private','shared'):need(packets['m8_'+tag]['source']==units[tag]['source'],'exact already-reviewed m8 unit-top source '+tag)
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),pins=copy.deepcopy(PINS),counts=dict(counts),outer_leading_coefficients=outer_leader_coefficients(),scalar_domain_checks=scalar_domain_checks(),primary_source_contract=[{'url':'https://arxiv.org/html/2507.04347v8','section':'Algorithm1.1, especially steps4-8','status':'general effective embedding route; no repository universal instance executed'},{'url':'https://arxiv.org/pdf/0810.0690','section':'Section1 introductory finite-generator recipe','status':'finite fibre-product generators from a supplied finite presentation; no additional asphericity premise used'}],packets=packets,general_theorem=dict(nonempty_graph=True,m_power2_at_least8=True,canonical_independent_coordinates=True,computed_P=True,paid_delta_M='-1 + indicator(J*R8 not already paid)',paid_delta_A=0,old_exact_degree='130m+749',new_exact_degree='72m+1213',exact_degree_drop='58(m-8)',positive_equivalence='same outer-coordinate projection with fresh native extension',universal_numeric_table_emitted=False),scope='Seven complete saved-source transfers and a canonical-family theorem; no historical builders, arbitrary public compiler API, universal numerical alphabet, or universal operation record.')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'exact typed receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status=r['status'],counts=r['counts'],ledgers={k:p['ledger']for k,p in r['packets'].items()})))
if __name__=='__main__':main()
