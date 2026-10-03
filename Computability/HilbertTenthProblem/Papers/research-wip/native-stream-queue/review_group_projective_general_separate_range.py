#!/usr/bin/env python3
"""Independent seven-source separate-range audit, without author execution."""
import argparse,ast,hashlib,json
from pathlib import Path
from collections import Counter
if not __debug__:raise RuntimeError('Run without -O')
STEM='group_projective_general_separate_range'
AUTHOR_PINS={'.py':'7da26e02d657f53fc6f27977d92065f15a5769533e27489d73ecd810c327f49c','.json':'23c18690cb114bfc4a0290b89383a4922ac3d32f55aa4b8dc60d05db5840ae2f','.md':'2e0744fd1aad96cc3a1e94ad47237e3c81f2d73705dca72998daf422cf2c3614'}
P_NAME='controller__geometry_power'
FACTORS=('first_unit','selection__R15','selection__P17','index_unit','linear_unit','strong_unit','joint_bound_unit')
PINS={'group_macro_automaton_sharing.py': 'f9d660c3309c030c98c8209f2b8a708a6731eedf62234d459ed4fa3f1db2af48', 'group_macro_automaton_sharing.json': '8e7044b66bebbacc0f89721807369607146b57bb67b14d1ddb9c4e05586a681b', 'group_macro_automaton_sharing.md': 'e253a396f999e8045bb1c4ee223602907f8ea003b7b7f3d93218cb425ffd5585', 'group_projective_label_aligned_lanes.py': 'cbecb51a164f7e4272a293fc2cb6e549838ec153b693399487e3ee0b4dd8c9a5', 'group_projective_label_aligned_lanes.json': '232fbc5d9409da72f7f8b0335316920c93cb435bbcbb43ce122b3b8c17477008', 'group_projective_label_aligned_lanes.md': '66221327c058b335febda310bb81b656b7c7095fb4463d633f60de9cd8213edb', 'group_projective_tail_quotient_shift.py': '08248ad763113a6a2e60168edfd058b92be4e14b2f7932fa1be66eb406a70610', 'group_projective_tail_quotient_shift.json': 'a422e7a65df26e626f3c36f97a53a68805b86806be3dc35d35e7d49a17b80b27', 'group_projective_tail_quotient_shift.md': 'a1e1e67df618f6f809c2e85a409509b288337f62cd1af35cfc6ca950e0efa92a', 'group_projective_idle_free_paths.md': '0cc8b21be7fca0cc5763ba3862f6888f94669259ca26beb0050cd5f8ef1ec9e9', 'group_projective_reindexed_edge_geometry.md': 'ceadd45bebece376f9cbaa5e7be1740f35510a55211819376fa335ad719152d3', 'group_sparse_macro_flow.py': '74604c1a9d1071a823e0df3388d2c89eb639cf3e088a39fa7fff3eae5113238a', 'group_sparse_macro_flow.md': '4e4356902a52de1464c91ac5aea2a654900492b74ee252d9ea22a34e5dd6febc', 'group_projective_shared_flow_target.py': 'eea982ef140ac046f9fe857747fdde82a51bedc78f22306558941ab839eeacf0', 'group_projective_shared_flow_target.md': '17bc108499565d3cbc5a6c55ca9395693c8fcce5c72069f5080560702424d1e4', 'group_projective_shared_selector_pack.md': 'b29225304b4a3b96c922df5645ca7060adc60c3074ed20e561a8e074dc411d66', 'group_projective_port_bias_folding.md': 'e699bb645378ced31c62dd9bb702eb6ed0ea93be8b6ee91e1cdc859b27e3c706', 'group_projective_zero_mortality6.md': 'c0f3cb53d8a189dd7b98e0deb892a75e64426e8ac480ee049f945ed09e896bc2', '../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md': '47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b', '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', 'group_projective_coupled_linear_unit.md': '15fa0737a82996a8ea5c28aa62cbbe798ac5e06e4a3323c4dcaa01c9cd6286c7', 'group_projective_joint_bound_unit.md': '3f33f4d7c04137409688b011859578924a4d1571d46d37bf1ca7ebd81a230a1e', 'group_projective_joint_first_norm.md': 'da7f6baaedaecae3166cfed050d2e913d26b280cc3332ca04bf0e8983417e9cb', 'group_projective_output_bound_obstruction.md': 'b478f73d003a62ed530ba329c01f875be7a5da2202b746d89ccd50f8f50aa56b', 'group_projective_padded_program_margin.md': 'a4ad4487f682d250f3a9ae84cc8f4182b21d2e216fa0d53624f7368abd028952', 'group_projective_product_radix_scale.json': '1403987d49c3613b3ca6cdc1f1794d16199af9020c9c88fd53c49981f95db9a7', 'group_projective_product_radix_scale.md': 'f342dbc1da849a7c74cc7043becad6d218582adeefffa55dec558a28b1e47b39', 'group_projective_product_radix_scale.py': 'd33e8aa3bff7559c72768be7116f0328ebad0cf65190115101457a71a0e25965', 'group_projective_shifted_X_quotient.md': '4f76dda46f9385a769da0c809292b466d352be2a6f2d39c5e70519bdeda37e00', 'group_projective_strong_unit_product.md': '06978175efe47f59bf497f8882b3138692abead1458c58de6a53af92b4f83605', 'native_controller_binary_selector56.md': '97fcdc7188f968f2ac3e315249b0e0a15dcc787c10451924ad3f2551c8bb376c', 'group_projective_shared_macro_automaton.json': '284da792cce620169ebca9cae7ee77488b56fe0f68c47cf12059af5d0e980497', 'group_projective_shared_macro_automaton.md': '5933851785599c3c83bbddc28f1dbe2e43c7db17ed256a87a5dd293117bc9eb6', 'group_projective_shared_macro_automaton.py': '2cbbc82d18e0e175d3c7f44707fdc16c2bf899aaad5deafa44c0975cf0b96bf7', 'group_projective_inverse_macro_sharing.py': 'c23f1cff1ccf1d7ad004c29670cf08926e05790eb02baeaddf4c691bd9b02957', 'group_projective_inverse_macro_sharing.json': '4f02c041fcb8db78849c5d95c2b23cabab615c88e42ef648f9c8377d876fb09b', 'group_projective_inverse_macro_sharing.md': '8ba6acdfcbf932c2814b44de590ac456ae223d7d686d19d72d54e17e2e0c8ac0', 'group_projective_unit_top_mask.py': '1b96e1908e35f95598230c658d42d83d83cb24dc1dea48726f948353011738d3', 'group_projective_unit_top_mask.json': 'a7544f40ce74ee67088fbfa1d753a04cf921cac6f04486dd7f6d83a39befa2e2', 'group_projective_unit_top_mask.md': 'e0898d1fc20f2f4c1abff21d33f90382aeac4f6b24c648624f0e54d59a3619b2', 'group_projective_nonempty_mask_frontier.py': '10d38ebaeac82c9e8ba39eefac3d03a9092e08035a8b5f0aef8dd30f78992cd5', 'group_projective_nonempty_mask_frontier.json': '589337541f83814e8d546d919caf2ab4a8977b76583f0110b9509e812521b655', 'group_projective_nonempty_mask_frontier.md': 'a0baff1b8223955f7d7682f31f8a8d1d62abe5bf72bce251e750207937fbce54', 'review_group_projective_nonempty_mask_frontier.py': '66a0b8d1d8a55fcb9fda66747440850fe88b387e85e2f1ba33a8bc525770fa09', 'review_group_projective_nonempty_mask_frontier.json': 'd4c7bd3b75bf44f26a998ad9a1057bb0e1389ac12a98e851522339414f92414a', 'review_group_projective_nonempty_mask_frontier.md': '799124b3a456dcded7d9b15ac80d61a4547ce8162fce859000b3fd2937c0754b', 'group_commutator_universal_substrate.py': '2eff5df85eebf91c09cc89de9b00a836241b27a5f45081f8954b430e02d68085', 'group_commutator_universal_substrate.json': '5ce9fdc18af091d4f16a9b12a579d0ca6528edd2bf262cad73a6c1554d7903e4', 'group_commutator_universal_substrate.md': '64a31c4ef76a1684b51f035735d817df53639c070d16c221eb9ee2095e51bf6a', 'group_projective_padded_program_margin.py': 'cd985af757b8354a6d8e78db6854a81d07279bdf731c029e6b0c67465afbc576', 'group_projective_padded_program_margin.json': 'fe016602afe3a09e43546f3c8726caefc1149047def8eb71ed38582f6e7deb20', 'group_projective_zero_mortality6.py': 'f3a28ea5244500533cc83d95a834e30e2748bb22461bcfb0e7016dc8259f96ad', 'group_projective_zero_mortality6.json': '035434a110f51804344a3a9110d5892633c8e75d7eceb4b78f685b3d83e10ce8'}
def require(x, message):
 if not x: raise ValueError(message)
def sha(b): return hashlib.sha256(b).hexdigest()
def typed(a,b):
 if type(a) is not type(b): return False
 if isinstance(a,dict): return a.keys()==b.keys() and all(typed(a[k],b[k]) for k in a)
 if isinstance(a,list): return len(a)==len(b) and all(typed(x,y) for x,y in zip(a,b))
 return a==b
# Independent sparse polynomial arithmetic for the complete outer cones.
def const(x): return {():x} if x else {}
def atom(x): return {((x,1),):1}
def add(a,b,sign=1):
 z=dict(a)
 for m,c in b.items():
  z[m]=z.get(m,0)+sign*c
  if not z[m]: del z[m]
 return z
def mul(a,b):
 z={}
 for m,c in a.items():
  for n,d in b.items():
   e=dict(m)
   for v,k in n:e[v]=e.get(v,0)+k
   mon=tuple(sorted(e.items()));z[mon]=z.get(mon,0)+c*d
 return {m:c for m,c in z.items() if c}
def power(a,n):
 z=const(1)
 while n:
  if n&1:z=mul(z,a)
  a=mul(a,a);n//=2
 return z
def total(xs):
 z={}
 for x in xs:z=add(z,x)
 return z
def scale(n,p): return mul(const(n),p)
def value(x,e): return e[x] if isinstance(x,str) else const(x)
def poly_cone(rows,free,target,cuts):
 defs={n:(o,a,b) for n,o,a,b in rows};env={n:atom(n) for n in free};env.update(cuts)
 def go(n):
  if type(n) is int:return const(n)
  if n not in env:
   op,a,b=defs[n];a,b=go(a),go(b);env[n]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
  return env[n]
 return go(target)
def run(rows,v):
 e=dict(v)
 for n,o,a,b in rows:
  a=e[a] if isinstance(a,str) else a;b=e[b] if isinstance(b,str) else b
  e[n]=a*b if o=='*' else a+b if o=='+' else a-b
 return e
def account(p):
 free=p['free'];degree={n:1 for n in free};defs={};c=Counter()
 require(len(free)==len(set(free)),'unique input leaves')
 for n,o,a,b in p['source']:
  require(n not in degree and o in ('+','-','*'),'fresh legal gate')
  require(all(type(t) is int or type(t) is str and t in degree for t in (a,b)),'closed exact-type schedule')
  da,db=(degree.get(t,0) for t in (a,b));degree[n]=da+db if o=='*' else max(da,db)
  defs[n]=(a,b);c['M' if o=='*' else 'A']+=1
 seen=set();used=set();stack=[p['output']]
 while stack:
  n=stack.pop()
  if type(n) is int:continue
  if n not in defs:used.add(n)
  elif n not in seen:seen.add(n);stack.extend(defs[n])
 require(seen==set(defs) and used==set(free),'all gates and supplied leaves live')
 ans=dict(operations=len(defs),M=c['M'],A=c['A'],degree_upper=degree[p['output']])
 require(ans==p['ledger'],'literal full ledger')
 return ans
# Exact ring-expression DAG: addition is a sparse linear combination of
# nonlinear node IDs, sufficient for D=(D-u)+u without a proof cut.
class Ring:
 def __init__(self):self.memo={};self.next=1
 def leaf(self,key):
  if key not in self.memo:self.memo[key]=self.next;self.next+=1
  return ((self.memo[key],1),)
 def number(self,n):return ((0,n),) if n else ()
 def op(self,o,a,b):
  if o in ('+','-'):
   z=dict(a)
   for k,v in b:z[k]=z.get(k,0)+(v if o=='+' else -v)
   return tuple(sorted((k,v) for k,v in z.items() if v))
  if not a or not b:return ()
  if len(a)==1 and a[0][0]==0:return tuple((k,a[0][1]*v) for k,v in b)
  if len(b)==1 and b[0][0]==0:return tuple((k,b[0][1]*v) for k,v in a)
  return self.leaf(('*',tuple(sorted((a,b)))))
 def execute(self,p,env):
  e=dict(env)
  for n,o,a,b in p['source']:
   av=e[a] if isinstance(a,str) else self.number(a);bv=e[b] if isinstance(b,str) else self.number(b)
   e[n]=self.op(o,av,bv)
  return e



def authenticate(root):
 def read(n,h):
  p=root/n
  if not p.exists():p=Path(__file__).resolve().parent/n
  b=p.read_bytes();require(sha(b)==h,'exact pinned bytes '+n);return b
 blobs={n:read(n,h) for n,h in PINS.items()};author={ext:read(STEM+ext,h) for ext,h in AUTHOR_PINS.items()};receipt=json.loads(author['.json'])
 require(len(blobs)==54 and receipt['pins']==PINS and receipt['source_sha256']==sha(author['.py']),'entire saved inventory and selfsource')
 tree=ast.parse(author['.py']);pins=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(v,ast.Name) and v.id=='PINS' for v in n.targets))
 require(pins==PINS,'literal author source inventory')
 return receipt,blobs

def parents_from(blobs):
 inverse=json.loads(blobs['group_projective_inverse_macro_sharing.json'])['packets'];macro=json.loads(blobs['group_projective_shared_macro_automaton.json'])['packets'];tail=json.loads(blobs['group_projective_tail_quotient_shift.json'])['packet']
 return {**{'inverse_'+k:v for k,v in inverse.items()},**{'m8_'+k:v for k,v in macro.items()},'m16_tail':dict(tail,free=['x']+tail['auxiliaries'])}

def own_rewrite(parent):
 rows=parent['source'];defs={r[0]:r for r in rows};pp=atom('P')
 J,Rm=defs['controller__origin_mask'][2:];Pm=defs['joint_scale'][3]
 power_poly=poly_cone(rows,parent['free'],Pm,{P_NAME:pp})
 require(len(power_poly)==1,'pure single-monomial actual Pm')
 mon,coeff=next(iter(power_poly.items()));require(coeff==1 and len(mon)==1 and mon[0][0]=='P','exact pure P power');m=mon[0][1]
 require(m>=8 and m&(m-1)==0,'actual padded power2 lane count')
 for port,want in [('controller__lane_power3',power(pp,8)),('controller__lane_repunit2',total(power(pp,i) for i in range(8))),(Rm,total(power(pp,i) for i in range(m))),('joint_scale',power(pp,m+8)),('range_body_scale',power(pp,2*m+8))]:
  require(poly_cone(rows,parent['free'],port,{P_NAME:pp})==want,'actual paid power/repunit '+port)
 require(defs['joint_scale']==['joint_scale','*','controller__lane_power3',Pm],'retained Pm consumer')
 require(defs['range_body_scale']==['range_body_scale','*','joint_scale',Pm],'old complete scale')
 require(defs['range_mask8']==['range_mask8','*','range_cell','controller__origin_mask'],'old reused range')
 require(defs['range_Bminus_shift']==['range_Bminus_shift','*','range_body_scale',2],'old literal topmask2 multiplication')
 require([r[0] for r in rows if 'range_Bminus_shift' in r[2:]]==['range_M'],'strict topmask producer privacy')
 paid=[n for n,o,a,b in rows if o=='*' and ((a,b)==(J,'controller__lane_repunit2') or (b,a)==(J,'controller__lane_repunit2'))]
 origin=paid[0] if paid else 'range_origin8';new=[]
 for row in rows:
  n,o,a,b=row
  if n=='range_Bminus_shift':continue
  if n=='range_mask8':
   if not paid:new.append([origin,'*',J,'controller__lane_repunit2'])
   b=origin
  elif n=='range_body_scale':b='controller__lane_power3'
  elif n=='range_M':b='range_body_scale'
  new.append([n,o,a,b])
 return new,dict(m=m,J=J,C=defs['joint_edge_shift'][3],origin=origin,added=not paid,Pm=Pm,Rm=Rm)

def full_account(p):
 ops=Counter(o for n,o,a,b in p['source']);degrees={n:1 for n in p['free']}
 for n,o,a,b in p['source']:degrees[n]=degrees.get(a,0)+degrees.get(b,0) if o=='*' else max(degrees.get(a,0),degrees.get(b,0))
 q=dict(source=p['source'],free=p['free'],output='joint_outer_output',ledger=dict(operations=len(p['source']),M=ops['*'],A=ops['+']+ops['-'],degree_upper=degrees['joint_outer_output']))
 return account(q)

def scalar_check(parent,child,info):
 rows=child['source'];free=child['free'];m=info['m'];pp,jj,dd,bb,hb,mb,zb,cc=[atom(n) for n in ('P','J','D','B','Hb','Mb','Zb','C')]
 masks=mul(jj,total(power(pp,i) for i in range(m)));mask8=mul(jj,total(power(pp,i) for i in range(8)))
 T=power(pp,m+8);T2=power(pp,m+16);range_mask=mul(add(scale(2,dd),const(1),-1),mask8)
 wanted={'controller__origin_mask':masks,info['origin']:mask8,'range_mask8':range_mask,'joint_scale':T,'range_body_scale':T2,'range_H':total([hb,mul(power(pp,8),cc),mul(T,hb),mul(bb,T2)]),'range_M':total([mb,mul(power(pp,8),masks),mul(T,range_mask),T2]),'range_Z':total([zb,mul(power(pp,8),cc),mul(T,hb)]),'selection__q':scale(32,mul(bb,T2))}
 cuts={P_NAME:pp,info['J']:jj,'D':dd,'B':bb,'selection__Hbatch':hb,'selection__Mbatch':mb,'selection__Zbatch':zb,info['C']:cc}
 for name,expected in wanted.items():require(poly_cone(rows,free,name,cuts)==expected,'expanded complete scalar '+name)
 hats=[n for n in free if n.startswith('controller__edge_hat')];require(1<=len(hats)<=m,'nonempty independent edge hats')
 require(poly_cone(rows,free,info['J'],{})==total(add(atom(n),const(1),-1) for n in hats),'complete hatted checksum')
 history=total(mul(atom('H'+str((i//2)^1)),power(pp,i)) for i in range(8))
 require(poly_cone(rows,free,'selection__Hbatch',{P_NAME:pp})==history,'actual physical history order and highest H2 lane')
 defs={r[0]:r for r in rows};alpha=defs['history__input_product'][2];gamma=defs['history__u'][3]
 require(type(alpha)is int and alpha>0 and type(gamma)is int and gamma>0,'fixed positive ordinary affine loader')
 require(defs['D']==['D','+','history__u','height_slack'] and defs['B']==['B','*',16,'D'] and 16*(alpha+gamma+1)>m,'paid actual margin before native typing')
 require(defs['controller__geometry_power']==[P_NAME,'+','controller__geometry_product',1] and defs['controller__geometry_product']==['controller__geometry_product','*','controller__cell_minus1',info['J']] and defs['controller__cell_minus1']==['controller__cell_minus1','-','B',1],'actual computed P relation')
 require(child['free']==parent['free'] and child['comparisons']==parent['comparisons'],'complete coordinates and equations retained')
 require(child['a_scale']==m+16 and child['range_lanes']==8 and child['top_mask']==1 and child['range_origin_added']==info['added'] and child['range_origin_port']==info['origin'],'actual range metadata')
 # All surviving computed expressions agree under the three proved changed
 # interface ports; this is intentionally not same-tuple polynomial equality.
 ring=Ring();leaves={v:ring.leaf(('free',v)) for v in free};changed={'range_mask8','range_body_scale','range_M'};formal={v:ring.leaf(('changed',v)) for v in changed}
 def ev(source):
  e=dict(leaves)
  for n,o,a,b in source:
   get=lambda v:e[v] if type(v)is str else ring.number(v)
   e[n]=formal[n] if n in formal else ring.op(o,get(a),get(b))
  return e
 old=ev(parent['source']);new=ev(rows);common=(set(old)&set(new))-set(free)
 require(all(old[n]==new[n] for n in common),'all retained computed expressions under the exact interface')
 require(old['joint_outer_output']==new['joint_outer_output'],'whole output under changed interface')
 final=[r for r in parent['source'] if r[0].startswith('joint_outer_')]
 require(len(final)==17 and final==[r for r in rows if r[0].startswith('joint_outer_')],'entire paid literal finalizer')
 return dict(scalar_polynomials=len(wanted),checksum_history_polynomials=2,static_registers=len(common),whole_interface_identity=True)

def degrees(p):
 defs={n:(o,a,b) for n,o,a,b in p['source']};X,A,C,G,H='selection__wn2','selection__R12','selection__R10a','selection__gam','selection__a4m5'
 required={'selection__R15':('-','selection__L15','selection__Ac2'),'selection__L15':('*','selection__R14','selection__R14'),'selection__R14':('+','selection__D1',G),'selection__D1':('+',X,'selection__cam2'),'selection__cam2':('*',C,A),'selection__A':('+','selection__a_square',H),'selection__a_square':('*',A,A),H:('+','selection__a4',3),'selection__a4':('*',4,A),G:('*','selection__ga',H),'selection__Ac2':('*','selection__A','selection__c2'),'selection__c2':('*',C,C)}
 require(all(defs[n]==row for n,row in required.items()),'guarded exact main-norm cone')
 for name in ('selection__tau_gap','selection__ga','selection__eta','selection__zeta','selection__i','selection__f','selection__h','selection__odd_half','H0','H1','H2','H3','x','height_slack'):require(name in p['free'],'independent leading-form coordinate '+name)
 m=p['m'];Q=2*m+33;F=2*m+31;R=3*Q+F;expected=[R+Q+4,2*R+Q+5,6*Q+14,R+2,R+2,2*R+4,2]
 require(sum(expected)+6==72*m+1213 and (130*m+749)-(sum(expected)+6)==58*(m-8),'general degree algebra')
 proofs=[]
 for prime in (2147483647,1000000007):
  weights={v:1+int(sha((v+':separate-independent').encode()),16)%113 for v in p['free']};env={v:(1,w) for v,w in weights.items()}
  def plus(a,b,s=1):
   d=max(a[0],b[0]);return d,((a[1] if a[0]==d else 0)+s*(b[1] if b[0]==d else 0))%prime
  def times(a,b):return a[0]+b[0],a[1]*b[1]%prime
  for n,o,a,b in p['source']:
   av=env[a] if type(a)is str else (0,a%prime);bv=env[b] if type(b)is str else (0,b%prime)
   if n=='selection__R15':
    vv=plus(env[X],env[G]);ac=times(env[A],env[C]);env[n]=plus(times(vv,plus(vv,times((0,2),ac))),times(env[H],times(env[C],env[C])),-1)
   else:env[n]=times(av,bv) if o=='*' else plus(av,bv,1 if o=='+' else -1)
  require([env[n][0] for n in FACTORS]==expected,'seven actual degree bounds')
  require(env['joint_outer_positive'][0]==6 and env['joint_outer_output'][0]==sum(expected)+6 and env['joint_outer_output'][1]!=0,'complete nonzero top coefficient attains bound')
  proofs.append(dict(prime=prime,nonzero_top=env['joint_outer_output'][1]))
 return dict(exact_degree=sum(expected)+6,factor_degrees=expected,coefficient_certificates=proofs,weights=weights)

def general_checks():
 rows=[]
 for label in range(1,9):
  vec=[1+(label==2*i+1)-(label==2*i+2) for i in range(4)]
  require(vec.count(1)==3 and sum(v*v for v in vec)>0,'general nonempty-edge outer leader')
  rows.append(vec)
 # Exact low-block identity for all formal m>=8: the remainder consists
 # solely of P^i terms i>=8, even for non-power2 m. The source restricts m.
 pp=atom('P');coef=atom('L');cases=0
 for m in (8,16,32,64,128):
  delta=add(mul(coef,total(power(pp,i) for i in range(m))),mul(coef,total(power(pp,i) for i in range(8))),-1)
  require(all(dict(mon).get('P',0)>=8 for mon in delta),'exact multiple P8 range difference')
  for B in (16,32):
   for t in (1,2):
    P=B**t;J=(P-1)//(B-1);D=B//16;L=(2*D-1)*J
    short=L*sum(P**i for i in range(8));long=L*sum(P**i for i in range(m))
    require(L<P and long%P**8==short,'typed low block exact arithmetic')
    for h in (0,1,P-1,P**8-1,short):require((h&long)==(h&short),'bounded typed AND equality');cases+=1
 return dict(outer_edge_vectors=rows,typed_low_block_cases=cases,range_difference_uniform_proof='L*sum(P^i,i=8..m-1), divisible by P^8; mask digit L<P excludes carries')

RT=(2,3,6,7);BM=(1,5)*5;AM=RT+BM

def path(edges,word):
 active={0:[]}
 for label in word:
  following={}
  for index,(a,b,l) in enumerate(edges):
   if l==label and a in active and b not in following:following[b]=active[a]+[index]
  active=following
 require(0 in active,'actual hub loop')
 return active[0]

def outer_fixture(p,x):
 u=24*x+13;e=(u-1)//5;word=RT+BM*e
 require(word==AM+BM*(e-1) and e>=1,'literal accepted original macro decomposition')
 choices=path(p['edges'],word);state=[1,u,1,u];before=[]
 for l in word:
  before.append(list(state));j=(l-1)//2;state[j]+=(1 if l%2 else -1)*state[j^1]
 require(state==[0,1,0,1] and len(word)==48*x+28,'complete genuine paired trajectory')
 D=128 if x==2 else 256;B=16*D;P=B**len(word);J=(P-1)//(B-1)
 require(D>u and D>1+max(abs(v) for st in before+[state] for v in st),'height/range sufficient margin')
 radixpowers=[B**i for i in range(len(word))];v={'x':x,'height_slack':D-u}
 for j in range(4):v['H'+str(j)]=sum((D-1+st[j])*b for st,b in zip(before,radixpowers))
 for l in range(1,9):v['Zhat'+str(l-1)]=1+sum((D-1+st[((l-1)//2)^1])*b for st,b,label in zip(before,radixpowers,word) if label==l)
 for edge in range(len(p['edges'])):v['controller__edge_hat'+str(edge+1)]=1+sum(b for i,b in zip(choices,radixpowers) if i==edge)
 v['selection__bound_global']=P+1-sum(v['H'+str(j)] for j in range(4))-sum(v['Zhat'+str(j)] for j in range(8))
 require(min(v.values())>0 and B>p['m'],'actual positive outer witness coordinates')
 definitions={n:(o,a,b) for n,o,a,b in p['source']};env=dict(v)
 def get(n):
  if type(n)is int:return n
  if n not in env:
   o,a,b=definitions[n];a,b=get(a),get(b);env[n]=a*b if o=='*' else a+b if o=='+' else a-b
  return env[n]
 require(get(P_NAME)==P and get(p['cuts']['computed_J'])==J,'literal paid P/repunit source')
 require(all(get(a)==get(b) for i,(a,b) in enumerate(p['comparisons']) if i!=4),'all five true outer equations')
 require(get('joint_bound_unit')==1,'true joint factor')
 H,M,Z=[get(n) for n in ('range_H','range_M','range_Z')];q=get('selection__q');Q=q//16
 require(H&M==Z and 0<=max(H,M,Z)<Q and q==32*B*P**(p['m']+16),'actual whole joined AND and paid product scale')
 fields=[16*(Q-H-M+Z)-15,16*(H-Z)+4,16*(M-Z)+2,16*Z+8]
 require(min(fields)>0 and sum(fields)==q-1 and all(fields[i]&fields[j]==0 for i in range(4) for j in range(i)),'positive disjoint truth fields')
 return dict(x=x,u=u,D=D,B=B,duration=len(word),edge_path=choices,q_bit_length=q.bit_length(),all_outer_equations=True,full_AND=True,native_Pell_zero_materialized=False)

def verify(root):
 saved,blobs=authenticate(root);parents=parents_from(blobs);require(set(saved['packets'])==set(parents) and len(parents)==7,'exact seven source selections')
 results={};fixtures=[]
 expected={'inverse_private':(492,191,301,5821),'inverse_shared':(432,178,254,3517),'inverse_nielsen':(371,150,221,3517),'inverse_folded':(376,147,229,3517),'m8_private':(235,98,137,1789),'m8_shared':(229,97,132,1789),'m16_tail':(244,103,141,2365)}
 for tag,parent in sorted(parents.items()):
  p=saved['packets'][tag];rows,info=own_rewrite(parent);require(rows==p['source'],'independently rebuilt complete literal source '+tag)
  old=full_account(parent);new=full_account(p);interface=scalar_check(parent,p,info);degree=degrees(p)
  require((new['operations'],new['M'],new['A'],degree['exact_degree'])==expected[tag],'actual complete cost and exact degree')
  require(new['M']-old['M']==-1+int(info['added']) and new['A']==old['A'],'exact whole paid delta')
  require(p['historical_parent']['source_sha256']==sha(json.dumps(parent['source'],separators=(',',':')).encode()) and p['historical_parent']['ledger']==old,'actual source/ledger provenance')
  ledger=p['ledger'];require(all(ledger[k]==new[k] for k in ('operations','M','A')) and ledger['naive_degree_upper']==new['degree_upper'] and ledger['degree_upper']==ledger['exact_degree']==degree['exact_degree'],'truthful exact-versus-naive degree ledger')
  require(ledger['positive_witnesses']==len(p['free'])-1 and p['auxiliaries']==p['free'][1:] and p['parameters']==['x'] and p['domains']==parent['domains'],'unchanged complete positive interface')
  require(ledger['certificate_operations']==new['operations']-17 and ledger['comparisons']==6 and ledger['finalizer_operations']==17,'complete finalizer charge')
  results[tag]=dict(m=info['m'],ledger=new,exact_degree=degree['exact_degree'],degree=degree,source_delta=dict(M=new['M']-old['M'],A=new['A']-old['A']),interface=interface)
  if tag.startswith('inverse_'):
   actual=dict(p,edges=parent['edges'])
   for x in (2,7):fixtures.append(dict(graph=tag,**outer_fixture(actual,x)))
 require(saved['packets']['inverse_nielsen']['source']==json.loads(blobs['group_projective_nonempty_mask_frontier.json'])['packets']['separate8']['source'],'frozen Nielsen exact specialization')
 for tag in ('private','shared'):require(saved['packets']['m8_'+tag]['source']==json.loads(blobs['group_projective_unit_top_mask.json'])['packets'][tag]['source'],'frozen m8 exact specialization')
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTHOR_PINS,dependency_pins=PINS,results=results,general=general_checks(),genuine_outer_fixtures=fixtures,totals=dict(authenticated_dependencies=len(PINS),full_sources=7,paid_live_gates=sum(r['ledger']['operations'] for r in results.values()),scalar_polynomials=sum(r['interface']['scalar_polynomials'] for r in results.values()),checksum_history_polynomials=14,retained_register_identities=sum(r['interface']['static_registers'] for r in results.values()),whole_interface_identities=7,whole_comparisons=42,exact_degree_certificates=14,genuine_accepting_outer_fixtures=8),scope='All seven entire saved literal sources independently rebuilt. Uniform degree proof requires the stated nonempty graph and independent canonical coordinates; finite modular attainments supplement it. Same outer-coordinate positive-zero projection with fresh native extension, not same-tuple polynomial identity/native-witness bijection. No historical/author execution, no arbitrary public API or numerical universal bound.')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.expect:require(typed(r,json.loads(a.expect.read_text())),'exact typed saved independent receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status=r['status'],totals=r['totals'],cost_degrees={k:[v['ledger']['operations'],v['exact_degree']] for k,v in r['results'].items()})))
if __name__=='__main__':main()
