#!/usr/bin/env python3
"""Smaller positive quotient offset in one saved complete group compiler.
Only the pinned default 244-gate source is emitted. General theorem in companion.
No historical Python is imported. Standard library only.
"""
import argparse,copy,hashlib,json,random
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'group_projective_product_radix_scale.py': 'd33e8aa3bff7559c72768be7116f0328ebad0cf65190115101457a71a0e25965', 'group_projective_product_radix_scale.json': '1403987d49c3613b3ca6cdc1f1794d16199af9020c9c88fd53c49981f95db9a7', 'group_projective_product_radix_scale.md': 'f342dbc1da849a7c74cc7043becad6d218582adeefffa55dec558a28b1e47b39', 'group_projective_padded_program_margin.md': 'a4ad4487f682d250f3a9ae84cc8f4182b21d2e216fa0d53624f7368abd028952', 'group_projective_shifted_X_quotient.md': '4f76dda46f9385a769da0c809292b466d352be2a6f2d39c5e70519bdeda37e00', 'group_projective_joint_first_norm.md': 'da7f6baaedaecae3166cfed050d2e913d26b280cc3332ca04bf0e8983417e9cb', 'group_projective_coupled_linear_unit.md': '15fa0737a82996a8ea5c28aa62cbbe798ac5e06e4a3323c4dcaa01c9cd6286c7', 'group_projective_strong_unit_product.md': '06978175efe47f59bf497f8882b3138692abead1458c58de6a53af92b4f83605', 'group_projective_joint_bound_unit.md': '3f33f4d7c04137409688b011859578924a4d1571d46d37bf1ca7ebd81a230a1e', 'group_projective_output_bound_obstruction.md': 'b478f73d003a62ed530ba329c01f875be7a5da2202b746d89ccd50f8f50aa56b', 'group_projective_label_aligned_lanes.md': '66221327c058b335febda310bb81b656b7c7095fb4463d633f60de9cd8213edb', 'native_controller_binary_selector56.md': '97fcdc7188f968f2ac3e315249b0e0a15dcc787c10451924ad3f2551c8bb376c', '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b', '../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md': '47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b'}
FACTORS=('first_unit','selection__R15','selection__P17','index_unit','linear_unit','strong_unit','joint_bound_unit')
def need(c,m):
 if not c:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def canonical_parent(*,root=None):
 root=Path(__file__).resolve().parent if root is None else Path(root)
 for n,h in PINS.items():need(sha((root/n).read_bytes())==h,'pin '+n)
 receipt=json.loads((root/'group_projective_product_radix_scale.json').read_text())
 rows=receipt['source'];need(len(rows)==244 and receipt['output']=='joint_outer_output','actual full parent')
 nodes={n for n,o,a,b in rows};free=sorted({v for n,o,a,b in rows for v in(a,b) if type(v)is str and v not in nodes})
 pairs=[[r[2],r[3]] for r in rows[227:] if r[1]=='-' and r[0].startswith('joint_outer_residual')]
 pairs.insert(4,['eight_units',1]);need(len(pairs)==6 and len(free)==37 and 'x' in free,'actual comparisons/free coordinates')
 return dict(source=rows,output=receipt['output'],comparisons=pairs,parameters=['x'],auxiliaries=[v for v in free if v!='x'],domains={'parameters':'positive','auxiliaries':'positive'},historical_parent_ledger=receipt['default_ledger'])

def rewrite(parent,*,root=None):
 need(exact(parent,canonical_parent(root=root)),'exact canonical parent')
 p=copy.deepcopy(parent);rows=p['source'];d={n:(o,a,b) for n,o,a,b in rows}
 expected={'shifted_native_quotient':('+','selection__w','packed_top_sum'),'selection__wn2':('*','shifted_native_quotient','selection__q'),'packed_z_product':('*','packed_q_minus','selection__F3'),'packed_q_minus':('-','selection__q',1),'selection__bs_packed':('*','packed_q_minus','packed_top_sum'),'packed_top_sum':('+','selection__padded_A','packed_middle_product'),'packed_middle_product':('*','packed_q_plus','packed_middle_sum'),'packed_q_plus':('+','selection__q',1),'packed_middle_sum':('+','selection__padded_B','packed_z_product')}
 need(all(d[n]==t for n,t in expected.items()),'literal native index/quotient cone')
 need([n for n,o,a,b in rows if 'selection__w' in(a,b)]==['shifted_native_quotient'],'sole supplied quotient consumer')
 need([n for n,o,a,b in rows if 'shifted_native_quotient' in(a,b)]==['selection__wn2'],'sole quotient addition consumer')
 seen=set(p['parameters']+p['auxiliaries'])
 for n,o,a,b in rows:
  if n=='packed_top_sum':need('selection__wn2' not in seen,'outer factor precedes X')
  seen.add(n)
 p['source']=[[n,o,a,'packed_z_product'] if n=='shifted_native_quotient' else [n,o,a,b] for n,o,a,b in rows]
 p['parent_pins']=copy.deepcopy(PINS)
 p['quotient_projection']={'parent':'group_projective_product_radix_scale','signed_pullback':'w_parent=w+packed_z_product-packed_top_sum','positive_parent_embedding':'w_child=w_parent+packed_top_sum-packed_z_product','same_coordinate_polynomial_identity':False,'all_value_identity_under_signed_pullback':True,'positive_zero_bijection':True,'positive_reverse_only_after_native_recovery':True,'X_gt_r_assumed_in_bootstrap':False}
 p['source_scope']='Exactly the pinned default ten-letter table, alpha24/beta12, controller range reuse, computed P. The general fixed-table proof does not instantiate a numerical universal alphabet.'
 p['ledger']=ledger(p);p['degree_certificate']=degree_certificate_internal(p)
 return p

def build(*,root=None):return rewrite(canonical_parent(root=root),root=root)
def checked(p,*,root=None):
 e=build(root=root);need(exact(p,e),'canonical child');return e

def execute(rows,values):
 e=dict(values)
 for n,o,a,b in rows:
  a=e[a] if type(a)is str else a;b=e[b] if type(b)is str else b
  e[n]=a*b if o=='*' else a+b if o=='+' else a-b
 return e

def check_values(p,v,signed):
 need(type(signed)is bool and type(v)is dict and set(v)==set(p['parameters']+p['auxiliaries']),'exact assignment')
 need(all(type(x)is int for x in v.values()),'exact integer values')
 if not signed:need(min(v.values())>0,'all supplied coordinates positive')
def evaluate(p,v,*,signed=False,root=None):
 p=checked(p,root=root);check_values(p,v,signed);return execute(p['source'],v)[p['output']]
def integer_pullback(p,v,*,root=None):
 p=checked(p,root=root);check_values(p,v,True);e=execute(p['source'],v);z=dict(v);z['selection__w']+=e['packed_z_product']-e['packed_top_sum'];return z

def ledger(p):
 rows=p['source'];known=set(p['parameters']+p['auxiliaries']);deps={};c=Counter()
 for n,o,a,b in rows:
  need(type(n)is str and n not in known and o in('+','-','*') and all(type(v)is int or type(v)is str and v in known for v in(a,b)),'closed typed DAG')
  known.add(n);deps[n]=(a,b);c['M' if o=='*' else 'A']+=1
 todo=[p['output']];live=set();free=set()
 while todo:
  n=todo.pop()
  if type(n)is int:continue
  if n not in deps:free.add(n);continue
  if n not in live:live.add(n);todo.extend(deps[n])
 need(live==set(deps) and free==set(p['parameters']+p['auxiliaries']),'all paid gates and coordinates live')
 return dict(operations=len(rows),M=c['M'],A=c['A'],certificate_operations=227,finalizer_operations=17,comparisons=6,positive_witnesses=36,all_gates_live=True)

# Rigorous upper bound, with a nonzero leading coefficient over a finite field.
# All source gates use exact highest-degree operations except the explicitly
# verified main-norm cancellation identity. A nonzero residue certifies a
# nonzero integer homogeneous component, not a numeric degree heuristic.
def degree_certificate_internal(p):
 rows=p['source'];drows={n:(o,a,b) for n,o,a,b in rows}
 X,A,c,G,H='selection__wn2','selection__R12','selection__R10a','selection__gam','selection__a4m5'
 expected={'selection__R15':('-','selection__L15','selection__Ac2'),'selection__L15':('*','selection__R14','selection__R14'),'selection__R14':('+','selection__D1',G),'selection__D1':('+',X,'selection__cam2'),'selection__cam2':('*',c,A),'selection__A':('+','selection__a_square',H),'selection__a_square':('*',A,A),H:('+','selection__a4',3),'selection__a4':('*',4,A),G:('*','selection__ga',H),'selection__Ac2':('*','selection__A','selection__c2'),'selection__c2':('*',c,c)}
 need(all(drows[n]==v for n,v in expected.items()),'exact main norm expansion cone')
 # Difference of the square and Delta*c² is X²+2Xac+2XG+2acG+G²-Hc².
 prime=1000000007;rng=random.Random(0);free=sorted(p['parameters']+p['auxiliaries']);weights={n:rng.randrange(1,100) for n in free};d={n:(1,w) for n,w in weights.items()}
 def add(a,b,sign=1):
  if a[0]>b[0]:return a
  if a[0]<b[0]:return (b[0],sign*b[1]%prime)
  return (a[0],(a[1]+sign*b[1])%prime)
 def mul(a,b):return (a[0]+b[0],a[1]*b[1]%prime)
 for n,o,a,b in rows:
  av=d[a] if type(a)is str else (0,a%prime);bv=d[b] if type(b)is str else (0,b%prime)
  if n=='selection__R15':
   xx,aa,cc,gg,hh=[d[v] for v in(X,A,c,G,H)]
   terms=[mul(xx,xx),mul((0,2),mul(mul(xx,aa),cc)),mul((0,2),mul(xx,gg)),mul((0,2),mul(mul(aa,cc),gg)),mul(gg,gg),mul((0,-1),mul(hh,mul(cc,cc)))]
   z=terms[0]
   for t in terms[1:]:z=add(z,t)
  else:z=mul(av,bv) if o=='*' else add(av,bv,1 if o=='+' else -1)
  need(z[1]!=0,'all leading coefficients nonzero: '+n);d[n]=z
 need(d[p['output']]==(2829,935638906),'exact full default degree and attained top')
 need([d[n][0] for n in FACTORS]==[391,698,500,308,308,616,2],'all individual exact factor degrees')
 return dict(exact_degree=2829,upper_degree=2829,prime=prime,weights=weights,leading_coefficient_mod_prime=d[p['output']][1],factor_degrees={n:d[n][0] for n in FACTORS},all_gate_leaders_nonzero=True,general_nonempty_family_degree='73+nu*(29*a+7*m+106); nu=1+computed_P; a=2*m+8 for controller reuse, else m+16')
def whole_graph_proof(parent,p):
 old=parent['source'];new=p['source'];changed=[[a,b] for a,b in zip(old,new) if a!=b]
 need(len(old)==len(new)==244 and changed==[[['shifted_native_quotient','+','selection__w','packed_top_sum'],['shifted_native_quotient','+','selection__w','packed_z_product']]],'exact single operand edit')
 # Independent local polynomial coefficients in formal w,Z,S.
 w=(1,0,0);Z=(0,1,0);S=(0,0,1)
 add=lambda a,b:tuple(x+y for x,y in zip(a,b))
 oldq=add(add(add(w,Z),tuple(-v for v in S)),S);newq=add(w,Z)
 need(oldq==newq==(1,1,0),'full affine quotient-cut identity')
 table={}
 def intern(t):
  if t not in table:table[t]=len(table)
  return table[t]
 def run(rows):
  env={n:intern(('input',n)) for n in p['parameters']+p['auxiliaries']}
  at=lambda v:intern(('const',v)) if type(v)is int else env[v]
  for n,o,a,b in rows:env[n]=intern(('proved_quotient_cut',)) if n=='shifted_native_quotient' else intern((o,at(a),at(b)))
  return env
 a=run(old);b=run(new)
 need(all(a[n]==b[n] for n,o,x,y in new),'all complete downstream DAG expressions agree under proved cut')
 for l,r in p['comparisons']:
  need((a[l] if type(l)is str else l)==(b[l] if type(l)is str else l) and (a[r] if type(r)is str else r)==(b[r] if type(r)is str else r),'every actual comparison')
 need(a[parent['output']]==b[p['output']],'entire final polynomial graph identity')
 return dict(changed_rows=changed,local_formal_coefficients=list(oldq),whole_gate_identities=244,comparison_identities=6,finalizer_retained_exactly=True)

def verify(root):
 parent=canonical_parent(root=root);p=build(root=root);proof=whole_graph_proof(parent,p);counts=Counter();rng=random.Random(2442829)
 need(p['ledger']==dict(operations=244,M=103,A=141,certificate_operations=227,finalizer_operations=17,comparisons=6,positive_witnesses=36,all_gates_live=True),'complete paid count')
 names=p['parameters']+p['auxiliaries']
 for i in range(32):
  v={n:rng.randrange(1,5) if i<12 else rng.randrange(-3,4) for n in names}
  if i>=24:v={n:Fraction(k,3) for n,k in v.items()};counts['rational_identities']+=1
  b=execute(p['source'],v);pv=dict(v);pv['selection__w']+=b['packed_z_product']-b['packed_top_sum'];a=execute(parent['source'],pv)
  need(all(a[n]==b[n] for n,o,x,y in p['source']),'all actual gate evaluations under signed map')
  counts['complete_evaluations']+=1
  for l,r in p['comparisons']:
   val=lambda e,n:e[n] if type(n)is str else n
   need(val(a,l)-val(a,r)==val(b,l)-val(b,r),'full retained residual');counts['residual_evaluations']+=1
  if i<12:need(b['packed_top_sum']>b['packed_z_product']>0,'outer positivity independent of equations')
 for i in range(16):
  v={n:rng.randrange(1,4) for n in names};a=execute(parent['source'],v);cv=dict(v);cv['selection__w']+=a['packed_top_sum']-a['packed_z_product'];b=execute(p['source'],cv)
  need(min(cv.values())>0 and all(a[n]==b[n] for n,o,x,y in p['source']),'unconditional positive old-to-new whole graph embedding');counts['positive_parent_embeddings']+=1
 # Exact pretyping checks use positive fields with the real padded residues,
 # including nondyadic q; neither Boolean typing nor a Pell zero is assumed.
 for _ in range(512):
  F=[v+16*rng.randrange(0,30) for v in [1,4,2,8]];q=1+sum(F);r=sum(v*q**i for i,v in enumerate(F));A=F[1]+F[3]+1;B=F[2]+F[3];Z=(q-1)*F[3];S=A+(q+1)*(B+Z)
  w=rng.randrange(1,6);s=2*rng.randrange(1,6)+1;X=q*(w+Z);Y=s*q;E=X*Y
  need(r==(q-1)*S and S>Z>0 and r<q**3*(F[3]+1),'literal packing and tail inequalities')
  need(3*(q-1)*F[3]>2*q*(F[3]+1) and E>2*r+3 and X>=16 and Y>=3*q,'noncircular native bootstrap')
  counts['positive_pretyping_field_cases']+=1
 # Population exclusion and canonical quotient size, without huge Pell tuples.
 for t in range(4,13):
  q=1<<t
  for _ in range(16):
   left=q//16-1;cuts=sorted([0,left]+[rng.randrange(left+1) for i in range(3)]);ks=[b-a for a,b in zip(cuts,cuts[1:])];F=[v+16*k for v,k in zip([1,4,2,8],ks)];r=sum(v*q**i for i,v in enumerate(F));S=r//(q-1)
   need(sum(F)==q-1 and r%16==1 and r.bit_count()>=t and (r-2).bit_count()>=t+2,'negative-index population contradiction')
   need(q<r and S<r and t<r and 2*r+1-t>=r+1,'canonical X/q>S by 2^r>=r+1')
   counts['population_and_positive_inverse_cases']+=1
 # An off-zero positive tuple need not have a positive pullback.
 v={n:1 for n in names};b=execute(p['source'],v);oldw=1+b['packed_z_product']-b['packed_top_sum'];need(oldw<0,'signed-only reverse before equations')
 boundary={'all_child_coordinates':1,'signed_parent_w_negative':True,'signed_parent_w_sha256':sha(str(oldw).encode()),'not_a_full_zero':b[p['output']]!=0}
 for bad in [None,{},dict(p,degree_certificate={})]:
  try:checked(bad,root=root)
  except (ValueError,TypeError):counts['canonical_rejections']+=1
  else:raise ValueError('malformed packet accepted')
 need(integer_pullback(p,{n:1 for n in names},root=root)['selection__w']==oldw,'public signed map')
 c=build(root=root);c['parent_pins'].clear();need(build(root=root)['parent_pins']==PINS,'provenance copied')
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),pins=copy.deepcopy(PINS),packet=p,whole_graph_proof=proof,counts=dict(counts),off_zero_signed_boundary=boundary,scope='One complete saved default244 source, exact degree2829. General fixed-table positive-zero bijection proved in note after noncircular native recovery. No numerical universal alphabet, no historical large suite, and no full native Pell tuple materialized.')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);args=ap.parse_args();out=verify(args.root)
 if args.expect:need(exact(out,json.loads(args.expect.read_text())),'exact saved receipt')
 if args.output:args.output.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':out['status'],'counts':out['counts'],'ledger':out['packet']['ledger'],'exact_degree':out['packet']['degree_certificate']['exact_degree']},sort_keys=True))
if __name__=='__main__':main()
