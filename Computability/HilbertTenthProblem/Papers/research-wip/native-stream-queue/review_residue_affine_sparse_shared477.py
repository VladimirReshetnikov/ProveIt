"""Independent inert-array audit of the frozen U21 shared477 packet.
No predecessor or author Python is imported or executed.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

AUTHOR = {
 'residue_affine_sparse_shared477.py':'21463ce43e33aea904401277940f83990e033018ab624d8367b11c7eee9c2b0f',
 'residue_affine_sparse_shared477.json':'3472269ef557bfbcb6dd2697f9a780990bb394d7e370cadb282f7b03a4cd3716',
 'residue_affine_sparse_shared477.md':'95c37d45ea3ca2d7e7d653173f22e9821ee85036abe3a345ec0c563348b8f2b9',
}
PARENT = {
 'residue_affine_sparse_control_codes.py':'433c4d87af47d166d8c26db4e879a77e12a3fbcf3e7a1bf8c125701b2b21a4a7',
 'residue_affine_sparse_control_codes.json':'2f9e97873bf4b02da0e6664bdf1ac150d4b3f5befb2bb5ae907c01c3c1dc7d9d',
 'residue_affine_sparse_control_codes.md':'be133b5d93c082c3f3022e4b9990140ff3de71cf7202a7ba281a48e8c77d34da',
 'residue_affine_sparse_factored.md':'b169236c449623049759b7ac0877b2202b3aba389ace8e06d31370396abb9ea7',
 'residue_affine_sparse_scale538.md':'0c6e6bd9606a6c6b1c70f21575784ac24ed9ff2f64ab788cc6c64b0106979623',
 'residue_affine_sparse_terminal537.md':'9deba23f3b210d730fd32a2a10aa886edc9637c4f8d26010cc0f0f55a7c7f6d1',
}
GROUPS = ('prime_selector_93','prime_selector_95','prime_selector_97','prime_selector_101',
 'prime_selector_109','prime_selector_113','prime_selector_115','selectors_36',
 'control_codes__duplicate_state_6','edge_29')
OUT='norm_output'

def require(v,msg):
 if not v: raise ValueError(msg)
def sha(b): return hashlib.sha256(b).hexdigest()
def canon(x): return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def pairs(xs):
 d={}
 for k,v in xs:
  require(k not in d,'duplicate key '+k); d[k]=v
 return d
def bad_constant(s): raise ValueError('nonfinite JSON '+s)
def read(p): return json.loads(p.read_text(),object_pairs_hook=pairs,parse_constant=bad_constant)
def pin(root,pins):
 for n,h in pins.items(): require(sha((root/n).read_bytes())==h,'pin '+n)
def defs(rows):
 d={}
 for r in rows:
  require(type(r)is list and len(r)==4,'row length')
  n,o,a,b=r
  require(type(n)is str and n not in d and o in ('+','-','*'),'SSA/op')
  require(all(type(x) in (int,str) for x in (a,b)),'operand types')
  d[n]=r
 return d
def ports(rows):
 d=defs(rows)
 return sorted({x for r in rows for x in r[2:] if type(x)is str and x not in d})
def check_graph(rows):
 d=defs(rows); free=ports(rows); seen=set(free)
 for n,o,a,b in rows:
  require(n not in seen and all(type(x)is int or x in seen for x in (a,b)),'topology '+n)
  seen.add(n)
 todo=[OUT]; live=set()
 while todo:
  n=todo.pop()
  if n not in d or n in live: continue
  live.add(n); todo.extend(x for x in d[n][2:] if type(x)is str)
 require(live==set(d),'dead registers')
 c=Counter(r[1] for r in rows)
 return {'operations':len(rows),'multiplications':c['*'],'additions_subtractions':c['+']+c['-']}

# Sparse polynomials have integer coefficients and sorted tuples of formal variable names.
def add(a,b,sign=1):
 c=dict(a)
 for m,v in b.items(): c[m]=c.get(m,0)+sign*v
 return {m:v for m,v in c.items() if v}
def mul(a,b):
 c={}
 for m,v in a.items():
  for n,w in b.items():
   k=tuple(sorted(m+n)); c[k]=c.get(k,0)+v*w
 return {m:v for m,v in c.items() if v}
def expand(rows,target,boundaries):
 d=defs(rows); memo={n:{(n,):1} for n in boundaries}; used=set()
 def at(x):
  if type(x)is int:return {():x} if x else {}
  if x not in memo:
   require(x in d,'unbound polynomial '+x)
   _,o,a,b=d[x]; a,b=at(a),at(b); used.add(x)
   memo[x]=mul(a,b) if o=='*' else add(a,b,1 if o=='+' else -1)
   require(len(memo[x])<1000,'bounded expansion exceeded')
  return memo[x]
 return at(target),sorted(used)
def plist(p): return [[list(m),v] for m,v in sorted(p.items())]

def reconstruct(old):
 # Independent dictionary reconstruction; chronology/liveness verified separately.
 d={r[0]:list(r) for r in old}
 gone=set('selectors_'+str(i) for i in range(37,70))|{
  'non_increment_149','non_decrement_150','zero_complement_151',
  'range_repeat_shift_407','three_range_repeat_408'}
 for n in gone: del d[n]
 chain=list(GROUPS)
 for k in range(9):
  n='selectors_70' if k==8 else 'u21_grouped_J_'+str(k)
  left=chain[0] if k==0 else 'u21_grouped_J_'+str(k-1)
  d[n]=[n,'+',left,chain[k+1]]
 d['common_quotient_152']=['common_quotient_152','+','quotient_71','difference_word_148']
 d['u21_nonzero_actions']=['u21_nonzero_actions','+','action_selector_123','action_selector_134']
 d['u21_nonzero_or_test']=['u21_nonzero_or_test','+','u21_nonzero_actions','edge_14']
 d['common_payload_154']=['common_payload_154','+','common_remainder_153','u21_nonzero_or_test']
 d['all_ranges_427']=['all_ranges_427','*','range_mask_91','repeat_odd_318']
 return d,sorted(gone)

class ExactExpressions:
 """Integer intern IDs: equality is exact tuple equality, never digest equality."""
 def __init__(self): self.nodes={}
 def intern(self,key):
  if key not in self.nodes:self.nodes[key]=len(self.nodes)
  return self.nodes[key]
 def leaf(self,n):return self.intern(('variable',n))
 def constant(self,n):return self.intern(('integer',n))
 def op(self,o,a,b):
  if o in ('+','*'):a,b=sorted((a,b))
  return self.intern((o,a,b))
 def polynomial(self,p,env):
  # Bind each formal local variable to its ACTUAL computed expression ID.
  terms=tuple(sorted((v,tuple(sorted(env[n] for n in m))) for m,v in p.items()))
  return self.intern(('polynomial_in_computed_expressions',terms))

def exact_identity(old,new):
 free=ports(old); edgebd={f'edge_{i}' for i in range(36)}; partition=[]; cover=[]
 for n in GROUPS:
  p,_=expand(old,n,edgebd)
  require(all(len(m)==1 and v==1 for m,v in p.items()),'group not unweighted sum')
  support=sorted(int(m[0][5:]) for m in p);cover.extend(support)
  partition.append({'register':n,'edges':support})
 require(sorted(cover)==list(range(36)),'partition overlap/gap')
 pj,_=expand(old,'selectors_70',free);qj,_=expand(new,'selectors_70',free)
 wantj={():-36,**{(f'edge{i}_hat',):1 for i in range(36)}}
 require(pj==qj==wantj,'raw hat J polynomial')
 pr,_=expand(old,'three_range_repeat_408',{'scale_89'})
 pr0,_=expand(old,'repeat_odd_318',{'scale_89'})
 qr,_=expand(new,'repeat_odd_318',{'scale_89'})
 require(pr==pr0==qr=={():1,('scale_89',):1,('scale_89','scale_89'):1},'repunit exact polynomial')
 bd={'quotient_71','selectors_70','difference_word_148','complement_73',
     'action_selector_123','action_selector_134','edge_14'}
 pc,_=expand(old,'common_payload_154',bd);qc,_=expand(new,'common_payload_154',bd)
 wantc={(n,):v for n,v in [('quotient_71',1),('difference_word_148',1),('complement_73',-1),
  ('action_selector_123',1),('action_selector_134',1),('edge_14',1)]}
 require(pc==qc==wantc,'common payload polynomial')
 inter=ExactExpressions(); envs=[]; bindings=[]
 cut={'selectors_70':(pj,set(free)), 'repeat_odd_318':(pr,{'scale_89'}),
  'three_range_repeat_408':(pr,{'scale_89'}),'common_payload_154':(pc,bd)}
 for index,rows in enumerate((old,new)):
  env={n:inter.leaf(n) for n in free}
  for n,o,a,b in rows:
   def get(x):return inter.constant(x) if type(x)is int else env[x]
   value=inter.op(o,get(a),get(b))
   if n in cut:
    p,boundary=cut[n]
    require(boundary<=env.keys(),'unavailable actual cut binding '+n)
    if index:
     require(all(env[v]==envs[0][v] for v in boundary),'unequal upstream cut binding '+n)
    value=inter.polynomial(p,env)
    bindings.append({'side':index,'target':n,'boundary':sorted(boundary)})
   env[n]=value
  envs.append(env)
 common=set(defs(old))&set(defs(new)); changed={'common_quotient_152','common_remainder_153'}
 checked=sorted(common-changed)
 require(len(checked)==465,'retained-value census')
 require(all(envs[0][n]==envs[1][n] for n in checked),'exact retained expression mismatch')
 require(all(envs[0][n]!=envs[1][n] for n in changed),'unexpected intermediate equality')
 require(envs[0][OUT]==envs[1][OUT],'exact output expression mismatch')
 return {'partition':partition,'J_raw_hat_polynomial':plist(pj),'R3_polynomial':plist(pr),
  'payload_polynomial':plist(pc),'exact_upstream_bindings':bindings,
  'same_value_retained_registers':checked,'expression_nodes':len(inter.nodes),
  'method':'Exact tuple intern IDs with independently expanded local polynomials bound to actual equal upstream expression IDs; no hash-based equality oracle'}

def degree_audit(rows):
 free=ports(rows); d={n:1 for n in free}
 for n,o,a,b in rows:
  aa=d[a] if type(a)is str else 0;bb=d[b] if type(b)is str else 0
  d[n]=aa+bb if o=='*' else max(aa,bb)
 naive=d[OUT]
 boundary={'native__wn2','native__R12','native__R10a','native__gam'}
 p,cone=expand(rows,'native__R15',boundary)
 X='native__wn2';a='native__R12';c='native__R10a';G='native__gam'
 expected={tuple(sorted(m)):v for m,v in [((X,X),1),((a,c,X),2),((X,G),2),
  ((a,c,G),2),((G,G),1),((a,c,c),-4),((c,c),-3)]}
 require(p==expected,'main norm cancellation identity')
 weights={n:d[n] for n in boundary}; require(weights=={X:308,a:374,c:67,G:375},'main norm weights')
 bound=max(sum(weights[x] for x in m) for m in p)
 require(bound==816 and d['native__R15']==882 and naive==5157,'main norm degree calculation')
 tightened={n:1 for n in free}
 for n,o,a0,b0 in rows:
  aa=tightened[a0] if type(a0)is str else 0;bb=tightened[b0] if type(b0)is str else 0
  tightened[n]=aa+bb if o=='*' else max(aa,bb)
  if n=='native__R15':tightened[n]=bound
 names=['native__R15','native__P17','native__first_unit','native__bs_q',
  'native__f_square_minus_one','native__index_unit','native__linear_unit','sparse_repunit_unit']
 factors=[tightened[n] for n in names]
 require(factors==[816,1900,442,65,1018,375,375,2],'factor bounds')
 require(tightened['sparse_all_units']==4993 and tightened['norm_sum5']==98 and tightened[OUT]==5091,'full tightened degree')
 return {'naive_source_degree_bound':naive,'main_norm_cone_rows':[defs(rows)[n] for n in cone],
  'main_norm_expansion':plist(p),'boundary_degree_bounds':weights,
  'main_norm_tightened_bound':bound,'factor_names':names,'factor_degree_bounds':factors,
  'factor_product_bound':4993,'outer_SOS_bound':98,'full_degree_upper_bound':5091,
  'exact_degree_claimed':False}

def evaluate(rows,values,p):
 env=dict(values)
 for n,o,a,b in rows:
  a=env[a] if type(a)is str else a;b=env[b] if type(b)is str else b
  env[n]=(a*b if o=='*' else a+b if o=='+' else a-b)%p
 return env

def build(root,author_dir):
 pin(root,PARENT);pin(author_dir,AUTHOR)
 parent=read(root/'residue_affine_sparse_control_codes.json');child=read(author_dir/'residue_affine_sparse_shared477.json')
 require(child['dependencies']==PARENT,'dependency manifest')
 require(child['source_sha256']==AUTHOR['residue_affine_sparse_shared477.py'],'author helper binding')
 old=parent['source'];new=child['packet']['source'];od=defs(old);nd=defs(new)
 require(parent['source_sha256']==sha(json.dumps(old).encode()),'parent stored source hash')
 require(child['packet']['source_sha256']==sha(canon(new)),'child source hash')
 before=check_graph(old);after=check_graph(new)
 require(before=={'operations':505,'multiplications':177,'additions_subtractions':328},'parent count')
 require(after=={'operations':477,'multiplications':176,'additions_subtractions':301},'child count')
 expected,removed=reconstruct(old)
 require(nd==expected,'full independently reconstructed row dictionary')
 require(set(od)-set(nd)==set(removed),'deleted row set')
 require(len(set(nd)-set(od))==10 and len(removed)==38,'row edit census')
 free=ports(old);require(ports(new)==free and len(free)==69,'unchanged free ports')
 require(child['packet']['witnesses']==sorted(set(free)-{'program','input'}),'witness list')
 require(child['packet']['parameters']==['program','input'] and child['packet']['fixed_program_parameters']==['program'] and child['packet']['ordinary_input_parameter']=='input','parameter scope')
 require('radix_program' not in free and len(child['packet']['witnesses'])==67,'one-program witness interface')
 height=[['height_83','+','program','input'],['height_85','+','height_83','height_slack'],['radix_86','*',64,'height_85']]
 require(all(od[r[0]]==nd[r[0]]==r for r in height),'height/radix rows')
 native=[r for r in old if r[0].startswith('native__')];require(len(native)==72 and all(nd[r[0]]==r for r in native),'literal native rows')
 final=old[485:];require(len(final)==20 and new[-20:]==final,'literal contiguous finalizer')
 fops=Counter(r[1] for r in final);require(fops==Counter({'*':7,'+':6,'-':7}),'finalizer count')
 # Complete-source liveness has already checked every certificate row.
 cert={'operations':after['operations']-20,'multiplications':after['multiplications']-7,'additions_subtractions':after['additions_subtractions']-13,'equations':7,'witnesses':67}
 require(cert==child['packet']['certificate_ledger'],'certificate ledger')
 require(dict(after,witnesses=67)==child['packet']['ledger'],'packet ledger')
 exact=exact_identity(old,new)
 require(exact['partition']==child['exact_contract']['disjoint_partition'],'author partition')
 degrees=degree_audit(old);require(degree_audit(new)==degrees,'same independent degree audit')
 require(child['packet']['polynomial_degree_upper_bound']==degrees['full_degree_upper_bound'] and child['packet']['exact_degree_claimed'] is False,'degree scope')
 rng=random.Random(410477);checked=exact['same_value_retained_registers'];samples=0
 for modulus in (1000000007,1000000009):
  for _ in range(12):
   v={n:rng.randrange(-100,101) for n in free};a=evaluate(old,v,modulus);b=evaluate(new,v,modulus)
   require(all(a[n]==b[n] for n in checked),'fresh whole-source signed modular equality');samples+=1
 return {'status':'PASS_INDEPENDENT_SHARED477','checker_sha256':sha(Path(__file__).read_bytes()),
  'author_pins':AUTHOR,'parent_pins':PARENT,'parent_ledger':before,'new_ledger':dict(after,witnesses=67),
  'certificate_ledger':cert,'all_rows_reconstructed':len(new),'removed_names':removed,
  'literal_native_rows':72,'literal_finalizer_rows':20,'literal_height_radix_rows':height,
  'unchanged_free_ports':free,'exact_identity':exact,'independent_degree_audit':degrees,
  'signed_modular_source_pairs':samples,'scope':'Exact full all-ring identity and inherited identical positive zero set to actual505; ordinary-input theorem reviewed at interface level, not independently re-proving U21/native universality; no full accepting Pell zero materialized'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--author-dir',type=Path,required=True)
 out=ap.add_mutually_exclusive_group(required=True);out.add_argument('--output',type=Path);out.add_argument('--expect',type=Path);a=ap.parse_args()
 r=build(a.root,a.author_dir)
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:require(canon(read(a.expect))==canon(r),'exact typed receipt replay')
 print(r['status'],r['new_ledger'],'degree upper',r['independent_degree_audit']['full_degree_upper_bound'])
if __name__=='__main__':main()
