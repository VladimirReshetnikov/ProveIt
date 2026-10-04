#!/usr/bin/env python3
"""Fresh inert-source census and bounded checks for exterior absorption."""
import argparse
import hashlib
import json
from pathlib import Path

PINS = {
 'complete84_scaled_strong_output.py':'8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
 'review_complete85_auxiliary_bezout_math.md':'77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d',
 'complete83_input_quotient_dichotomy.md':'46d6457d10d1847cd4241aa1ed6705bf520216fc32cf97891c1f439f6c2c2505',
 'complete83_computed_gamma_obstruction.md':'02b55f39ea585c76563897fcb0040f75d4257c410ffc3c27d5f3686822632d04',
 'complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
 'complete83_direct_gamma_witness_obstruction.md':'c1f7a146ba85020ea1ed436e64de9a9163f9c5c7ac8d013d46d719ccef92d3f4',
 'complete83_auxiliary_product_collapse.md':'a224d930f94a3888b4208147dc54d90127999342313120a5239e40408e948d50',
 'complete83_free_coefficient_scout.md':'867e277a2ca09af392e81cf7e54f6eaa7677a939ea3717448cd89053b5690b31',
 '../../1980/FIXED_RAW_UNIVERSAL_78_PROOF.md':'b28ddb9aec5225cda7dabc85fb952daf49de4041cf35910f62dabf3893749d39',
 '../../1980/FIXED_RAW_UNIVERSAL_76_PROOF.md':'75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87',
}
AUX = ['i','f','auxiliary_quotient','y_aux']
GROUPS = {
 'units':'norm_first norm_main norm_pair norm_input norm_triple norm_index norm_transport'.split(),
 'first_root_ratio':'tau_square R10b ksn2 first_root_base first_next first_product R10a hpm1'.split(),
 'main_root':'cam2 D1 gamma_sum a4 a4m5 gam R14 L15 a_square A c2 Ac2'.split(),
 'input_root':'index_product index_rhs difference_multiple exponent_partial modulus_multiple exponent_rhs mu2 kappa2 scaled_kappa2'.split(),
 'outer':'repunit q Lbig n2 wn2 sn2 UM R12 q_minus_F q_minus_FZ C_after_alpha scaled_t marked_rhs W odd_index index_difference gap_product gap Lm1 rproduct qMF mask_factor mask r_lhs kinner innerC transport_partial local_rhs'.split(),
}
WITNESSES = 'Jrep F alpha transport_quotient h s w tau_root eta zeta Z delta rho sigma'.split()
FIXED = 'Bm1 Kconstant twice_cell_bits inner_bits MC MF'.split()
REQUIRED = [
 ['R10b','+','eta','zeta'], ['R10a','+','ksn2','eta'],
 ['gamma_sum','+','rho','sigma'], ['A','+','a_square','a4m5'],
 ['c2','*','R10a','R10a'], ['Ac2','*','A','c2'],
 ['odd_index','+','scaled_t','inner_bits'],
 ['index_rhs','+','odd_index','index_product'],
 ['index_product','*','delta','A'],
 ['aux_y2','*','y_aux','y_aux'], ['L16','*','f','f'],
 ['auxiliary_Tf','*','auxiliary_quotient','f'],
 ['auxiliary_Tf_minus_one','-','auxiliary_Tf',1],
 ['auxiliary_c_Tf','*','R10a','auxiliary_Tf_minus_one'],
 ['auxiliary_R_f2','*','r_lhs','L16'],
 ['aux_u_rhs','-','auxiliary_c_Tf','auxiliary_R_f2'],
 ['H2','*','aux_u_rhs','aux_u_rhs'],
 ['aux_square_gap','-','H2','aux_y2'],
 ['aux_coefficient_root','*','i','Ac2'],
 ['R16','*','aux_coefficient_root','aux_coefficient_root'],
 ['scaled_f_square','*','A','L16'],
 ['norm_strong','-','scaled_f_square','R16'],
 ['L17','*','R16','aux_square_gap'], ['norm_aux','+','L17','aux_y2'],
 ['norm_pair','*','norm_first','norm_main'],
 ['norm_triple','*','norm_pair','norm_input'],
 ['norm_four','*','norm_triple','norm_aux'],
 ['norm_product','*','norm_four','norm_index'],
 ['all_units','*','norm_product','norm_transport'],
 ['seven_units','*','all_units','norm_strong'],
 ['polynomial','-','seven_units','A'],
]

def ck(ok, message):
 if not ok: raise ValueError(message)
def sha(b): return hashlib.sha256(b).hexdigest()
def canonical(a): return json.dumps(a,sort_keys=True,separators=(',',':')).encode()
def read(path):
 def pairs(items):
  out={}
  for k,v in items:
   ck(k not in out,'duplicate key');out[k]=v
  return out
 def bad(x): raise ValueError('noninteger JSON number '+x)
 return json.loads(path.read_text(),object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)

def pell(A,n):
 D=A*A-1
 def product(x,y): return (x[0]*y[0]+D*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
 result=(1,0);base=(A,1)
 while n:
  if n&1:result=product(result,base)
  base=product(base,base);n//=2
 return result

def polynomial_checks():
 names=['Delta','c','i','f','T','R','y','P5'];z=(0,)*len(names)
 def num(n):return {z:n} if n else {}
 def v(name):
  a=list(z);a[names.index(name)]=1;return {tuple(a):1}
 def add(a,b,sign=1):
  d=dict(a)
  for m,c in b.items():
   d[m]=d.get(m,0)+sign*c
   if not d[m]:del d[m]
  return d
 def mul(a,b):
  d={}
  for m,c in a.items():
   for n,e in b.items():
    k=tuple(x+y for x,y in zip(m,n));d[k]=d.get(k,0)+c*e
  return {k:c for k,c in d.items() if c}
 def square(a):return mul(a,a)
 D,c,i,f,T,R,y,P=map(v,names)
 Q=square(mul(mul(D,i),square(c)))
 V=add(mul(c,add(mul(T,f),num(1),-1)),mul(R,square(f)),-1)
 Na=add(mul(Q,add(square(V),square(y),-1)),square(y))
 Ns=add(mul(D,square(f)),Q,-1)
 full=add(mul(mul(P,Na),Ns),D,-1)
 ck(all(m[2]%2==0 for m in full),'evenness in i')
 zero={m:k for m,k in full.items() if m[2]==0}
 expected=mul(D,add(mul(mul(P,square(f)),square(y)),num(1),-1))
 ck(zero==expected,'exact i=0 output')
 return {'variables':names,'full_factor_coefficients':[[list(m),c] for m,c in sorted(full.items())],
         'zero_i_coefficients':[[list(m),c] for m,c in sorted(zero.items())],
         'all_i_exponents_even':True,'zero_i_identity':'Delta*(P5*f^2*y^2-1)'}

def full_source_contraction(p,outside):
 # Read every literal row, cutting only source values proved independent of
 # all four auxiliary ports. Keep the two exterior product rows expanded
 # so P5 resolves to its five actual factor wires.
 cuts=set(outside)-{'norm_pair','norm_triple'}
 def v(n):return {(n,):1}
 def num(n):return {():n} if n else {}
 def add(a,b,s=1):
  out=dict(a)
  for m,c in b.items():
   out[m]=out.get(m,0)+s*c
   if not out[m]:del out[m]
  return out
 def mul(a,b):
  out={}
  for m,c in a.items():
   for n,d in b.items():
    key=tuple(sorted(m+n));out[key]=out.get(key,0)+c*d
  return {m:c for m,c in out.items() if c}
 def run(ivalue):
  e={n:v('port:'+n) for n in p['free']};e['i']=ivalue
  for n,o,a,b in p['source']:
   if n in cuts:e[n]=v('cut:'+n);continue
   a=e[a] if isinstance(a,str) else num(a)
   b=e[b] if isinstance(b,str) else num(b)
   e[n]=mul(a,b) if o=='*' else add(a,b,1 if o=='+' else -1)
  return e
 plus=run(v('port:i'));minus=run({('port:i',):-1});zero=run({})
 ck(plus[p['output']]==minus[p['output']],'all84 source even-i identity')
 f=v('port:f');y=v('port:y_aux');P5=num(1)
 factors=['norm_first','norm_main','norm_input','norm_index','norm_transport']
 for n in factors:P5=mul(P5,v('cut:'+n))
 expected=mul(v('cut:A'),add(mul(mul(P5,mul(f,f)),mul(y,y)),num(1),-1))
 ck(zero[p['output']]==expected,'all84 source zero-i contraction')
 return {'literal_rows_visited_per_pass':len(p['source']),
         'auxiliary_independent_cut_rows':sorted(cuts),
         'exterior_factor_product_rows_expanded':['norm_pair','norm_triple'],
         'five_actual_factors':factors,'even_i_source_identity':True,
         'zero_i_source_identity':True,
         'zero_i_output_coefficients':[[list(m),c] for m,c in sorted(expected.items())],
         'nonzero_source_cut_terms':len(plus[p['output']])}

def build(root):
 for name,h in PINS.items():ck(sha((root/name).read_bytes())==h,'dependency '+name)
 p=read(root/'complete84_scaled_strong_output.json')['packet'];rows=p['source'];by={r[0]:r for r in rows}
 ck(len(rows)==len(by)==84,'complete source')
 for r in REQUIRED:ck(by[r[0]]==r,'literal interface '+r[0])
 known=set(p['free']);tainted=set(AUX);outside=[]
 for n,o,a,b in rows:
  ck(n not in known and o in ['+','-','*'],'producer')
  ck(all(type(x)is int or (isinstance(x,str) and x in known) for x in [a,b]),'topology')
  known.add(n)
  if a in tainted or b in tainted:tainted.add(n)
  else:outside.append(n)
 grouped=[n for g in GROUPS.values() for n in g]
 ck(len(grouped)==len(set(grouped))==len(outside)==64 and set(grouped)==set(outside),'exact64 partition')
 ck(set(p['witnesses'])-set(AUX)==set(WITNESSES) and len(WITNESSES)==14,'all14 exterior witnesses')
 ck(p['fixed_numerals']==FIXED,'all6 fixed numeral ports')
 ck(set(p['free'])-set(AUX)==set(WITNESSES+FIXED+['x']),'all21 exterior free values')
 ck([r[0] for r in rows if 'i' in r[2:]]==['aux_coefficient_root'],'sole i consumer')
 ck([r[0] for r in rows if 'aux_coefficient_root' in r[2:]]==['R16'],'root only squared')
 ck(all(n not in tainted for n in ['norm_first','norm_main','norm_input','norm_index','norm_transport']),'P5 exterior')
 models=[]
 for A in range(2,7):
  for rank in [2,3]:
   D,c=pell(A,rank);m=rank*c;f,z=pell(A,m);ck(z%c**2==0,'square divisibility')
   i=z//c**2;bound=c**(c-2)
   ck(f*f-(A*A-1)*z*z==1 and i>bound,'exact strong growth')
   models.append({'A':A,'rank':rank,'c':c,'least_allowed_index':m,'strong_i':str(i),'strict_power_bound':str(bound),'scope':'Pell component only; not a compiler history'})
 congruences=[]
 for A in range(2,8):
  for rank in range(1,6):
   D,c=pell(A,rank)
   for k in range(1,13):
    z=pell(A,rank*k)[1];ck(z%c==0,'rank divisibility')
    residue=z//c%c;expected=k*pow(D,k-1,c)%c
    ck(residue==expected and ((z%c**2==0)==(k%c==0)),'exact quotient congruence')
    congruences.append([A,rank,k,c,residue])
 thresholds=[]
 for t in range(13):
  for L in [1,2,3,4,5,7,8,9,15,16,17,31,32,33,255,256,257,1024]:
   ceiling=(L-1).bit_length();bound=4*t+2+ceiling;c=bound+1
   ck(c**(c-2)>L*c**(4*t),'effective threshold')
   thresholds.append([t,L,bound])
 return {'schema':'complete84-exterior-auxiliary-absorption-v1',
  'source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,
  'parent_packet_sha256':sha(canonical(p)),'authenticated_parent_source':rows,
  'source_census':{'auxiliary_ports':AUX,'computed_exterior_in_source_order':outside,'proof_partition':GROUPS,
                  'exterior_witnesses':WITNESSES,'fixed_numerals':FIXED,'ordinary_input':'x',
                  'computed_count':64,'free_count':21,'all_named_values':85,'literal_boundary_rows':REQUIRED},
  'factor_polynomial_checks':polynomial_checks(),'full_source_contraction':full_source_contraction(p,outside),
  'strong_growth_components':models,
  'rank_congruence_components':congruences,'effective_threshold_components':thresholds,
  'theorem':{'parent_bound':'every exterior absolute value < c^4; i > c^(c-2)',
             'G_nonzero_input_bound':'c <= 4*degree(G)+2+ceil(log2(max(1,coefficient_l1_norm(G))))',
             'zero_G_boundary':'f=y_aux=1 and P5=1, with G(exterior)=0; T any positive integer',
             'signed_G_nonzero_uses_parent_i':'abs(G)',
             'finite_nonzero_sector_only':True,'canonical_auxiliary_completion_assumed':False},
  'scope':{'predecessor_code_executed':False,'new_complete_candidate_emitted':False,'operation_saving_claim':False,
           'independent_gamma_language_resolved':False,'component_examples_are_native_histories':False,
           'actual_native_tuple_materialized':False}}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True)
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 a=ap.parse_args();result=build(a.root)
 if a.output:
  with a.output.open('x') as stream:stream.write(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else:ck(canonical(result)==canonical(read(a.expect)),'exact receipt')
 print('PASS:64 exterior rows/21 free values; exact signed/zero-i boundary;10 Pell growth,360 rank and234 threshold checks')
if __name__=='__main__':main()
