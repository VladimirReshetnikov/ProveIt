"""Fresh finite evidence for the separately pinned mathematical note.

Only source/proof bytes and JSON data are read. No predecessor is imported.
For pretyping ratio bounds, first use X>=16, r>=24 and 6XY^2>a in the
strict lower estimate. It gives a>X^(r+1)/3>8r, establishing 4r/a<1/2
before the upper estimate. The older X>=4096 statement is not needed.
This file does not materialize Y, main Pell values or an auxiliary tuple.
"""
import argparse
from collections import Counter
import hashlib
import json
from math import comb
from pathlib import Path

PINS = {
 'complete84_joint_root_cut.md':'79cfda9e870ad63a848fb454266d1bca98f2117393edc57f99108b4c1cce780c',
 'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'review_complete85_auxiliary_bezout_math.md':'77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d',
 'review_complete74_asymmetric_scale_math.md':'a7f8d64389597c5a8fff93bad1f023dfc440d736bb9d77f2acd549e758aa0b58',
 'pell_kernel_half_binomial42.md':'0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992',
 '../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md':'47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b',
}
AUTHOR_PINS = {
 'complete83_shared_projection_scout.py':'2ff8bede5f08b0bc452ca50a432ebc6dbcad5ddd18bd5da5acc2b1d5b189ae9c',
 'complete83_shared_projection_scout.json':'dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c',
}
PROOF_PIN='1a9923b7202bef2e5a640b3b27c942423b9d9829d9fc6e7f4b55fa5c4d91053c'

def require(value, why):
 if not value: raise ValueError(why)

def digest(data): return hashlib.sha256(data).hexdigest()

def pairs(items):
 out={}
 for k,v in items:
  require(k not in out,'duplicate JSON key'); out[k]=v
 return out

def bad_number(value): raise ValueError('non-integer JSON number '+value)

def read_json(data):
 return json.loads(data, object_pairs_hook=pairs, parse_float=bad_number, parse_constant=bad_number)

def typed_equal(a,b):
 if type(a) is not type(b): return False
 if isinstance(a,dict): return a.keys()==b.keys() and all(typed_equal(a[k],b[k]) for k in a)
 if isinstance(a,list): return len(a)==len(b) and all(typed_equal(x,y) for x,y in zip(a,b))
 return a==b

def v2(n):
 require(type(n) is int and n>0,'v2 positive integer domain')
 return (n & -n).bit_length()-1

def build(root, author_root, proof):
 for name,expected in PINS.items():require(digest((root/name).read_bytes())==expected,'proof/source pin '+name)
 for name,expected in AUTHOR_PINS.items():require(digest((author_root/name).read_bytes())==expected,'author pin '+name)
 require(digest(proof.read_bytes())==PROOF_PIN,'mathematical companion pin')
 author=read_json((author_root/'complete83_shared_projection_scout.json').read_bytes())
 packet=author['packet']; rows=packet['source']; defs={r[0]:r for r in rows}
 require(len(defs)==len(rows)==83,'unique 83-row source')
 required=[
  ['repunit','*','Bm1','Jrep'],['q','+','repunit',1],
  ['Lbig','*','q','q'],['n2','*','Lbig','q'],
  ['wn2','*','w','q'],['sn2','*','s','n2'],
  ['q_minus_F','-','q','F'],['q_minus_FZ','-','q_minus_F','Z'],
  ['C_after_alpha','-','q_minus_FZ','alpha'],
  ['scaled_t','*','twice_cell_bits','x'],['marked_rhs','-','C_after_alpha','scaled_t'],
  ['W','-','marked_rhs','Z'],['odd_index','+','scaled_t','inner_bits'],
  ['gap_product','*','repunit','q_minus_F'],['gap','+','gap_product','q_minus_FZ'],
  ['Lm1','-','Lbig',1],['rproduct','*','gap','Lm1'],
  ['qMF','*','q','MF'],['mask_factor','+','MC','qMF'],
  ['mask','*','mask_factor','Jrep'],['r_lhs','+','rproduct','mask'],
  ['kinner','+','Kconstant','w'],['innerC','*','kinner','marked_rhs'],
  ['transport_partial','+','innerC','q_minus_F'],
  ['local_rhs','*','transport_quotient','repunit'],['norm_transport','-','transport_partial','local_rhs'],
  ['gam','*','sigma','a4m5'],['shared_main_partial','+','D1','shared_projection'],
  ['R14','+','shared_main_partial','gam'],['exponent_rhs','+','exponent_partial','shared_projection'],
 ]
 for row in required:require(defs.get(row[0])==row,'literal diagnostic interface '+row[0])
 require('rho' not in packet['free'] and 'shared_projection' in packet['witnesses'],'changed positive coordinate')
 counts=Counter(r[1] for r in rows)
 require(counts['*']==46 and counts['+']+counts['-']==37,'literal counts')
 require(len(packet['witnesses'])==18,'18 positive witnesses')

 fixed={'Bm1':15,'Kconstant':28,'twice_cell_bits':8,'inner_bits':1,'MC':14,'MF':19}
 outer={'Jrep':1,'x':1,'F':4,'Z':1,'alpha':2}
 q=fixed['Bm1']*outer['Jrep']+1; B=fixed['Bm1']+1
 C=q-outer['F']-outer['Z']-outer['alpha']-fixed['twice_cell_bits']*outer['x']
 W=C-outer['Z']; u=fixed['twice_cell_bits']*outer['x']+fixed['inner_bits']
 R=(q*q-outer['Z']-q*outer['F'])*(q*q-1)+(fixed['MC']+q*fixed['MF'])*outer['Jrep']
 r=(R-1)//2
 require((q,C,W,u,R,r)==(16,1,0,9,49023,24511),'outer diagnostic')
 require(R%4==3 and 3*q+1<R<q**4-q**3,'index/radix bounds')
 native_MF=fixed['MF']-(B-1)
 require(0<fixed['MC']<B-1 and fixed['MC']%4==2,'MC scalar conditions')
 require(0<native_MF<B-1 and native_MF%8==4,'MF scalar conditions')
 require(fixed['MC'].bit_count()+native_MF.bit_count()==4,'mask population')
 low_mask=fixed['MC']*outer['Jrep']+1
 high_mask=native_MF*outer['Jrep']-1
 require(((outer['Z']-1)&low_mask)==0 and (outer['F']&high_mask)==0,'both diagnostic ANDs')
 require(R.bit_count()==14,'packed population')
 X=(1<<R)-(1<<u)
 require(X>0 and X%q==0 and X>(1<<(R-1)),'X margin/divisibility')
 w=X//q
 transport_numerator=fixed['Kconstant']+w+11
 require(transport_numerator%(q-1)==0,'transport integrality')
 transport=transport_numerator//(q-1)
 require(transport>0 and (fixed['Kconstant']+w)*C+q-outer['F']-transport*(q-1)==1,'transport norm')
 central=comb(2*r,r); first=comb(2*r,r+1)
 require(first*(r+1)==central*r,'first coefficient identity')
 require((v2(r+1),v2(X),v2(central),v2(first),v2(first*X))==(6,9,13,7,16),'valuation calculation')
 modulus=1<<18
 require((X*X)%modulus==0,'every higher power has zero residue')
 Mmod=(central+first*X)%modulus
 require(Mmod==139264 and v2(Mmod)==13 and v2(Mmod//2)==12,'half-word cubed-scale valuation')
 require(w%(q-1)==6 and 24*r<X+1,'transport and ratio margins')
 return {
  'scope':'Finite scalar and binomial evidence only. No valid-program instance or native Pell tuple is materialized.',
  'source_sha256':digest(Path(__file__).read_bytes()),'proof_sha256':PROOF_PIN,
  'dependency_pins':PINS,'author_pins':AUTHOR_PINS,
  'guarded_rows':required,'source_ledger':{'M':46,'A':37,'total':83,'positive_witnesses':18},
  'fixed_diagnostic_numerals':fixed,'supplied_outer_values':outer,
  'outer_values':{'q':q,'C':C,'W':W,'u':u,'R':R,'r':r,'native_MF':native_MF,'popcount_R':R.bit_count(),
    'low_mask':low_mask,'high_mask':high_mask,'low_AND':0,'high_AND':0,'offset_e':-(1<<u),
    'X_bits':X.bit_length(),'X_mod_q':X%q,'w_mod_q_minus_one':w%(q-1),'transport_positive':True,'transport_norm':1},
  'binomial_evidence':{'central_bits':central.bit_length(),'first_coefficient_bits':first.bit_length(),
    'v2_r_plus_one':v2(r+1),'v2_X':v2(X),'v2_central':v2(central),'v2_first_coefficient':v2(first),
    'v2_first_term':v2(first*X),'all_j_at_least_two_valuation_lower_bound':18,
    'modulus':modulus,'M_modulus':Mmod,'v2_Y':12,'q_cubed_valuation':12},
  'ratio_hypothesis_clarification':[
    'Pretyping: X>=16, r>=24, 6XY^2>a suffice for the strict lower Pell estimate.',
    'That lower estimate gives a>X^(r+1)/3>=16^(r+1)/3>8r, hence 4r/a<1/2 before using the upper estimate.',
    'The coarse inequality a>R alone would not establish the upper-estimate premise; no such inference is made.',
    'For this diagnostic X>2^(R-1), so theta<1/2; independently checked 24r<X+1 gives 12r/(X+1)<1/2.'
  ],
  'unmaterialized':['Y','c','main Pell tuple','normalized auxiliary tuple'],
  'valid_compiler_recipe_certified':False,'rejected_input_counterexample_claimed':False,
 }

def main():
 parser=argparse.ArgumentParser()
 parser.add_argument('--root',type=Path,required=True)
 parser.add_argument('--author-root',type=Path,default=Path(__file__).parent)
 parser.add_argument('--proof',type=Path,default=Path(__file__).with_suffix('.md'))
 group=parser.add_mutually_exclusive_group(required=True)
 group.add_argument('--output',type=Path);group.add_argument('--expect',type=Path)
 args=parser.parse_args();result=build(args.root,args.author_root,args.proof)
 encoded=(json.dumps(result,sort_keys=True,indent=2)+'\n').encode()
 if args.expect:require(typed_equal(result,read_json(args.expect.read_bytes())),'type-exact receipt mismatch')
 if args.output:
  with args.output.open('xb') as f:f.write(encoded)
 print(json.dumps({'status':'PASS','receipt_sha256':digest(encoded),'R':49023,'v2_Y':12,'full_Pell_zeros_materialized':0},sort_keys=True))

if __name__=='__main__':main()
