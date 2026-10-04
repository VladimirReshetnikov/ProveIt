#!/usr/bin/env python3
"""Independent full-source audit of the refuted83 outer slack chart."""
import argparse,hashlib,json
from collections import Counter
from fractions import Fraction
from pathlib import Path
AUTHOR_PINS = {'py':'8e3c335f157e9a237791eeaceffec94415ba9ce8c2638d89d023213cfcbd0fd5','json':'9b0b05ad969eec99ca761898149ec3798a803fbb591a7bf462bf82a15090c207','md':'6623a525ab1b0376b1d6a452f8e5618f8e1f64f0a255fdcbcc97611dd3598259'}
PARENT_PINS={
 'complete84_scaled_strong_output.py':'8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
 'complete75_weakened86_all_input_collapse.py':'ab7a3280915a569a6fb18adc3ab5acb0a917748664d146a6a655eb3c5ac16685',
 'complete75_weakened86_all_input_collapse.json':'5a77d0d95ad4ea3c61c3d5c82c9c159c7348a1ad3be2b1057a51e05b1c212736',
 'complete75_weakened86_all_input_collapse.md':'46f3e0f25fc4efeb3f8129b77c3df988283c7a818ee2af330e8e8f460dc8d017',
 'complete75_weakened86_auxiliary_sign_lift.md':'491ac3c3755efed1c6c89f7e07a752c25fb040859cac8c07d7db25e803c62c53',
 'complete75_weakened86_infinite_outer_family.md':'74b6c968500c5177440096bd3da3c9c07f9208f10aea79cad73554e9814bf1a2',
 'complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
 'complete75_weakened86_rejecting_compiler.md':'186fc8a89c99455361fd0eb0b90d53c1fa90af32191a741c02e950d3bb0d8e78'}
def check(v,msg):
 if not v:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def same(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(same(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
 return a==b
def pairs(ps):
 d={}
 for k,v in ps:check(k not in d,'duplicate JSON key');d[k]=v
 return d
def read(p):return json.loads(p.read_text(),object_pairs_hook=pairs)
def step(op,a,b):
 if op=='+':return a+b
 if op=='-':return a-b
 check(op=='*','operator');return a*b
# Independent exponent-vector coefficient arithmetic, only for the changed cuts.
class R:
 def __init__(self,c):self.c={k:v for k,v in c.items() if v}
 def __add__(self,b):
  z=dict(self.c)
  for k,v in b.c.items():z[k]=z.get(k,0)+v
  return R(z)
 def __sub__(self,b):return self+R({k:-v for k,v in b.c.items()})
 def __mul__(self,b):
  z={}
  for k,v in self.c.items():
   for l,w in b.c.items():
    key=tuple(x+y for x,y in zip(k,l));z[key]=z.get(key,0)+v*w
  return R(z)
 def __eq__(self,b):return self.c==b.c
def constants(n):return R({(0,)*4:n})
def variable(i):return R({tuple(int(j==i) for j in range(4)):1})
def cut_proof():
 q,F,Z,b=[variable(i) for i in range(4)];one=constants(1)
 old_C=((q-F)-Z)-(b-Z);new_C=(q-F)-b
 old_gap=(q-one)*(q-F)+((q-F)-Z);new_gap=q*(q-F)-Z
 check(old_C==new_C,'C cut coefficients');check(old_gap==new_gap,'gap cut coefficients')
 return {'C_terms':len(new_C.c),'gap_terms':len(new_gap.c),'all_ring':True}
def audit(p):
 seen=set(p['free']);parents={};ops=Counter()
 check(len(seen)==len(p['free']),'distinct inputs')
 deg={x:0 if x in p['fixed_numerals'] else 1 for x in p['free']}
 for d,op,a,b in p['source']:
  check(type(d)is str and d not in seen and op in ('+','-','*'),'SSA')
  for x in (a,b):check(type(x)is int or type(x)is str and x in seen,'closure')
  da=deg[a] if type(a)is str else 0;db=deg[b] if type(b)is str else 0
  deg[d]=da+db if op=='*' else max(da,db)
  parents[d]=[x for x in (a,b) if type(x)is str];seen.add(d);ops[op]+=1
 live={p['output']};queue=list(live)
 while queue:
  for x in parents.get(queue.pop(),[]):
   if x not in live:live.add(x);queue.append(x)
 check(live==seen,'all rows and inputs live')
 return {'M':ops['*'],'A':ops['+']+ops['-'],'total':sum(ops.values())},deg[p['output']]
def evaluate(p,v):
 e=dict(v)
 for d,op,a,b in p['source']:e[d]=step(op,e[a] if type(a)is str else a,e[b] if type(b)is str else b)
 return e

def verify(root,author):
 check(AUTHOR_PINS is not None,'author freeze required')
 for name,h in PARENT_PINS.items():check(sha(root/name)==h,'dependency pin '+name)
 for ext,h in AUTHOR_PINS.items():check(sha(author/('complete83_outer_slack_collapse.'+ext))==h,'author pin '+ext)
 receipt=read(author/'complete83_outer_slack_collapse.json');parent=read(root/'complete84_scaled_strong_output.json')['packet'];child=receipt['packet']
 check(receipt['source_sha256']==AUTHOR_PINS['py'] and same(receipt['pins'],PARENT_PINS),'self/dependency receipt pins')
 expected=[]
 edits={'C_after_alpha':['C_after_alpha','-','q_minus_F','alpha_sum'],
        'gap_product':['gap_product','*','q','q_minus_F'],
        'gap':['gap','-','gap_product','Z']}
 for row in parent['source']:
  if row[0]!='q_minus_FZ':expected.append(edits.get(row[0],row))
 check(same(expected,child['source']),'all83 literal rows')
 for key in ('free','witnesses'):
  check(child[key]==['alpha_sum' if z=='alpha' else z for z in parent[key]],'exact '+key)
 for key in ('factors','fixed_numerals','ordinary_input','output'):check(same(child[key],parent[key]),key)
 counts=Counter(x for row in parent['source'] for x in row[2:] if type(x)is str)
 check(counts['alpha']==1 and counts['q_minus_FZ']==2 and counts['gap_product']==1,'all changed consumers')
 pdeg=parent['exact_degree'];check(pdeg==187 and child['exact_degree']==pdeg,'inherited degree')
 ledger,upper=audit(child);check(ledger=={'M':47,'A':36,'total':83} and ledger==child['ledger'],'paid ledger')
 check(upper==197==child['syntactic_degree_upper'] and len(child['witnesses'])==18,'degree/interface')
 cuts=cut_proof()
 # Two proved cuts imply all other retained rows agree by identical paid definitions.
 check([r for r in child['source'] if r[0] not in edits]==[r for r in parent['source'] if r[0] not in edits and r[0]!='q_minus_FZ'],'remaining definitions')
 # Validate the actual complete finalizer, including early norm products.
 scalar_factors=dict(zip(child['factors'],[1,1,1,1,-1,-1,11]));scalar_factors['A']=11
 final_names={'norm_pair','norm_triple','norm_four','norm_product','all_units','seven_units','polynomial'}
 final_rows=[r for r in child['source'] if r[0] in final_names]
 check(len(final_rows)==7,'seven paid finalizer gates')
 for d,op,a,b in final_rows:scalar_factors[d]=step(op,scalar_factors[a],scalar_factors[b])
 check(scalar_factors[child['output']]==0,'minus/minus complete output')
 cases=0;rational=0;retained=0
 for j in range(40):
  v={k:((j+5)*(n+3)%13)-6 for n,k in enumerate(child['free'])}
  if j%2:
   v={k:Fraction(x,n%4+1) for n,(k,x) in enumerate(v.items())};rational+=1
  pv={k:v['alpha_sum']-v['Z'] if k=='alpha' else v[k] for k in parent['free']}
  a=evaluate(parent,pv);b=evaluate(child,v)
  for d,_,_,_ in child['source']:
   if d!='gap_product':check(a[d]==b[d],'complete signed register identity '+d);retained+=1
  cases+=1
 return {'status':'PASS','source_sha256':sha(Path(__file__)),'author_pins':AUTHOR_PINS,'dependency_pins':PARENT_PINS,
  'ledger':ledger,'witnesses':18,'exact_degree':187,'syntactic_degree_upper':197,
  'cut_proof':cuts,'literal_rows':83,'complete_finalizer_rows':7,
  'whole_cases':cases,'rational_cases':rational,'retained_register_value_checks':retained,
  'whole_identity':'P83(alpha_sum)=P84(alpha_sum-Z)',
  'forward_positive_map':'alpha_sum=alpha+Z','inverse_only_if':'alpha_sum>Z',
  'zero_family_factor_cut':['1','1','1','1','-1','-1','Delta'],
  'scope':'Full source/algebra/degree audit; no full compiler zero materialized. All-input existence requires the corrected signed CRT/auxiliary argument in the companion and independent mathematical review.'}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--author-root',type=Path)
 out=ap.add_mutually_exclusive_group(required=True);out.add_argument('--output',type=Path);out.add_argument('--expect',type=Path)
 a=ap.parse_args();r=verify(a.root,a.author_root or a.root)
 if a.expect:check(same(r,read(a.expect)),'typed receipt')
 else:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print('PASS: all83 source rows, 47M36A, 18 witnesses, exact degree187, 40 signed/rational whole checks.')
if __name__=='__main__':main()
