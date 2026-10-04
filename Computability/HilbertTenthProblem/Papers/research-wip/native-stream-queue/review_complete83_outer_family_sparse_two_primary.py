#!/usr/bin/env python3
"""Independent finite checks; predecessor programs are authenticated, never run."""
import argparse
import hashlib
import json
from pathlib import Path

STEM=Path('/tmp/complete83_outer_family_sparse_two_primary')
AUTHOR_PINS={'md':'bda0275af08ceaf1637b6bfa3ba8a8347205f5a674783cec7105ca263bf3fb97','py':'f68c311277b30f432bb8e89bee66f96601825b8d11c112049f736c070f43f0e2','json':'3c1ec8075c9e6437717b4f1b68a3137b23070c5d5b69ffb080db83f3f17d1e82'}
PAPERS=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers')

def require(truth,message):
 if not truth:raise RuntimeError(message)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def v2(n):
 require(n>0,'valuation domain');return (n&-n).bit_length()-1

def clauses():
 results=[]
 for a in (2,3,4):
  for k in (2,3,5,8):
   w=max(2,(k+1).bit_length())
   # Distinct nine-letter tuples, not actual allowed-machine windows.
   selectors=[]
   for index in range(k):
    letters=[];rem=index
    for _ in range(9):rem,letter=divmod(rem,a);letters.append(letter)
    exponents={0}|{w*(1+a*j+letters[j]) for j in range(9)}|{w*(9*a+j) for j in range(1,5)}
    require(len(exponents)==14,'fourteen distinct selector bits')
    selectors.append(sum(1<<e for e in exponents))
   payload=[1<<(w*j) for j in range(1,9*a+1)]
   anchors=[1<<(w*j) for j in range(9*a+1,9*a+5)]
   for padding in (0,1,7):
    mask=(1<<w)-2+sum(1<<(w*j) for j in range(1,9*a+5+padding))
    p=mask.bit_count();N=2*p+12*a+3;dummy_count=N-k-9*a-4
    require(p==w+9*a+3+padding and dummy_count>=1,'mask and native count')
    E0=k+12*a+dummy_count-1;M=E0+3*a+1
    require(M==N+6*a-4==2*w+36*a+5+2*padding and M>=k+15*a,'layout identities')
    total=sum(selectors+payload+anchors)
    target=max(4*(N+2)*(2*total+6)+8,2*mask+4,16)
    b=1
    while (1<<b)<target:b*=5
    require(b>w*(9*a+4+padding) and b>=125 and M<3*b,'radix implications')
    weight=sum(c.bit_count() for c in selectors+payload+anchors)
    require(weight==14*k+9*a+4 and 2*weight+6<=30*M,'coefficient population sum')
    H=51*M+3*a+1;T1=105*M+4*a+2;T2=159*M+4*a+3;g=T2+27*M+1
    L=1
    while L<=g+27*M:L*=5
    # Every coefficient is positive; verify unique least term valuation directly.
    terms=[(3*a,1),(H+a,1),(8*M,1),(24*M,1),(g,1),(L+H,1)]
    locations=list(range(k))
    for row in range(3):
     for col in range(3):
      for color in range(a):locations.append(k+3*a+(2-row)*3*a+(2-col)*a+color)
    locations.extend([M,3*M,9*M,27*M])
    for position,coefficient in zip(locations,selectors+payload+anchors):
     terms.extend([(T1-position,coefficient),(T2-position,coefficient)])
    valuations=[e*b+v2(c) for e,c in terms]
    require(valuations.count(3*a*b)==1 and min(valuations)==3*a*b,'unique least monomial')
    results.append({'a':a,'k':k,'w':w,'padding':padding,'mask_population':p,'N':N,'M':M,'b':b,'L':L,'coefficient_population':weight,'K_population_upper':2*weight+6,'K_valuation':3*a*b})
 return results

def subtraction_cases():
 count=0
 for T in range(2,4097,2):
  h=v2(T)
  for c in range(1,min((1<<h)-1,257)+1):
   require((T-c).bit_count()==T.bit_count()-1+h-(c-1).bit_count(),'exact subtraction population')
   count+=1
 return count

def deficit_cases():
 count=0;max_loss=0;d=4096;logd=12
 for v in (5,9,17,375):
  for unit in range(1,64,2):
   for z in (1,5,17,513,4*d-3):
    K=unit<<v;F=K*z;P=F.bit_count()
    require(v2(F)==v and P<=K.bit_count()*z.bit_count(),'odd product valuation/population')
    for shape,top in [('plus',9),('minus',8)]:
     for eps in range(-1,top+1):
      first=6*F+4*z+2-eps
      tail=[6*F-4,2*F-6] if shape=='plus' else [8*F-25,32]
      loss=sum(x.bit_count() for x in [first]+tail)
      require(first>0 and loss<=5*P+3*v+logd+6,'common deficit population bound')
      require((6*F-4).bit_count()==(6*F).bit_count()+v-2,'sixfold subtraction')
      require((2*F-6).bit_count()==P+v-2,'twofold subtraction')
      require((8*F-25).bit_count()==P+v,'eightfold subtraction')
      max_loss=max(max_loss,loss);count+=1
 return {'cases':count,'max_loss':max_loss,'d':d,'valuations':[5,9,17,375],'scope':'algebraic deficit tests, not actual compiler coefficients'}

def uniform_bounds():
 b=125
 require((639*b*b)**2<1<<b,'base logarithm comparison')
 require((b+1)**4<2*b**4,'monotone logarithm ratio')
 # ln(2)>1/2 gives151/ln(2)<302<456; this rational check records the derivative margin.
 require(302<456,'derivative constant margin')
 tested=0
 for b in range(125,1001):
  require((639*b*b)**2<1<<b,'finite logarithm corroboration')
  require(151*b*5+4560+6*b<1065*b,'half-cell rational bound')
  tested+=1
 return {'base_b':125,'base_left':(639*125**2)**2,'base_right':2**125,'ratio_left':126**4,'ratio_right':2*125**4,'finite_b_cases':tested,'exact_half_cell_reduction':'304*b>4560'}

def main():
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args()
 require(bool(a.output)^bool(a.expect),'choose writer or replay')
 require(set(AUTHOR_PINS)=={'md','py','json'},'await frozen author pins')
 authentication=[]
 for ext,pin in AUTHOR_PINS.items():
  path=STEM.with_suffix('.'+ext);raw=path.read_bytes();require(sha(raw)==pin,'frozen author '+ext)
  authentication.append({'name':path.name,'bytes':len(raw),'sha256':pin})
 author=json.loads(STEM.with_suffix('.json').read_text())
 require(author['helper_sha256']==AUTHOR_PINS['py'],'author helper byte binding')
 dependencies=[]
 for item in author['dependencies']:
  raw=(PAPERS/item['path']).read_bytes()
  require(len(raw)==item['bytes'] and sha(raw)==item['sha256'],'dependency bytes')
  dependencies.append(item)
 # The source snippets were read directly; their exact bytes remain available for independent audit.
 reads=[]
 for name,start,end in [('verification/explore_fixed_raw_universal_76.py',94,144),('verification/explore_fixed_raw_universal_78.py',162,208),('1980/FIXED_RAW_UNIVERSAL_77_PROOF.md',28,65)]:
  raw=(PAPERS/name).read_bytes();part=b''.join(raw.splitlines(keepends=True)[start-1:end])
  reads.append({'path':name,'sha256':sha(raw),'bytes':len(raw),'start':start,'end':end,'span_sha256':sha(part)})
 result={'schema':'independent sparse two-primary review v1','source_sha256':sha(Path(__file__).read_bytes()),'author_authentication':authentication,'authenticated_dependencies':dependencies,'inert_source_spans':reads,'fresh_clause_cases':clauses(),'subtraction_cases':subtraction_cases(),'deficit_cases':deficit_cases(),'uniform_bounds':uniform_bounds(),'scope':{'compiler_executed':False,'predecessor_program_run':False,'actual_allowed_windows':False,'packed_index_materialized':False,'odd_primary_success':False,'source_zero_claim':False},'status':'PASS'}
 raw=(json.dumps(result,indent=2,sort_keys=True)+'\n').encode()
 if a.output:
  with a.output.open('xb') as f:f.write(raw)
 else:require(raw==a.expect.read_bytes(),'exact reviewer receipt')
 print(json.dumps({'status':'PASS','clause_cases':len(result['fresh_clause_cases']),'subtraction_cases':result['subtraction_cases'],'deficit_cases':result['deficit_cases']['cases'],'receipt_sha256':sha(raw)}))
if __name__=='__main__':main()
