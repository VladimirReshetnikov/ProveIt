#!/usr/bin/env python3
"""Independent final audit: standard library only; no symbolic-algebra package."""
from pathlib import Path
from math import comb
from fractions import Fraction
from collections import Counter
import hashlib,json

def trim(a):
 a=list(a)
 while a and a[-1]==0:a.pop()
 return a

def add(a,b,mod=None):
 c=[(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))]
 return trim([x%mod for x in c] if mod else c)

def mul(a,b,mod=None):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return trim([x%mod for x in c] if mod else c)

def derivative(a):return [i*a[i] for i in range(1,len(a))]
def translate_one(a):return [sum(comb(n,k)*a[n] for n in range(k,len(a))) for k in range(len(a))]
def vp(x,p):
 assert x
 ans=0
 while x%p==0:ans+=1;x//=p
 return ans

def newton(a,p):
 pts=[(i,vp(c,p)) for i,c in enumerate(a) if c]
 hull=[]
 for c in pts:
  while len(hull)>=2:
   a,b=hull[-2:]
   if (b[1]-a[1])*(c[0]-b[0]) >= (c[1]-b[1])*(b[0]-a[0]):hull.pop()
   else:break
  hull.append(c)
 return hull

def compositions(n,k):
 if k==1:yield (n,)
 else:
  for a in range(n+1):
   for q in compositions(n-a,k-1):yield(a,)+q

ROOT=Path(__file__).resolve().parents[1]
path=ROOT/'data/lattice_certificates.json'
data=json.loads(path.read_text())
profiles=data['eight_term_open_global']['profile_certificates']
seen=set();counts=Counter();failed=[]
for i,c in enumerate(profiles):
 nu=tuple(c['residue_multiplicities']);assert nu not in seen;seen.add(nu)
 even=nu[0]+nu[2]
 predicted=9 if even%4==2 else (7 if even%4==0 and len({x%2 for x in nu})==1 else 8)
 actual=c['maximum']
 if predicted!=actual:failed.append({'profile':nu,'predicted':predicted,'actual':actual})
 assert sum(c['quotient_rank_increments'])==8
 assert [k for k,d in enumerate(c['quotient_rank_increments']) if d]==c['rank_increase_indices']
 assert max(c['rank_increase_indices'])==actual
 counts[actual]+=1
assert seen==set(compositions(8,4)) and len(seen)==165 and not failed
assert dict(counts)=={7:23,8:100,9:42}

P=[2049,128,3,-128,-6,0,54,0,-235,0,183]
A=[-1,3,-1,3,-3,-1,-1,0,3]
B=[3,2,-3,-3,2,-3,-2,3,0,-1]
bez=add(mul(A,P,7),mul(B,derivative(P),7),7)
assert bez==[1] and P[-1]%7==1
translated=translate_one(P)
assert translated==[2048,0,2048,9728,22784,33280,31904,20080,8000,1830,183]
hull=newton(translated,2)
assert hull==[(0,11),(9,1),(10,0)]
Q=[2045,20,-56,84,-70,28,0,-4,1]
assert translate_one(Q)==[2048,0,0,0,0,0,0,4,1]
assert newton(translate_one(Q),2)==[(0,11),(8,0)]

report={
 'status':'passed',
 'audited_report':'main_body.tex',
 'report_sha256_at_read':hashlib.sha256((ROOT/'main_body.tex').read_bytes()).hexdigest(),
 'certificate_file':'data/lattice_certificates.json',
 'certificate_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
 'classification':{'profiles_checked':165,'complete_coverage':True,'duplicates':0,'mismatches':failed,'maxima_distribution':dict(sorted(counts.items())),'all_rank_increment_sums_equal_eight':True},
 'nine_root_witness':{'coefficient_count':sum(bool(x) for x in P),'translation_verified':True,'newton_vertices':hull,'root_depths':{'10/9':9,'1':1},'mod_7_bezout_remainder':bez,'leading_coefficient_mod_7':P[-1]%7,'squarefree_certificate_valid':True},
 'same_mod_2_example':{'translation_verified':True,'newton_vertices':newton(translate_one(Q),2),'eight_roots_depth':'11/8'},
}
print(json.dumps(report,indent=2))
