from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path
files=[P('research/ordinary13-qcube-unscale84/candidate.json'),P('research/ordinary13-aux-root87-36/candidate.json'),P('research/ordinary13-qcube-unscale84/README.md'),P('research/ordinary13-qcube93-model-draft/Ordinary13QCube93Arithmetic.lean.src'),P('Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean'),P('research/ordinary14-first-main-large-k-draft/FirstMainLargeK.lean'),P('research/ordinary13-eta-natural-norm-large-k-draft/EtaNaturalNormLargeK.lean.src'),P('Lean/DiophantineConsistency/Compact44/P73Converse.lean'),P('research/ordinary13-positive81-to83-model-draft/CarrierWitnessFacts.lean.src'),P('research/ordinary13-residue-root-switch-extraction-draft/ResidueRootSwitchExtract.lean.src'),P('Lean/DiophantineConsistency/BFS943/Trace75IntegralTransport.lean'),P('research/ordinary13-qcube93-model-draft/README.md')]
s=[f.read_text() for f in files];g84,g87=map(json.loads,s[:2]);assert [len(g['source']) for g in (g84,g87)]==[84,87]
assert g84['witnesses'][7]=='s' and g87['witnesses'][7]=='Y' and g84['witnesses'][8]==g87['witnesses'][8]=='r'
assert g84['witnesses'][:7]+g84['witnesses'][8:]==g87['witnesses'][:7]+g87['witnesses'][8:]
assert g84['fixed_numerals']==g87['fixed_numerals'];a,b=({row[0]:row for row in g['source']} for g in (g84,g87))
assert set(a)-set(b)=={'Y'} and set(b)-set(a)=={'M','g33','g34','folded_q3Bt'}
changed={'g32','Z','g39'}
for n in a.keys() & b.keys():
 if n not in changed:assert a[n]==b[n],n
for row in [['Y','*','q3','s'],['g32','*','qm','folded_g31'],['Z','-','g32','Bt'],['g39','*','qm','qm']]:assert a[row[0]]==row
for row in [['M','*','q3','qm'],['g32','*','M','folded_g31'],['g33','*','Y','qm'],['g34','+','g32','g33'],['folded_q3Bt','*','q3','Bt'],['Z','-','g34','folded_q3Bt'],['g39','*','M','M']]:assert b[row[0]]==row
def deps(rows,n):
 if isinstance(n,int):return set()
 if n not in rows:return {n}
 _,_,l,r=rows[n];return deps(rows,l)|deps(rows,r)
for n in ('A1','Fa','g72'):assert 'r' not in deps(a,n) and 'r' not in deps(b,n)
# Exact polynomial equalities with h=q³, Y=h*s, r_old=r-s.
def add(x,y,sgn=1):
 z=x.copy()
 for a,b in y.items():z[a]=z.get(a,0)+sgn*b
 return {a:b for a,b in z.items() if b}
def mul(x,y):
 z={}
 for a,b in x.items():
  for c,d in y.items():
   e=tuple(i+j for i,j in zip(a,c));z[e]=z.get(e,0)+b*d
 return {a:b for a,b in z.items() if b}
one={(0,)*7:1};h={(1,0,0,0,0,0,0):1};b0={(0,1,0,0,0,0,0):1};ell={(0,0,1,0,0,0,0):1};k={(0,0,0,1,0,0,0):1};r={(0,0,0,0,1,0,0):1};s0={(0,0,0,0,0,1,0):1};B={(0,0,0,0,0,0,1):1}
core=add(add(ell,k),r);core=add(core,mul(k,B),-1)
Z=add(mul(b0,core),B,-1); oldcore=add(core,s0,-1)
Zold=add(add(mul(mul(h,b0),oldcore),mul(mul(h,s0),b0)),mul(h,B),-1)
assert Zold==mul(h,Z)
rad=add(one,mul(ell,add(ell,k)));A=add(mul(Z,Z),mul(mul(b0,b0),rad),-1)
Aold=add(mul(Zold,Zold),mul(mul(mul(h,b0),mul(h,b0)),rad),-1)
assert Aold==mul(mul(h,h),A)
for i,needles in {3:['theorem positive_quotient_of_signed_norm','theorem cube_bezout','theorem cube_dvd_of_dvd_mul','ModelRelationCombining.sq_dvd_sq','natural_dvd_of_signed'],4:['theorem scaled_quotient'],5:['theorem first_main_large_k'],6:['theorem large_first_ordinate'],7:['private theorem tau_gt','(hk : 3 * s ≤ k) (hs : s ≤ ell)'],8:['theorem positive_target_root'],10:['theorem natural_dvd_of_signed']}.items():
 for needle in needles: assert needle in s[i],(i,needle)
# The unchanged actual positive 84 coordinate need not remain positive under
# r_old=r-s; this is a scalar control, not a graph-zero witness.
assert 1-2<0
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in files},'exact_graph_row_delta':True,'three_nonfirst_residuals_r_independent':True,'Zold_equals_q3_Z_symbolically':True,'first_residual_old_equals_q6_new_symbolically':True,'simple_predecessor_scalar_control':{'r':1,'s':2,'is_full_graph_zero':False},'lean_executed':False,'status':'Bounded source/mathematical audit only; graph zero maps, model casts and providers remain open.'},sort_keys=True,indent=2))
