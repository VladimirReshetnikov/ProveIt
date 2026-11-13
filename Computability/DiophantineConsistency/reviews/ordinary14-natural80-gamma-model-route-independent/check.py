#!/usr/bin/env python3
"""Independent source-interface and exact graph-cut audit; no Lean."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parents[2]
files={
'research/ordinary14-natural80-gamma-model-route/check_sources.py':'98e3d9d63a25b38aeff9eae02946ded17136456f5738c3c16f06b3060c6b0fff',
'research/ordinary14-natural80-gamma-model-route/result.json':'66891d7835a8908450fc2dbaad7f3e0b4dc2de0305b2554520b6052c4b4364d6',
'Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean':'0895f6e74b29c2cc2e4542d739b238352778750da62766819caeb105995fb794',
'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean':'374719597b3126504fc7b4daeb8ce08a7bae36c911ed37d8fee3d90ed324a5d5',
'Lean/DiophantineConsistency/ArithmeticPellClassification.lean':'77dc61a25a075c237ea36cc14a3e46c9832a1de827b84427679e268111a4cf78',
'Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean':'63ec2a49f8d7066dbd8647a663db4bbd7255abd3ca7c3cc0d4d7b3533a189b16',
'Lean/DiophantineConsistency/BFS943/Direct80IndexOne.lean':'db0462fd907b629d9720106cfd9ea19fc8fa9e74e659d8286a039affbdc50761',
'Lean/DiophantineConsistency/BFS943/TraceNormKpos.lean':'c8616ea29abed8cf4beceb426f202fb955557de43422647e47f0bf75df65c1b5',
'Lean/DiophantineConsistency/Compact44/DirectMainNorm.lean':'29c748582368b4ab2bcdb4b4cdd4f7890dda32f77718e33355b590b8f07b7fbd',
'Lean/DiophantineConsistency/Compact44/DirectMainProjection.lean':'913b54cea53402e9da91b2fb9e5c41dbbf9e5926be9531986fc08fe90163a956',
'research/ordinary14-74-ownzero-product-draft/OwnZeroProduct74.lean':'26404a26b78b3099ddaa407d2eed829d884568821e08a5c7780a1e0ac167a1db',
'research/ordinary14-74-ownzero-guard-strict-draft/OwnZeroGuardStrict74.lean':'d8d99e58177cdc6fde4fad5f79b577ce97023162656931691ce314141f98e1b8',
'research/ordinary14-74-factor-residues-draft/FactorResidues74.lean':'368e6e5f3db5693db859fdc85a9441f0d6378969563eec289c2c121e6b4b1d60',
'research/ordinary14-strict-k0-symbolic-source-draft/StrictK0Symbolic.lean':'7b694e0aa874a1d321cc348db26d2aa56a6dc6509b331b6bb3dfdd9c1d6ce31a',
'research/ordinary14-positive-guard74/candidate.json':'e70af4f896013695368180743f514c027faa86f8b3cedd5479b22e64e4c26093',
'research/ordinary14-natural-forced-gamma80/candidate.json':'136560324b95b3fda68d10ebe49bdba0a02e950e0bf6b7f1b1588baea4805bf5'}
s={}
for path,h in files.items():
 b=(D/path).read_bytes();assert hashlib.sha256(b).hexdigest()==h,path
 s[path.rsplit('/',1)[-1] if not path.endswith('candidate.json') else path]=b.decode()
def header(src,name):
 m=re.search(r'\btheorem\s+'+re.escape(name)+r'\b(.*?)\s*:=\s*by',src,re.S);assert m,name
 return ' '.join(m.group(1).split())
main=header(s['DirectMainNorm.lean'],'direct_main_orientation')
projection=header(s['DirectMainProjection.lean'],'direct_parts_positive')
for h in (main,projection):
 assert '(U X Y k eta G R : V)' in h and '(hU : 0<U)' in h.replace('0 < U','0<U')
 assert '(hY : 8≤Y)' in h.replace('8 ≤ Y','8≤Y') and '(hk : 0<k)' in h.replace('0 < k','0<k')
 assert '0<G' not in h.replace(' ','') and '0<G' not in h.replace(' ','')
assert 'magnitude (P,N)*magnitude (P,N)' in main and 'P=N+U*m' in main
idx=header(s['Direct80IndexOne.lean'],'impossible')
for token in ('(Y S X eta zeta m : V)','(hY : 1≤Y)','(hYS : Y≤S)','(heta : 0<eta)',
 '(hzeta : 0<zeta)','(hk : eta+zeta=2)','ycoord m (S*(X+1)-1)'):
 assert token in idx,token
assert 'def delta (b : V) : V := (b+1)*(b+3)' in s['ArithmeticPellRecurrence.lean']
assert 'theorem solution_index (b x y : V) (h : x*x=1+delta b*y*y)' in s['ArithmeticPellClassification.lean']
assert 'theorem positive_parameter_solution (Q x k : V) (hQ : 0<Q)' in s['ArithmeticPellFirstNorm.lean']
for name in ('first_index_ge_two','graph_rank_size'):
 h=header(s['TraceNormKpos.lean'],name);assert '(hv : ∀j,0<v j)' in h
strict=header(s['OwnZeroGuardStrict74.lean'],'strict_of_zero');assert '(hv : ∀ j, 0<v j)' in strict
unit=header(s['OwnZeroProduct74.lean'],'factor_units_of_zero')
for token in ('(hJ : 0<v 0)','(hw : 0<v 6)','(hs : 0<v 7)','(hmain :','(haux :','(hstrong :'):assert token in unit,token
assert '(hv :' not in unit and 'theorem restricted_residues' in s['FactorResidues74.lean']
assert 'theorem port_one_representation' in s['StrictK0Symbolic.lean'] and 'theorem kernel_model_pos' in s['StrictK0Symbolic.lean']
# Independently compare all graph rows under the partial shift. Four local
# ring cuts are checked exactly as sparse polynomials below.
a=json.loads(s['research/ordinary14-positive-guard74/candidate.json']);b=json.loads(s['research/ordinary14-natural-forced-gamma80/candidate.json'])
assert a['domain']=='strictly positive integers' and b['domain']=='nonnegative integers'
assert len(a['source'])==74 and len(b['source'])==80
old={r[0]:r[1:] for r in a['source']};new={r[0]:r[1:] for r in b['source']}
extra={'alpha','i','T','w','s','eta','kbase'}
assert set(new)-set(old)==extra and set(old)-set(new)=={'g52'}
for n in extra-{'kbase'}:assert new[n]==['+','n_'+n,1]
assert old['q']==['+',1,'qm'] and old['qF']==['-','q','F'] and new['qF']==['-','qm','n_F']
assert old['k']==['+','eta','zeta'] and new['kbase']==['+','eta','n_zeta'] and new['k']==['+','kbase',1]
assert old['g52']==['-','k','R'] and old['r0']==['-','g52',1] and new['r0']==['-','kbase','R']
assert old['guard_base']==['+','g27','qF'] and old['bt_quotient']==['*','qm','h']
assert new['guard_base']==['-','g27','n_F'] and new['bt_quotient']==['*','qm','n_h']
rename={'J':'n_J','f':'n_f','r':'n_r','y':'n_y','gamma':'n_gamma'}
for n in set(old)&set(new)-{'qF','k','r0','guard_base','bt_quotient'}:
 op,x,y=old[n];assert new[n]==[op,rename.get(x,x),rename.get(y,y)],n
# Exact algebra, independent of the later Lean evaluation/embedding proof.
def cn(n):return {():n} if n else {}
def v(n):return {(n,):1}
def add(a,b):
 z=dict(a)
 for m,w in b.items():z[m]=z.get(m,0)+w
 return {m:w for m,w in z.items() if w}
def neg(a):return {m:-w for m,w in a.items()}
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 z={}
 for i,x in a.items():
  for j,y in b.items():
   m=tuple(sorted(i+j));z[m]=z.get(m,0)+x*y
 return {m:w for m,w in z.items() if w}
b0,nf,eta,nz,R,g,nh=map(v,('b','nF','eta','nZ','R','g','nH'))
qf=sub(add(cn(1),b0),add(nf,cn(1)));assert qf==sub(b0,nf)
kold=add(eta,add(nz,cn(1)));kbase=add(eta,nz)
assert kold==add(kbase,cn(1)) and sub(sub(kold,R),cn(1))==sub(kbase,R)
assert sub(add(g,qf),mul(b0,add(nh,cn(1))))==sub(sub(g,nf),mul(b0,nh))
# Direct80IndexOne: S=a+1, X=0 gives base (a+1)*(0+1)-1=a.
for aa in range(100):
 assert (aa+1)*(0+1)-1==aa
print(json.dumps({'scope':'bounded source interface and exact graph cuts; no Lean or model theorem',
 'pinned_sources':len(files),'graph_parent_gates':74,'graph_target_gates':80,
 'partial_shift_cuts':4,'main_orientation_has_no_G_positivity_premise':True,
 'index_one_S':'a+1','index_one_X':0,'all_positive_client_caveats_checked':True},sort_keys=True,indent=2))
