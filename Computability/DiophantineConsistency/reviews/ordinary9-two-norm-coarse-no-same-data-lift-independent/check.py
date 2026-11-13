from pathlib import Path
from hashlib import sha256
import json,sys,subprocess,itertools,random
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary9-two-norm-coarse-no-same-data-lift-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
for name in ('research/ordinary9-two-norm-coarse-no-same-data-lift','reviews/ordinary13-eta-zeta84-unshift-i-coarse-bounds-independent','reviews/ordinary9-shifted-free-aux-two-norm64-independent'):
 p=Path(name);assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
s=Path('Lean/DiophantineConsistency/Compact44/P72Exact.lean').read_text()
# Exact P72 parameter order and all 18 named premises, including positive eta.
assert 'theorem indices_ordinary (q X Y k R g c a y0 i\' f T u n s μ m η : V)' in s
for token in ('(hq3 : 3 ≤ q)','(hX : 0 < X)','(hy0 : 0 < y0)','(hYq : Y = q * (q * q) * y0)',
 '(hη : 0 < η)','(hc : c = η + Y * k)','(hi\' : 0 < i\')','(hf : 0 < f)',
 '(ha : a = X * Y + Y)','(hR26 : 26 ≤ R)','(hny : 2 * ycoord n',
 '(hks : k = 2 * n + 4 *','(hRμ : R + 1 < μ)','(hnmod : (2 * n) % μ = R + 1)',
 '(hmy : ycoord m a = c)','(hg : g * g = 1 + delta a * c * c)',
 '(hs\' : (i\' * c * c)','(haux :','absdiff (f * f * (T * c) + u) (f * f * R + c)',
 '13 ≤ n ∧ n < m ∧ m = R ∧ 2 * n = R + 1'):
 assert token in s,token
parent=json.loads(Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text());nine=json.loads(Path('research/ordinary9-shifted-free-aux-two-norm64/candidate.json').read_text())
assert nine['witnesses']==['n_J','n_F','n_alpha','n_w','n_s','n_r','n_eta','n_zeta','n_gamma']
rows={r[0]:r[1:] for r in parent['source']}
for name,row in {'kbase':['+','n_eta','n_zeta'],'k':['+','kbase',1],'c':['+','n_eta','kY'],'R':['+','g47','g50'],'g72':['-','g71','Q'],'V':['-','g76','c'],'Fa':['-','y2','g82']}.items():assert rows[name]==row
L=2172;n=L*(2*L+1);m=n+L;q=128;R=2*n-1;mu=q**4
assert (n,m,R,mu)==(9437340,9439512,18874679,268435456)
assert m!=R and 26<=R and R+1<mu and 2*n%mu==R+1
# The first/main/strong factors exclude -1; auxiliary is then the remaining
# integer unit +1 because the product equals 1.
for b,z,x,s0,k in itertools.product(range(4),repeat=5):
 Y=(1+b)**3*s0;ell=x*Y*Y*k
 assert (1+z*z-b*b*(1+ell*(ell+k)))%4!=3
for U,a,c,z in itertools.product(range(4),repeat=4):assert (1+z*z-U*U*(1+(a*a+4*a+3)*c*c))%4!=3
for I,a,f in itertools.product(range(4),repeat=3):assert (1+I*I-(a*a+4*a+3)*(f*f-1))%4!=3
# More general independent absdiff identity: for integer V=A-B and y>=|V|,
# u=y−V is natural and both P72 distances are exactly |V| and y.
count=0
for V in range(-60,61):
 for B in range(max(0,-V),max(0,-V)+8):
  A=B+V
  for y in range(abs(V),abs(V)+5):
   u=y-V;assert u>=0 and abs(A-B)==abs(V) and abs(A+u-B)==y
   count+=1
# Check y=0 impossible and y>=|V| for bounded exact auxiliary norms.
aux=0
for I in range(2,20):
 for V in range(-25,26):
  for y in range(30):
   if y*y-I*I*(y*y-V*V)==1:
    assert y>=1 and y>=abs(V);aux+=1
print(json.dumps({'author_and_two_independent_predecessor_receipts_reproduced':True,'P72_all_named_hypotheses_and_parameter_order_inspected':True,'unit_negative_sign_cases':1344,'signed_to_absdiff_controls':count,'auxiliary_norm_controls':aux,'coarse_n_m_R_mu':[n,m,R,mu],'conditional_on_source_theorem_and_witness':True,'fixed_compact_or_global_zero_nonequivalence_proved':False,'lean_executed':False},sort_keys=True,indent=2))
