from pathlib import Path
from hashlib import sha256
import itertools,json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary9-two-norm-coarse-no-same-data-lift')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-eta-zeta84-unshift-i-coarse-bounds-zero')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
s=Path('Lean/DiophantineConsistency/Compact44/P72Exact.lean').read_text()
for t in ('theorem indices_ordinary','(hη : 0 < η)','(hc : c = η + Y * k)',
 '(hR26 : 26 ≤ R)','(hny : 2 * ycoord n','(hks : k = 2 * n + 4 *',
 '(hnmod : (2 * n) % μ = R + 1)','(hmy : ycoord m a = c)',
 '(hs\' : (i\' * c * c)', 'm = R ∧ 2 * n = R + 1'):
 assert t in s,t
g=json.loads(Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text())
h=json.loads(Path('research/ordinary9-shifted-free-aux-two-norm64/candidate.json').read_text())
r={n:(op,a,b) for n,op,a,b in g['source']}
for n,row in {'k':('+','kbase',1),'c':('+','n_eta','kY'),'a':('+','E','Y'),
 'R':('+','g47','g50'),'g72':('-','g71','Q'),'V':('-','g76','c'),
 'Fa':('-','y2','g82'),'out':('-','P0123',1)}.items():assert r[n]==row
assert len(h['witnesses'])==9 and h['witnesses'][7]=='n_zeta'
L=2172;n=L*(2*L+1);m=n+L;R=2*n-1;q=128;mu=q**4
assert (n,m,R,mu)==(9437340,9439512,18874679,268435456)
assert m!=R and 26<=R and R+1<mu and (2*n)%mu==R+1 and m%7==5
# Main/first/strong mod-4 negative-unit exclusions, independent of hidden ports.
for b,z,x,s,k in itertools.product(range(4),repeat=5):
 Y=(1+b)**3*s;ell=x*Y*Y*k
 assert (1+z*z-b*b*(1+ell*(ell+k)))%4!=3
for u,a0,c,d in itertools.product(range(4),repeat=4):
 assert (1+d*d-u*u*(1+(3+4*a0+a0*a0)*c*c))%4!=3
for I,a0,f in itertools.product(range(4),repeat=3):
 assert (1+I*I-(3+4*a0+a0*a0)*(f*f-1))%4!=3
# Independent finite controls for the aux-to-absdiff witness conversion.
count=0
for I in range(2,12):
 for V in range(-15,16):
  for y in range(0,25):
   if y*y-I*I*(y*y-V*V)!=1:continue
   assert y>=abs(V)
   for B in range(20):
    A=V+B
    if A<0:continue
    u=y-V;assert u>=0 and abs(A+u-B)==y and abs(A-B)==abs(V)
   count+=1
assert count>0
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'coarse_witness_receipt_reproduced':True,'fixed_n_m_R_mu':{'n':n,'m':m,'R':R,'mu':mu},
 'P72Exact_indices_ordinary_source_hypotheses_observed':True,'generic_unit_sign_exclusions':True,
 'aux_absdiff_conversion_controls':count,'conditional_obstruction':'same nine first/main coordinates at specified noncompact ports, assuming P72Exact source theorem is sound in standard naturals',
 'actual_compact_or_existential_nonequivalence_proved':False,'lean_executed':False},sort_keys=True,indent=2))
