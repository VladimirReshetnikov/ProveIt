from pathlib import Path
import hashlib,json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-zeta-zero-norm-large-k-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==h,p
P=Path('research/ordinary13-zeta-zero-norm-large-k-draft')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(P/'check.py')])==(P/'receipt.json').read_bytes()
a=(P/'ZetaZeroNormLargeK.lean.src').read_text()
for x in ['(hDelta : (X*Y+Y+2)*(X*Y+Y+2)=Delta+1)', '(hmain : d*d=1+Delta*(k+Y*k)*(k+Y*k))', 'have hcEq : c=2+2*Y', 'apply no_main_square A c Delta d hA hc hcA', '(hk : 0<k)', 'two_le_ordinate (m-1) tau k hk hn\'', 'first_ordinate_large m tau k hm hkgt hn']:
 assert x in a,x
square=Path('research/ordinary14-natural81-combined-slim-overlay/source/MainSquareGap.lean.src').read_text()
for x in ['theorem no_main_square (A c Delta d : V) (hA : 0<A) (hc : 1<c)','(hbound : c<2*A) (hDelta : A*A=Delta+1)','(hnorm : d*d=1+Delta*c*c)']:
 assert x in square,x
first=Path('research/ordinary14-natural81-combined-slim-overlay/source/AuxRootBounds.lean.src').read_text()
assert 'theorem first_ordinate_large (m tau k : V) (hm : 0<m) (hk : 2<k)' in first
assert '(hn : tau*tau=1+m*(m+1)*k*k) : 8*m+4≤k' in first
pell=Path('Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean').read_text()
assert 'def discriminant (q : V) : V := (q+1)*(q+2)' in pell
assert 'theorem two_le_ordinate (q x k : V) (hk : 0<k)' in pell
print(json.dumps({'k2_square_gap_and_strict_bounds_checked':True,'first_norm_descent_interfaces_checked':True,'positive_k_explicit':True,'graph_zero_binding_proved':False,'lean_executed':False},indent=2,sort_keys=True))
