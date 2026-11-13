from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path;p=P('research/ordinary13-positive84-division-model-draft')
files=[p/'Positive84Division.lean.src',p/'README.md',p/'check.py',p/'receipt.json',P('research/ordinary13-residue-three-projection-model-draft/ResidueThreeProjection.lean.src'),P('research/ordinary14-modified-carrier-model-facts-draft/ModifiedCarrierFacts.lean'),P('Lean/DiophantineConsistency/ArithmeticAdaptiveMersenne2011.lean'),P('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean'),P('research/ordinary13-positive83-to84-model-draft/Positive83To84Transport.lean.src'),P('research/ordinary13-positive83-to84-model-draft/Positive83To84Bridge.lean.src'),P('research/ordinary13-qcube-unscale84/candidate.json'),P('research/ordinary13-eta-zero-growth-model-draft/EtaZeroGrowth.lean.src'),P('Lean/DiophantineConsistency/Compact44/FreeJPowerFinish.lean'),P('Lean/DiophantineConsistency/Compact44/FreeJPowerProjection.lean')]
s=[f.read_text() for f in files];g=json.loads(s[10]);rows={r[0]:r for r in g['source']};assert len(g['source'])==84 and g['witnesses'][6:8]==['X','s']
for row in [['q','+',1,'qm'],['Y','*','q3','s'],['U','*','Y','q2'],['E','*','X','Y'],['g55','*','E','q'],['g56','+','g54','g55'],['shift','-','g56','r0']]:assert rows[row[0]]==row
for n in ['def OrientedIndexCut','∃ R main w : V','k84 v=R+1+4*(v 6*Y84 p v*Y84 p v)*w',
 'H*(U*v 12+v 6*Y84 p v*q84 p v+R+1)','theorem three_of_oriented','ResidueThreeProjectionDraft.q_dvd_threeX',
 'def IndexGraphCut','def PowerGraphCut','theorem divCut_of_index_and_power',
 'ModifiedCarrierFactsDraft.compact_beta_divides_X (v 0) R (v 6) hpow hthree\'']:
 assert n in s[0],n
cut=s[0].split('def OrientedIndexCut',1)[1].split('/-- Source-only',1)[0]
assert 'q84 p v∣v 6' not in cut and 'zero84_to83' not in s[0] and 'zero83_to84' not in s[0]
assert 'theorem q_dvd_threeX' in s[4] and 'X*Y*q+R+1' in s[4]
assert 'theorem compact_beta_divides_X' in s[5] and '(hX : X=Exp.exp R)' in s[5]
assert '(hq : q=(Exp.exp d-1)*J+1) (hdiv : q∣3*Exp.exp R) : q∣Exp.exp R' in s[6]
assert 'def betaNat : ℕ := 2^(67*8807)-1' in s[7] and 'theorem beta_identity' in s[7]
assert 'def q84 (p : Fin 4 → ℕ) (v : Fin 13 → V) : V := 1+v 0*(p 0:V)' in s[0]
assert 'def q (p : Fin 4 → ℕ) (v : Fin 13 → V) : V := 1+v 0*(p 0:V)' in s[8]
# Exact polynomial identity: with Y=q³*s and H=3+4Y(X+1),
# H*X - 3*X is q times an explicitly displayed polynomial.
def add(x,y,sgn=1):
 z=x.copy()
 for k,n in y.items():z[k]=z.get(k,0)+sgn*n
 return {k:n for k,n in z.items() if n}
def mul(x,y):
 z={}
 for a,b in x.items():
  for c,d in y.items():
   k=tuple(i+j for i,j in zip(a,c));z[k]=z.get(k,0)+b*d
 return {k:n for k,n in z.items() if n}
one={(0,0,0):1};three={(0,0,0):3};four={(0,0,0):4};q={(1,0,0):1};X={(0,1,0):1};ss={(0,0,1):1}
Y=mul(mul(mul(q,q),q),ss);H=add(three,mul(four,mul(Y,add(X,one))))
assert add(mul(H,X),mul(three,X),-1)==mul(q,mul(mul(mul(mul(four,mul(q,q)),ss),add(X,one)),X))
assert (3*8)%3==0 and 8%3!=0
res=subprocess.run([sys.executable,'-I','-S','-B',str(files[2])],check=True,stdout=subprocess.PIPE);assert res.stdout==files[3].read_bytes()
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in files},'actual_extra_carrier_rows_checked':True,'three_X_projection_factor_exact':True,'no_q_divides_X_assumption_in_index_cut':True,'specific_mersenne_source_hypotheses_pinned':True,'nonmersenne_control_is_graph_zero':False,'author_receipt_reproduced':True,'lean_executed':False,'scope':'Conditional source review; graph cuts, provider checks, parent bridge and endpoint remain open.'},sort_keys=True,indent=2))
