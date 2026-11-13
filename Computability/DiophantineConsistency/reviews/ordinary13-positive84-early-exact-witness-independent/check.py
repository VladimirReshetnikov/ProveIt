from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path;p=P('research/ordinary13-positive84-early-exact-model-draft')
files=[p/'Positive84EarlyExact.lean.src',p/'README.md',p/'check.py',p/'receipt.json',P('research/ordinary13-positive84-power-model-draft/Positive84Power.lean.src'),P('research/ordinary13-residue-first-index-model-draft/ResidueFirstIndexModel.lean.src'),P('research/ordinary13-positive81-calibration-model-draft/Positive81ExactIndexCut.lean.src'),P('Lean/DiophantineConsistency/Compact44/FreeJMainOrientation.lean'),P('research/ordinary13-unscale84-large-k-model-draft/Unscale84LargeK.lean.src'),P('research/ordinary13-qcube-unscale84/candidate.json'),P('research/ordinary13-positive83-to84-model-draft/PositiveUnscaled84Graph.lean.src'),P('research/ordinary13-positive84-to87-unscale-model-draft/PositiveUnscale84Graph.lean.src'),P('Lean/DiophantineConsistency/Compact44/P72Exact.lean')]
s=[f.read_text() for f in files];g=json.loads(s[9]);assert len(g['source'])==84 and g['witnesses'][6:8]==['X','s']
for src in (s[10],s[11]):
 for i,n in enumerate(g['witnesses']):assert f'  let {n} : Expr (Fin 13) := .var {i}\n' in src
 for i,n in enumerate(g['fixed_numerals']):assert f'  let {n} : Expr (Fin 13) := .constant (p {i})\n' in src
 for n,op,l,r in g['source']:assert f'  let {n} := {l} {op} {r}\n' in src,n
rows={r[0]:r for r in g['source']}
for row in [['Y','*','q3','s'],['U','*','Y','q2'],['E','*','X','Y'],['g55','*','E','q'],['g56','+','g54','g55'],['shift','-','g56','r0'],['R','+','g47','g50']]:assert rows[row[0]]==row
for n in ['theorem same84','def RankFacts','def Early','theorem early_of_rank_facts','def MainStrongAux','theorem exact_of_facts',
 'let t : Fin 12 → V := ![v 0,v 1,v 2,v 3,v 4,v 6,Y84 p v,v 5,v 9,v 10,v 11,v 12]',
 'theorem rank_congruence_of_main','FreeJMainOrientation.rank_congruence_from_main p t hc',
 'def RankWindowGraphCut','def MainStrongAuxGraphCut','theorem exactPowerGraphCut_of_window_and_main']:
 assert n in s[0],n
for n in ['obtain ⟨n,w,hn,_,_,hny,hnmod,_,_,hks⟩','obtain ⟨main,m,u,hx,hy,hmain,hstrong,haux,hbal⟩',
 '(v 6*Y84 p v+Y84 p v) (v 7) (v 4) (v 3) (v 5) u n w (mu p v) m (v 9)',
 'hR26 hny hks hRmu hnmod hy hmain hstrong haux',
 'refine ⟨rank84 p v,n,main,w,rfl,hn,hnR']:
 assert n in s[0],n
assert 'zero84_to83' not in s[0] and 'q84 p v∣v 6' not in s[0]
for n in ['def FreeJMainCongruence','H*(E*q+R+1)','theorem rank_congruence_from_main (p : Fin 4 → ℕ) (v : Fin 12 → V)',
 '(hmain : FreeJMainCongruence p v)']:assert n in s[7],n
assert '(hcong : q^4 ∣ magnitude (R+1,k))' in s[5] and 'm=R ∧ 2*n=R+1' in s[6]
assert '13 ≤ n ∧ n < m ∧ m = R ∧ 2 * n = R + 1' in s[12]
# Exact E*q=q⁴*X*s given Y=q³*s; valid in any commutative ring.
def mul(a,b):
 c={}
 for x,i in a.items():
  for y,j in b.items():
   z=tuple(i+j for i,j in zip(x,y));c[z]=c.get(z,0)+i*j
 return {k:n for k,n in c.items() if n}
q={(1,0,0):1};X={(0,1,0):1};ss={(0,0,1):1};Y=mul(mul(mul(q,q),q),ss)
assert mul(mul(X,Y),q)==mul(mul(mul(mul(q,q),mul(q,q)),X),ss)
res=subprocess.run([sys.executable,'-I','-S','-B',str(files[2])],check=True,stdout=subprocess.PIPE);assert res.stdout==files[3].read_bytes()
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in files},'both_84_literal_rows_and_extra_main_term_checked':True,'same_n_w_and_main_index_source_flow_checked':True,'freej_12_slot_correspondence_checked':True,'extra_Eq_is_q4_multiple_polynomial_identity':True,'no_q_div_X_or_84_to83_call':True,'author_receipt_reproduced':True,'lean_executed':False,'scope':'Unelaborated source flow; rank-window and main/strong/aux graph cuts, providers and endpoint remain open.'},sort_keys=True,indent=2))
