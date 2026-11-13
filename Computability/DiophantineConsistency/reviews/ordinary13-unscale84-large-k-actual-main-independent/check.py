from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path;p=P('research/ordinary13-unscale84-large-k-model-draft')
files=[p/'Unscale84LargeK.lean.src',p/'README.md',p/'check.py',p/'pins.json',p/'receipt.json',P('research/ordinary13-qcube-unscale84/candidate.json'),P('research/ordinary13-unscale84-reverse-graph-model-draft/Unscale84ReverseGraph.lean.src'),P('research/ordinary13-positive87-first-norm-binding-draft/Positive87FirstNormBinding.lean.src'),P('research/ordinary14-aux-ring-norm-extraction-draft/RingNormExtraction.lean'),P('research/ordinary14-first-main-large-k-draft/FirstMainLargeK.lean'),P('research/ordinary13-positive84-to87-unscale-model-draft/PositiveUnscale84To87.lean.src'),P('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean'),P('research/ordinary13-residue90-norm-model-draft/Residue90CompactPortBounds.lean.src')]
s=[f.read_text() for f in files];g=json.loads(s[5]);assert len(g['source'])==84 and g['witnesses'][7]=='s'
rows={r[0]:r for r in g['source']}
for row in [['q','+',1,'qm'],['q2','*','q','q'],['q3','*','q','q2'],['Y','*','q3','s'],['U','*','Y','q2'],['E','*','X','Y'],['g15','*',4,'a'],['H','+',3,'g15'],['Delta','+','H','g17'],['b0','+','X','g19'],['g44','*','qF','qm'],['G','+','alpha','g44'],['g47','*','G','g46'],['g50','*','J','g49'],['R','+','g47','g50'],['g52','-','k','R'],['r0','-','g52',1],['g54','*','U','gamma'],['g55','*','E','q'],['g56','+','g54','g55'],['shift','-','g56','r0'],['g58','*','U','b0'],['g59','*','H','shift'],['Dstar','+','g58','g59'],['g61','*','Dstar','Dstar'],['g62','*','U','U'],['g63','*','Delta','c2'],['g64','+',1,'g63'],['g65','*','g62','g64'],['A1','-','g61','g65']]:assert rows[row[0]]==row
for n in ['def rank (p : Fin 4 → ℕ)','def mainRoot (p : Fin 4 → ℕ)',
 'ι (u p v)*ι (v 12)+ι (X v)*ι (Y p v)*ι (q p v)-',
 'theorem main_form','theorem norm_roots','root_of_scaled_ring_square (b p v)',
 'root_of_scaled_ring_square (u p v)','theorem large_k','first_main_large_k',
 'theorem compact_reverse_inputs','theorem compact_positive_zero_iff',
 'Positive87FirstNormBindingDraft.forward_graph_cut','reverse_cut _ (compact_reverse_inputs K)']:
 assert n in s[0],n
for n in ['def ReverseInputs','0<(p 0:V) ∧ 8*X v*Y p v*Y p v+4≤k v','theorem source_first']:assert n in s[6],n
assert 'theorem forward_graph_cut (p : Fin 4 → ℕ) : ForwardGraphCut (intPorts p)' in s[7]
assert 'def intPorts (p : Fin 4 → ℕ) : Fin 4 → ℤ := fun i => (p i : ℤ)' in s[7]
assert 'def portsInt (p : Fin 4 → ℕ) : Fin 4 → ℤ := fun j => (p j : ℤ)' in s[6]
assert 'theorem root_of_scaled_ring_square' in s[8] and 'theorem first_main_large_k' in s[9]
# Exact free-ring check that the literal main shift has +E*q and +R+1.
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
one={(0,)*10:1};U={(1,0,0,0,0,0,0,0,0,0):1};X={(0,1,0,0,0,0,0,0,0,0):1};a={(0,0,1,0,0,0,0,0,0,0):1};c={(0,0,0,1,0,0,0,0,0,0):1};H={(0,0,0,0,1,0,0,0,0,0):1};gamma={(0,0,0,0,0,1,0,0,0,0):1};E={(0,0,0,0,0,0,1,0,0,0):1};q={(0,0,0,0,0,0,0,1,0,0):1};k={(0,0,0,0,0,0,0,0,1,0):1};R={(0,0,0,0,0,0,0,0,0,1):1}
graph_shift=add(add(mul(U,gamma),mul(E,q)),add(add(k,R,-1),one,-1),-1)
claimed_shift=add(add(add(add(mul(U,gamma),mul(E,q)),k,-1),R),one)
assert graph_shift==claimed_shift
root=add(mul(U,add(X,mul(a,c))),mul(H,graph_shift))
wrong=add(mul(U,add(X,mul(a,c))),mul(H,add(add(add(mul(U,gamma),k,-1),R),one)))
assert add(root,wrong,-1)==mul(H,mul(E,q))
# The omitted-extra-term difference is a formal nonzero polynomial,
# not an example of a graph zero.
assert add(root,wrong,-1)
two={(0,)*10:2};three={(0,)*10:3};four={(0,)*10:4}
delta=add(add(three,mul(four,a)),mul(a,a));assert mul(add(a,two),add(a,two))==add(delta,one)
res=subprocess.run([sys.executable,'-I','-S','-B',str(files[2])],check=True,stdout=subprocess.PIPE);assert res.stdout==files[4].read_bytes()
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in files},'actual_84_main_rows_and_extra_Eq_checked':True,'signed_main_carrier_identity_exact':True,'wrong_no_Eq_root_detected':True,'discriminant_identity_exact':True,'same_model_first_main_norms_and_tuple_interfaces_checked':True,'author_receipt_reproduced':True,'lean_executed':False,'scope':'Unelaborated source review; exact graph proofs, helpers, providers, parent bridge and endpoint remain open.'},sort_keys=True,indent=2))
