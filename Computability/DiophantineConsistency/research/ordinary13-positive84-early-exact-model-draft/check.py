from pathlib import Path
from hashlib import sha256
import json,sys,re
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
PINS={'research/ordinary13-qcube-unscale84/candidate.json': '2293d98affce104dc1522ddd69a0cf904ee752034dbd8959f4d3f41a3c604a77', 'research/ordinary13-positive83-to84-model-draft/PositiveUnscaled84Graph.lean.src': 'd2eb1fc077aac66c67a4c75f6b6a70792b6f0c7923f3ec952ea64d3ad7cf8740', 'research/ordinary13-positive84-to87-unscale-model-draft/PositiveUnscale84Graph.lean.src': 'fbf2499bdbc587072665852fdec5833b96aeae965b983066d4a8fa7eb782cadf', 'research/ordinary13-unscale84-large-k-model-draft/Unscale84LargeK.lean.src': '8002fb8d0000a0f2f49b7f6e65826ce543deec738f5bf6b15e6c3f20ad841251', 'research/ordinary13-residue-first-index-model-draft/ResidueFirstIndexModel.lean.src': '0b69fb042a913232ef9f4a92757107f60d8a590f855176134587939012b1b93b', 'research/ordinary13-positive81-calibration-model-draft/Positive81ExactIndexCut.lean.src': 'f166f5e320594b8179ef452044029a2a3ff96cdad6d650e17e3b991012fcab24', 'research/ordinary13-positive84-power-model-draft/Positive84Power.lean.src': '565b28f2fcecbbc0b0f53d827a3dffc7fe8cd1f5090a8a80375e03242cf60a23', 'Lean/DiophantineConsistency/Compact44/P72Exact.lean': 'a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3', 'Lean/DiophantineConsistency/Compact44/FreeJMainOrientation.lean': 'd02beb02122e682deef3e89c3dcb8e3e6aea31ddfbc4f320fe6af9a3df7f9a6b', 'research/ordinary13-positive84-early-exact-model-draft/Positive84EarlyExact.lean.src': '2735739f3320c6d8794deba53e73bfc054bfeef0ff1b57ed4deefae5623d8d19'}
for p,h in PINS.items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
f=list(PINS);g=json.loads(Path(f[0]).read_text());s=[Path(x).read_text() for x in f[1:]]
assert len(g['source'])==84
for text in s[:2]:
 for i,n in enumerate(g['witnesses']):assert f'  let {n} : Expr (Fin 13) := .var {i}\n' in text
 for i,n in enumerate(g['fixed_numerals']):assert f'  let {n} : Expr (Fin 13) := .constant (p {i})\n' in text
 for n,op,x,y in g['source']:assert f'  let {n} := {x} {op} {y}\n' in text
assert '⟨A0,A1,Fa,g72,out⟩' in s[0] and '⟨A0,A1,Fa,g72,Z,Bt,ell,k,out⟩' in s[1]
for text in ['theorem norm_roots','mainRoot p v','tau*tau=1+']:assert text in s[2]
for text in ['theorem early_index_of_natural_norm','(hcong : q^4 ∣ magnitude (R+1,k))','xcoord n B=tau','2*ycoord n B=k']:assert text in s[3]
for text in ['theorem exact_pair','(hmy : ycoord m a=c)','(hstrong :','(haux :','m=R ∧ 2*n=R+1']:assert text in s[4]
for text in ['theorem rank_congruence_from_main','FreeJMainCongruence','FreeJRankCongruence']:assert text in s[7]
for text in ['def RankFacts','def Early','theorem early_of_rank_facts','def MainStrongAux','theorem exact_of_facts','theorem rank_congruence_of_main','def RankWindowGraphCut','def MainStrongAuxGraphCut','exactPowerGraphCut_of_window_and_main']:assert text in s[8]
# Synthetic same-main balance controls; no assertion these are graph zeros.
count=0
for q in range(1,6):
 for ss in range(1,3):
  Y=q**3*ss;U=Y*q*q
  for X in range(1,9):
   a=X*Y+Y;H=3+4*a
   for R in range(7):
    for k in range(1,12):
     for c in range(2):
      for gamma in range(2):
       num=U*(X+a*c)+H*(U*gamma+X*Y*q+R+1)-H*k
       if num>0 and num%U==0:
        main=num//U
        assert U*main+H*k==U*(X+a*c)+H*(U*gamma+X*Y*q+R+1)
        assert abs(R+1-k)%(q**4)==0
        assert H*(X*Y*q+R+1)+(q**5)*(ss*(X+a*c+H*gamma))==H*k+(q**5)*(ss*main)
        count+=1
assert count>0
print(json.dumps({'sha256':PINS,'literal_row_bindings_checked':True,'same_index_interfaces_checked':True,'extra_term_rank_congruence_controls':count,'lean_executed':False,'status':'Unelaborated conditional source composition; rank-window and same-root graph witness cuts remain open.'},sort_keys=True,indent=2))
