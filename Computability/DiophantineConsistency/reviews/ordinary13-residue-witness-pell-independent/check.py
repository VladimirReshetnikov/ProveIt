#!/usr/bin/env python3
"""Independent source witness/identity review, no Lean or builds."""
from pathlib import Path
import hashlib,json,random,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent;root=here.parents[1]
pins={
'research/ordinary13-residue-witness-pell-model-draft/ResidueExactIndexWitness.lean.src':'6dc344285cb14e51c2afce9dedca2d8739e826337c43c16b77f3c7e6ba99a9e1',
'research/ordinary13-residue-witness-pell-model-draft/ResidueExactIndexGraphWitness.lean.src':'7e83748e9dea640b70f4b8ec53f350590614e14ada1549588a5b389775b6e14f',
'research/ordinary13-residue-witness-pell-model-draft/ResiduePellCoordinates.lean.src':'7e4640421d8585db33e08c0b3ed389f6af9017f3e03416b6197bfcbc9f8f96b3',
'research/ordinary13-residue-exact-index-model-draft/ResidueExactIndexModel.lean.src':'dc941fd8914795ac46f513f45979ef7c69c22a6d1be4dc332605f1ddb7a3a79a',
'research/ordinary13-residue-aux-bounds-adapter-draft/ResidueExactIndexFromGraph.lean.src':'169c4e604a573fa1da69ca5d642d9d9de4b125515badb88f67b17f78b24601f1',
'research/ordinary13-residue-main-congruence-model-draft/ResidueMainCongruence.lean.src':'c92cbbca34371870b01f03042de0a4a024bd56a6175d909c43b6887736700ce8',
'research/ordinary13-residue-qbalance-graph-draft/ResidueQBalance.lean.src':'a1369553c520dc5db2839f36fb9181f5434bad0f196bbb04399ef4c3b2f7e344',
'research/ordinary13-residue-qbalance-graph-draft/ResidueQBalanceGraph.lean.src':'d4c6ff3e85231b841395b81dca8d940c14ae588d7b06fa2fe1ed1a4bbe381617',
'research/ordinary13-residue-three-projection-graph-draft/ResidueThreeProjectionGraph.lean.src':'589fb5cd96875a7ee9728035c8ca49bf3406336c8c9362eebd112d2d6e3e3f7b',
'Lean/DiophantineConsistency/ArithmeticPellClassification.lean':'77dc61a25a075c237ea36cc14a3e46c9832a1de827b84427679e268111a4cf78',
'Lean/DiophantineConsistency/ArithmeticPellCongruences.lean':'75e5e2c18b70a6cf9b4cdd0d1f8fe52bc3104c2ae34de5ff4169f5786885c6b1',
'Lean/DiophantineConsistency/Compact44/DirectMainNorm.lean':'29c748582368b4ab2bcdb4b4cdd4f7890dda32f77718e33355b590b8f07b7fbd'}
s={}
for p,h in pins.items():
 b=(root/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[p]=b.decode()
w=s['research/ordinary13-residue-witness-pell-model-draft/ResidueExactIndexWitness.lean.src']
x=s['research/ordinary13-residue-exact-index-model-draft/ResidueExactIndexModel.lean.src']
def one(t,a,b):assert t.count(a)==1,(a,t.count(a));return t.replace(a,b)
w=one(w,'      n≤k v ∧ k v=2*n+4*(m p v)*s ∧\n      2*ycoord n (2*(m p v-1)+1)=k v := by','      n≤k v ∧ k v=2*n+4*(m p v)*s := by')
w=one(w,'  exact ⟨tau,n,s,htau,hn13,hnlt,hindex,heq,hnk,hks,hny⟩','  exact ⟨tau,n,s,htau,hn13,hnlt,hindex,heq,hnk,hks⟩')
w=w.replace('ResidueExactIndexWitnessDraft','ResidueExactIndexModelDraft')
assert w==x
w=s['research/ordinary13-residue-witness-pell-model-draft/ResidueExactIndexGraphWitness.lean.src']
x=s['research/ordinary13-residue-aux-bounds-adapter-draft/ResidueExactIndexFromGraph.lean.src']
w=one(w,'      n≤k v ∧ k v=2*n+4*(m p v)*s ∧\n      2*ArithmeticPellRecurrence.ycoord n (2*(m p v-1)+1)=k v ∧\n      ArithmeticPellRecurrence.ycoord (rank p v) (a p v)=c p v := by','      n≤k v ∧ k v=2*n+4*(m p v)*s := by')
w=one(w,'  obtain ⟨tau,n,s,htau,hn13,hnlt,hindex,heq,hnk,hks,hfirst⟩ :=','  obtain ⟨tau,n,s,htau,hn13,hnlt,hindex,heq,hnk,hks⟩ :=')
w=one(w,'  have hmainy : ArithmeticPellRecurrence.ycoord (rank p v) (a p v)=c p v := by\n    rw [←hindex]\n    exact hmy\n  exact ⟨tau,n,s,mainIndex,u,hu,htau,hn13,hnlt,hindex,heq,hnk,hks,hfirst,hmainy⟩','  exact ⟨tau,n,s,mainIndex,u,hu,htau,hn13,hnlt,hindex,heq,hnk,hks⟩')
w=w.replace('ResidueExactIndexGraphWitnessDraft','ResidueExactIndexFromGraphDraft').replace('ResidueExactIndexWitnessDraft','ResidueExactIndexModelDraft').replace('import ResidueExactIndexWitness','import ResidueExactIndexModel')
assert w==x
c=s['research/ordinary13-residue-witness-pell-model-draft/ResiduePellCoordinates.lean.src']
for term in ['(hty.trans hy.symm)','⟨main,hmain,hbalance,hnorm⟩','⟨_,n,w,_,_,_,_,hn,_,_,heq,_,hks,hfirst,hmainy⟩','(rank p v+v 6*Y p v*q p v)','main_coordinate_of_norm (a p v) (c p v) main (rank p v) hnorm\' hmainy','ResidueThreeProjectionGraphDraft.q_dvd_threeX_of_graph','(hq46 : 46≤q p v)']:assert term in c,term
assert 'time≤y ∧ xcoord time b=x ∧ ycoord time b=y' in s['Lean/DiophantineConsistency/ArithmeticPellClassification.lean']
assert 'theorem y_strictMono (b : V)' in s['Lean/DiophantineConsistency/ArithmeticPellCongruences.lean']
assert '∃ m : V, 0<m ∧ P=N+U*m ∧ m*m=1+(H+a*a)*(c*c)' in s['Lean/DiophantineConsistency/Compact44/DirectMainNorm.lean']
# Numerically check the exact natural-balance rearrangement, not graph zeros.
r=random.Random(130945);cases=0
for _ in range(300):
 q=r.randrange(1,9);X=r.randrange(0,10);s0=r.randrange(1,6);Y=q**3*s0
 c,R,gamma,main,w=[r.randrange(0,12) for j in range(5)]
 a=X*Y+Y;H=3+4*a;U=Y*q*q;k=R+1+4*X*Y*Y*w;W=4*X*q*s0*w
 root=U*main+H*k-(U*(X+a*c)+H*(U*gamma+X*Y*q+R+1))
 bal=q*(main+H*W)-(q*(X+a*c+H*gamma)+H*X)
 assert root==q*Y*bal
 cases+=1
# Distinct Pell times produce distinct y, so x is fixed when the same y matches.
pell=0
for a in range(8):
 X,Y=1,0;seen={}
 for n in range(20):
  assert X*X==1+(a+1)*(a+3)*Y*Y
  assert Y not in seen
  seen[Y]=(n,X);X,Y=(a+2)*X+(a+1)*(a+3)*Y,X+(a+2)*Y
  pell+=1
print(json.dumps({'source_sha256':pins,'reverse_diff_both_predecessors_exact':True,'balance_identity_controls':cases,'distinct_ordinate_controls':pell,'lean_executed':False,'scope':'source witness alignment plus finite integer controls only; no theorem elaboration, graph correctness, provider build or iPRA endpoint'},sort_keys=True,indent=2))
