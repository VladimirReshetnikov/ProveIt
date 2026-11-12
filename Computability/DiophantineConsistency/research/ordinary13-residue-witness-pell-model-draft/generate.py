from pathlib import Path
p=Path('research/ordinary13-residue-witness-pell-model-draft')
f=Path('research/ordinary13-residue-exact-index-model-draft/ResidueExactIndexModel.lean.src')
s=f.read_text().replace('namespace DiophantineConsistency.ResidueExactIndexModelDraft','namespace DiophantineConsistency.ResidueExactIndexWitnessDraft').replace('end DiophantineConsistency.ResidueExactIndexModelDraft','end DiophantineConsistency.ResidueExactIndexWitnessDraft').replace('#print axioms DiophantineConsistency.ResidueExactIndexModelDraft.','#print axioms DiophantineConsistency.ResidueExactIndexWitnessDraft.')
a='      n≤k v ∧ k v=2*n+4*(m p v)*s := by'
b='      n≤k v ∧ k v=2*n+4*(m p v)*s ∧\n      2*ycoord n (2*(m p v-1)+1)=k v := by'
assert s.count(a)==1;s=s.replace(a,b)
a='  exact ⟨tau,n,s,htau,hn13,hnlt,hindex,heq,hnk,hks⟩'
b='  exact ⟨tau,n,s,htau,hn13,hnlt,hindex,heq,hnk,hks,hny⟩'
assert s.count(a)==1;s=s.replace(a,b)
(p/'ResidueExactIndexWitness.lean.src').write_text(s)
f=Path('research/ordinary13-residue-aux-bounds-adapter-draft/ResidueExactIndexFromGraph.lean.src')
s=f.read_text().replace('import ResidueExactIndexModel','import ResidueExactIndexWitness').replace('namespace DiophantineConsistency.ResidueExactIndexFromGraphDraft','namespace DiophantineConsistency.ResidueExactIndexGraphWitnessDraft').replace('end DiophantineConsistency.ResidueExactIndexFromGraphDraft','end DiophantineConsistency.ResidueExactIndexGraphWitnessDraft').replace('#print axioms DiophantineConsistency.ResidueExactIndexFromGraphDraft.','#print axioms DiophantineConsistency.ResidueExactIndexGraphWitnessDraft.').replace('ResidueExactIndexModelDraft.','ResidueExactIndexWitnessDraft.')
a='      n≤k v ∧ k v=2*n+4*(m p v)*s := by'
b='      n≤k v ∧ k v=2*n+4*(m p v)*s ∧\n      2*ArithmeticPellRecurrence.ycoord n (2*(m p v-1)+1)=k v ∧\n      ArithmeticPellRecurrence.ycoord (rank p v) (a p v)=c p v := by'
assert s.count(a)==1;s=s.replace(a,b)
a='  obtain ⟨tau,n,s,htau,hn13,hnlt,hindex,heq,hnk,hks⟩ :='
b='  obtain ⟨tau,n,s,htau,hn13,hnlt,hindex,heq,hnk,hks,hfirst⟩ :='
assert s.count(a)==1;s=s.replace(a,b)
a='  exact ⟨tau,n,s,mainIndex,u,hu,htau,hn13,hnlt,hindex,heq,hnk,hks⟩'
b='  have hmainy : ArithmeticPellRecurrence.ycoord (rank p v) (a p v)=c p v := by\n    rw [←hindex]\n    exact hmy\n  exact ⟨tau,n,s,mainIndex,u,hu,htau,hn13,hnlt,hindex,heq,hnk,hks,hfirst,hmainy⟩'
assert s.count(a)==1;s=s.replace(a,b)
(p/'ResidueExactIndexGraphWitness.lean.src').write_text(s)
