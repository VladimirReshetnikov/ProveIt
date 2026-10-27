from pathlib import Path
p=Path('/home/codex/.codex/worktrees/46be/Proofs/Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorSeedTaggedCollection222.lean')
s=p.read_text()
s=s.replace('  simpa [eqTerm,SetCongruence.eqAtom,Bootstrapping.Semiformula.substs_substs,','  have heq : (Language.Eq.eq : ℒₛₑₜ.Rel 2)=Language.Set.Rel.eq := rfl\n  simpa [eqTerm,SetCongruence.eqAtom,heq,Bootstrapping.Semiformula.substs_substs,')
s=s.replace('    ∃⁰ (memTerm t.bShift.bShift.bShift (Bootstrapping.Semiterm.bvar 0) ⋏\n      (singTerm','    (∃⁰ (memTerm t.bShift.bShift.bShift (Bootstrapping.Semiterm.bvar 0) ⋏\n      (singTerm',1)
s=s.replace('θ.subst ![Bootstrapping.Semiterm.bvar 1,Bootstrapping.Semiterm.bvar 0]))))\n\n@[simp] theorem collectionMatrix_shift','θ.subst ![Bootstrapping.Semiterm.bvar 1,Bootstrapping.Semiterm.bvar 0])))))\n\n@[simp] theorem collectionMatrix_shift',1)
s=s.replace('((eqTerm p t ⋏ eqTerm y t) ⋎ ∃⁰ imageCore θ t p y))','((eqTerm p t ⋏ eqTerm y t) ⋎ (∃⁰ imageCore θ t p y)))')
s=s.replace('eqTerm y E ⋎ (eqTerm y t ⋎ ∃⁰ supportImage θ t y)','eqTerm y E ⋎ (eqTerm y t ⋎ (∃⁰ supportImage θ t y))')
# Opaque body opening prevents proof search from expanding arbitrary theta and terms.
a=s.index('private theorem image_projection');b=s.index('private def outputProperty',a)
s=s[:a]+'''@[simp] private theorem supportImage_free (θ : Semiformula V ℒₛₑₜ 2) (t y : Term V ℒₛₑₜ) :
    (supportImage θ t y).free=
      (memTerm t.shift (Bootstrapping.Semiterm.fvar 0) ⋏
        θ.shift.subst ![y.shift,Bootstrapping.Semiterm.fvar 0]) := by
  rcases term_is_fvar t with ⟨t,rfl⟩
  rcases term_is_fvar y with ⟨y,rfl⟩
  simp [supportImage,memTerm,Bootstrapping.Semiformula.free,
    Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs,
    Matrix.vecHead,Matrix.vecTail]

private theorem image_projection (θ : Semiformula V ℒₛₑₜ 2) (t p y : Term V ℒₛₑₜ) :
    Source V ⊢ (∃⁰ imageCore θ t p y) 🡒 ∃⁰ supportImage θ t y := by
  apply TProof.exs_imp_exs!
  rw [imageCore_free,supportImage_free]
  cl_prover

'''+s[b:]
# Normalize ambient terms before nested binder substitutions.
for name in ['collection_support_all','collection_coverage_all']:
 a=s.index('private theorem '+name);b=s.index('  unfold ',a)
 s=s[:b]+'''  rcases term_is_fvar a with ⟨a,rfl⟩
  rcases term_is_fvar t with ⟨t,rfl⟩
  rcases term_is_fvar c with ⟨c,rfl⟩
'''+s[b:]
 # names a/t/c are now raw values, so reconstruct typed terms in the local h call only
 b=s.index('  have h :=',b);e=s.index('\n',b)
 line=s[b:e].replace('a.shift','(Bootstrapping.Semiterm.fvar a).shift').replace('t.shift','(Bootstrapping.Semiterm.fvar t).shift').replace('c.shift','(Bootstrapping.Semiterm.fvar c).shift')
 s=s[:b]+line+s[e:]
# Explicit arithmetic code cast for falsum.
s=s.replace('collectionConclusionGraph,collectionConclusionCode,numeral_eq_natCast]','collectionConclusionGraph,collectionConclusionCode,numeral_eq_natCast,Bootstrapping.qqFalsum,pair]')
# Apply the body binding before exposing its term-value implementation.
s=s.replace('  simp only [collectionConclusionCode,b0_cast,Bootstrapping.Semiterm.fvar,hmt,hta,hb]','  rw [collectionConclusionCode,hb]\n  simp only [b0_cast,Bootstrapping.Semiterm.fvar,hmt,hta]')
p.write_text(s)
