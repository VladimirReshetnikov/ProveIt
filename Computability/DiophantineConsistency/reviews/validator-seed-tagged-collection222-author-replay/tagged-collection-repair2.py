from pathlib import Path
p=Path('/home/codex/.codex/worktrees/46be/Proofs/Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorSeedTaggedCollection222.lean')
s=p.read_text().replace(': ℒₛₑₜ.Rel 2',': (ℒₛₑₜ).Rel 2')
s=s.replace('cl_prover [root_not_singleton E t r p x,he\',image_core_singleton θ t p y x]','cl_prover 96 [root_not_singleton E t r p x,he\',image_core_singleton θ t p y x]')
s=s.replace('''      simpa using (by_axm₀! (𝓢 := Source V) (Γ := []) (φ := ∼(∃⁰ p)))''','''      simp only [Bootstrapping.Semiformula.neg_exs]
      exact by_axm₀!''')
a=s.index('private theorem image_projection');b=s.index('private def outputProperty',a)
s=s[:a]+'''private theorem image_projection (θ : Semiformula V ℒₛₑₜ 2) (t p y : Term V ℒₛₑₜ) :
    Source V ⊢ (∃⁰ imageCore θ t p y) 🡒 ∃⁰ supportImage θ t y := by
  apply FiniteContext.provable_iff_provable.mpr
  apply TProof.exs_imp_exs!
  rw [imageCore_free,supportImage_free]
  cl_prover

@[simp] private theorem selectedImage_free (θ : Semiformula V ℒₛₑₜ 2) (t c x : Term V ℒₛₑₜ) :
    (selectedImage θ t c x).free=
      (memTerm t.shift (Bootstrapping.Semiterm.fvar 0) ⋏
        (memTerm (Bootstrapping.Semiterm.fvar 0) c.shift ⋏
          θ.shift.subst ![Bootstrapping.Semiterm.fvar 0,x.shift])) := by
  rcases term_is_fvar t with ⟨t,rfl⟩
  rcases term_is_fvar c with ⟨c,rfl⟩
  rcases term_is_fvar x with ⟨x,rfl⟩
  simp [selectedImage,memTerm,Bootstrapping.Semiformula.free,
    Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs,
    Matrix.vecHead,Matrix.vecTail]

'''+s[b:]
s=s.replace('  rw [hitBody_free,collectionMatrix_shift]\n','  rw [hitBody_free,collectionMatrix_shift,selectedImage_free]\n')
s=s.replace(':= by cl_prover [hv,hH]',':= by cl_prover 96 [hv,hH]')
s=s.replace('''  simpa [Γ,selectedImage,memTerm,Bootstrapping.Semiformula.free,
    Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs,
    Matrix.vecHead,Matrix.vecTail] using h''','''  exact h''')
s=s.replace('cl_prover [hs,hu]','cl_prover 96 [hs,hu]').replace('cl_prover 80 [hs,hm]','cl_prover 128 [hs,hm]')
s=s.replace('∃⁰ selectedImage θ.shift t.shift c.shift x.shift from by cl_prover [hp])','∃⁰ selectedImage θ.shift t.shift c.shift x.shift from by cl_prover 96 [hp])')
s=s.replace('∃ mt emptyBody empty tag body exbody consequent,','∃ mt bot emptyBody empty tag body exbody consequent,')
s=s.replace('''!at2Graph mt ↑b0Code t ↑memCode ∧
    !(Bootstrapping.impGraph ℒₛₑₜ) emptyBody mt ↑(Bootstrapping.qqFalsum : ℕ) ∧''','''!at2Graph mt ↑b0Code t ↑memCode ∧ !qqFalsumDef bot ∧
    !(Bootstrapping.impGraph ℒₛₑₜ) emptyBody mt bot ∧''')
s=s.replace('numeral_eq_natCast,Bootstrapping.qqFalsum,pair]','numeral_eq_natCast]')
s=s.replace('have hsing := at2_sing (Bootstrapping','have hsing := at2_sing (V := V) (Bootstrapping')
p.write_text(s)
