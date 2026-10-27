from pathlib import Path
p=Path('/home/codex/.codex/worktrees/46be/Proofs/Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorSeedGuardedComprehension222.lean')
s=p.read_text()
def rep(a,b):
 global s
 if a not in s:raise RuntimeError(a[:120])
 s=s.replace(a,b,1)
rep('  exact full_member_closure K a c y','  unfold pairAt pairMatrix closureTerm\n  exact full_member_closure K a c y')
rep('  change Source V ⊢! ∀⁰ (memTerm (Bootstrapping.Semiterm.bvar 0)\n    (Bootstrapping.Semiterm.bvar 0) 🡒 ⊥) at h','  have h\' : Source V ⊢! ∀⁰ (memTerm (Bootstrapping.Semiterm.bvar 0)\n    (Bootstrapping.Semiterm.bvar 0) 🡒 ⊥) := by\n    simpa [irreflexiveSentence,memTerm,FirstOrder.Semiformula.quote_def,\n      Matrix.vecHead,Matrix.vecTail] using h')
rep('⟨TProof.specialize h t⟩)','⟨TProof.specialize h\' t⟩)')
rep('simpa [memTerm] using TProof.specialize_with_ctx! h z','simpa [emptyAt,memTerm] using TProof.specialize_with_ctx! h z')
rep('    Source V ⊢ rawPairAt x y c 🡒 (memTerm z c 🡘 (eqTerm z x ⋎ eqTerm z y)) := by\n  apply deduct\'!', '    Source V ⊢ rawPairAt x y c 🡒 (memTerm z c 🡘 (eqTerm z x ⋎ eqTerm z y)) := by\n  rcases term_is_fvar x with ⟨x,rfl⟩\n  rcases term_is_fvar y with ⟨y,rfl⟩\n  rcases term_is_fvar c with ⟨c,rfl⟩\n  apply deduct\'!')
# Above normalization leaves x/y/c as labels; rebuild local uses in this theorem only.
a=s.index('private theorem rawPairAt_spec'); b=s.index('attribute [local irreducible] rawPairMatrix',a)
part=s[a:b]
part=part.replace('have h : [rawPairAt x y c] ⊢[Source V] rawPairAt x y c', 'have h : [rawPairAt (Bootstrapping.Semiterm.fvar x) (Bootstrapping.Semiterm.fvar y) (Bootstrapping.Semiterm.fvar c)] ⊢[Source V] rawPairAt (Bootstrapping.Semiterm.fvar x) (Bootstrapping.Semiterm.fvar y) (Bootstrapping.Semiterm.fvar c)')
part=part.replace('simpa [rawPairBody,eqTerm','simpa [rawPairAt,rawPairBody,eqTerm')
s=s[:a]+part+s[b:]
rep('∃⁰ hitBody (rawPairMatrix t r x y) r c := hr','∃⁰ hitBody (rawPairMatrix t r x y) r c := by simpa only [hitBody] using hr')
rep('cl_prover [hcl,he,hstep,hk]','cl_prover 80 [hcl,he,hstep,hk]')
rep('∃⁰ supportCore (rawPairMatrix t r x y) z := pair_support _ _ _ _','∃⁰ supportCore (rawPairMatrix t r x y) z := by\n    simpa only [supportCore] using pair_support (rawPairMatrix t r x y) r c z')
rep('simp [rawPairAt,rawPairBody,eqTerm,memTerm,SemitermVec.q,\n    Bootstrapping.Semiformula.substs_substs,Matrix.vecHead,Matrix.vecTail]', 'simp [rawPairAt,rawPairBody,eqTerm,memTerm,SemitermVec.q,Matrix.vecHead,Matrix.vecTail]')
rep('cl_prover [hn,hs,hr]','cl_prover 80 [hn,hs,hr]')
rep('    pair_request _ _ _ _','    by simpa only [hitBody] using pair_request (twoRootMatrix θ B t r) r c B')
rep('cl_prover [hcl,he,hstep,hk]','cl_prover 80 [hcl,he,hstep,hk]')
rep('∃⁰ supportCore (twoRootMatrix θ B t r) z := pair_support _ _ _ _','∃⁰ supportCore (twoRootMatrix θ B t r) z := by\n    simpa only [supportCore] using pair_support (twoRootMatrix θ B t r) r c z')
rep('simpa [twoProperty,memTerm,eqTerm,Bootstrapping.Semiformula.substs_substs,','simpa only [twoRootAt_eq_all,twoProperty,memTerm,eqTerm,\n    Bootstrapping.Semiformula.substs_substs,Bootstrapping.Semiformula.substs_iff,\n    Bootstrapping.Semiformula.substs_or,Bootstrapping.Semiformula.substs_and,\n    Bootstrapping.Semiformula.substs_rel,Bootstrapping.Semiterm.subst_bvar_zero,')
# Use existing simplifier globally for this context conversion, without guessing term lemma names.
s=s.replace('simpa only [twoRootAt_eq_all,twoProperty,memTerm,eqTerm,\n    Bootstrapping.Semiformula.substs_substs,Bootstrapping.Semiformula.substs_iff,\n    Bootstrapping.Semiformula.substs_or,Bootstrapping.Semiformula.substs_and,\n    Bootstrapping.Semiformula.substs_rel,Bootstrapping.Semiterm.subst_bvar_zero,','simpa [twoRootAt_eq_all,twoProperty,memTerm,eqTerm,Bootstrapping.Semiformula.substs_substs,')
rep('  memTerm t.bShift (Bootstrapping.Semiterm.bvar 0) ⋏\n    ∀⁰ (memTerm t.bShift.bShift','  memTerm t.bShift (Bootstrapping.Semiterm.bvar 0) ⋏\n    (∀⁰ (memTerm t.bShift.bShift')
rep('θ.subst ![Bootstrapping.Semiterm.bvar 0])))\ndef guardedAt','θ.subst ![Bootstrapping.Semiterm.bvar 0]))))\ndef guardedAt')
rep('simp [guardedBody,eqTerm,memTerm,','simp [guardedBody,memTerm,')
# aug_spec: expose only the exact context alongside all substitution reductions, using term classification.
a=s.index('private theorem aug_spec');b=s.index('private theorem envelope_ne',a)
part=s[a:b].replace("  apply deduct'!","  rcases term_is_fvar U with ⟨U,rfl⟩\n  rcases term_is_fvar E with ⟨E,rfl⟩\n  apply deduct'!",1)
part=part.replace('have h : [rawAugAt θ U E] ⊢[Source V] rawAugAt θ U E','have h : [rawAugAt θ (Bootstrapping.Semiterm.fvar U) (Bootstrapping.Semiterm.fvar E)] ⊢[Source V] rawAugAt θ (Bootstrapping.Semiterm.fvar U) (Bootstrapping.Semiterm.fvar E)')
part=part.replace('simpa [memTerm,eqTerm,','simpa [rawAugAt,rawAugBody,memTerm,eqTerm,')
s=s[:a]+part+s[b:]
rep("cl_prover [hs',he,hi]","cl_prover 80 [hs',he,hi]")
rep('cl_prover [hp,he,hu,hc]','cl_prover 96 [hp,he,hu,hc]')
rep("cl_prover 48 [hnE,hnt,hs']","cl_prover 96 [hnE,hnt,hs']")
rep("cl_prover 48 [hEz,hs']","cl_prover 96 [hEz,hs']")
rep('cl_prover [hf,hb]','cl_prover 80 [hf,hb]')
rep('cl_prover [hp,he,hc]','cl_prover 80 [hp,he,hc]')
p.write_text(s)
