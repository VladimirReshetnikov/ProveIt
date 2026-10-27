from pathlib import Path
p=Path('Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorSeedTransitive222.lean');s=p.read_text()
s=s.replace('private theorem singleton_hit', 'attribute [local irreducible] transitiveMatrix\n\nprivate theorem singleton_hit',1)
s=s.replace('  have hr := pair_request (transitiveMatrix (V := V)) s c a\n  change Source V ⊢ pairAt transitiveMatrix s c 🡒\n    transitiveMatrix.subst ![a,s] 🡒 ∃⁰ hitBody transitiveMatrix s c at hr', '  have hr : Source V ⊢ pairAt transitiveMatrix s c 🡒\n      transitiveMatrix.subst ![a,s] 🡒 ∃⁰ hitBody transitiveMatrix s c := by\n    simpa only [hitBody] using pair_request (transitiveMatrix (V := V)) s c a')
# Substitution under nested binders is literal on raw free labels.
import re
for name,args in [('pair_transitive',['s','c']),('transitive_spec',['U','y','z']),('cut_transitive',['U','t','c'])]:
 start=s.index('private theorem '+name); at=s.index(' := by\n',start)+len(' := by\n')
 end=s.index('\nprivate theorem',at)
 body=s[at:end]
 for arg in args: body=re.sub(r'\b'+arg+r'\b',f'(Bootstrapping.Semiterm.fvar {arg}Idx)',body)
 prefix=''.join(f'  rcases term_is_fvar {arg} with ⟨{arg}Idx,rfl⟩\n' for arg in args)
 s=s[:at]+prefix+body+s[end:]
s=s.replace('  simp [memTerm]\n  cl_prover\n\nprivate theorem cut_spec','  simp [memTerm]\n\nprivate theorem cut_spec')
# Keep the original context when reducing a recognized formula.
s=s.replace('  simp [memTerm,Bootstrapping.Semiformula.substs_substs,SemitermVec.q,Matrix.vecHead,Matrix.vecTail] at hz\n  cl_prover [hz]', '''  have hz' : [guardedAt (⊤ : Semiformula V ℒₛₑₜ 1)
      (Bootstrapping.Semiterm.fvar U) (Bootstrapping.Semiterm.fvar t) (Bootstrapping.Semiterm.fvar c)] ⊢[Source V]
      memTerm (Bootstrapping.Semiterm.fvar t) z 🡒
      (memTerm z (Bootstrapping.Semiterm.fvar c) 🡘 (memTerm z (Bootstrapping.Semiterm.fvar U) ⋏ ⊤)) := by
    simpa [guardedAt,guardedBody,memTerm,SemitermVec.q,Matrix.vecHead,Matrix.vecTail] using hz
  cl_prover [hz']''')
s=s.replace('  simpa [memTerm,eqTerm,Bootstrapping.Semiformula.substs_substs,SemitermVec.q,\n    Matrix.vecHead,Matrix.vecTail] using TProof.specialize_with_ctx! h z', '  simpa [rawPairAt,rawPairBody,memTerm,eqTerm,SemitermVec.q,\n    Matrix.vecHead,Matrix.vecTail] using TProof.specialize_with_ctx! h z')
s=s.replace('    simpa using\n      (show Γ', '    simpa only [Γ,List.map_cons,List.map_nil,rawTransitiveAt_shift] using\n      (show Γ')
s=s.replace('    simpa using (show Γ', '    simpa only [Γ,List.map_cons,List.map_nil,rawPairAt_shift] using (show Γ')
# Correct notation precedence of binders as conjunction arguments.
s=s.replace('seedMem 2 1 0 ⋏ ∀⁰ (seedMem 3 0 1 🡒 ∀⁰ (seedMem 4 0 1 🡒 seedMem 4 0 2))', 'seedMem 2 1 0 ⋏ (∀⁰ (seedMem 3 0 1 🡒 ∀⁰ (seedMem 4 0 1 🡒 seedMem 4 0 2)))')
s=s.replace('seedMem 3 2 0 ⋏ (seedMem 3 1 0 ⋏ ∀⁰ (seedMem 4 3 0 🡒 seedMem 4 0 1 🡒\n    ∀⁰ (seedMem 5 4 0 🡒 seedMem 5 0 1 🡒 seedMem 5 0 2)))', 'seedMem 3 2 0 ⋏ (seedMem 3 1 0 ⋏ (∀⁰ (seedMem 4 3 0 🡒 seedMem 4 0 1 🡒\n    ∀⁰ (seedMem 5 4 0 🡒 seedMem 5 0 1 🡒 seedMem 5 0 2))))')
s=s.replace('seedMem 4 3 0 ⋏ ∀⁰ (seedMem 5 4 0 🡒 (seedMem 5 0 1 🡘\n    (FirstOrder.Semiformula.rel Language.Eq.eq ![#0,#2] ⋎\n      FirstOrder.Semiformula.rel Language.Eq.eq ![#0,#3])))', 'seedMem 4 3 0 ⋏ (∀⁰ (seedMem 5 4 0 🡒 (seedMem 5 0 1 🡘\n    (FirstOrder.Semiformula.rel Language.Eq.eq ![#0,#2] ⋎\n      FirstOrder.Semiformula.rel Language.Eq.eq ![#0,#3]))))')
s=s.replace('  exact congrArg Subtype.val transitiveMatrix_quote', '  exact congrArg Bootstrapping.Semiformula.val (transitiveMatrix_quote (V := V))')
s=s.replace('simp [rawTransitiveBodyGraph,rawTransitiveBodyCode]', 'simp [rawTransitiveBodyGraph,rawTransitiveBodyCode,numeral_eq_natCast]')
s=s.replace('simp [taggedTransitiveBodyGraph,taggedTransitiveBodyCode]', 'simp [taggedTransitiveBodyGraph,taggedTransitiveBodyCode,numeral_eq_natCast]')
s=s.replace('simp [taggedPairBodyGraph,taggedPairBodyCode]', 'simp [taggedPairBodyGraph,taggedPairBodyCode,numeral_eq_natCast]')
# Exact quote equality at the represented value avoids irrelevant function tails.
a=s.index('theorem transitiveMatrix_quote'); b=s.index('theorem transitiveMatrixCode_eq',a)
s=s[:a]+'''theorem transitiveMatrix_quote : (⌜transitiveMatrixMeta⌝ : Semiformula V ℒₛₑₜ 2)=transitiveMatrix := by
  apply Bootstrapping.Semiformula.ext
  simp [transitiveMatrixMeta,transitiveMatrix,singTerm,seedMem,memTerm,eqTerm,
    FirstOrder.Semiformula.quote_def,Matrix.vecHead,Matrix.vecTail,Bootstrapping.iff]
'''+s[b:]
# Definitions are reduced only explicitly, to keep finite proof-search atoms stable.
s=s.replace('private theorem pair_transitive', 'attribute [local irreducible] transitiveTerm rawTransitiveBody rawTransitiveAt\n\nprivate theorem pair_transitive',1)
s=s.replace('private theorem cut_subset', 'attribute [local irreducible] taggedSubsetTerm taggedTransitiveTerm taggedTransitiveBody taggedTransitiveAt taggedPairBody taggedPairAt\n\nprivate theorem cut_subset',1)
# Three diagnostics identify genuinely unused simplifier arguments.
s=s.replace('simp [rawTransitiveAt,rawTransitiveBody,transitiveTerm,subsetTerm,memTerm,\n    Bootstrapping.Semiformula.substs_substs,', 'simp [rawTransitiveAt,rawTransitiveBody,transitiveTerm,subsetTerm,memTerm,\n    ')
s=s.replace('simp [taggedTransitiveAt,taggedTransitiveBody,taggedTransitiveTerm,taggedSubsetTerm,memTerm,\n    Bootstrapping.Semiformula.substs_substs,', 'simp [taggedTransitiveAt,taggedTransitiveBody,taggedTransitiveTerm,taggedSubsetTerm,memTerm,\n    ')
s=s.replace('simp [taggedPairAt,taggedPairBody,taggedPairAll,memTerm,eqTerm,\n    Bootstrapping.Semiformula.substs_substs,', 'simp [taggedPairAt,taggedPairBody,taggedPairAll,memTerm,eqTerm,\n    ')
p.write_text(s)
