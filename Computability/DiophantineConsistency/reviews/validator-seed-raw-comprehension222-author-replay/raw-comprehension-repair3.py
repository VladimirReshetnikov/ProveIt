from pathlib import Path
p=Path('Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorSeedRawComprehension222.lean');s=p.read_text()
s=s.replace("  apply deduct'!\n  apply deduct'!", "  apply deduct'!\n  apply FiniteContext.deduct!")
s=s.replace("  cl_prover [hp',hz',hh,ht]", "  cl_prover 64 [hp',hz',hh,ht,hs]")
s=s.replace("      cl_prover [hc',hst',hh']", "      cl_prover 64 [hc',hst',hh']")
s=s.replace('  change Source V ⊢ pairAt (rawAugMatrix θ a r) r c 🡒\n    (rawAugMatrix θ a r).subst ![a,r] 🡒 ∃⁰ hitBody (rawAugMatrix θ a r) r c at h', '''  have h' : Source V ⊢ pairAt (rawAugMatrix θ a r) r c 🡒
    (rawAugMatrix θ a r).subst ![a,r] 🡒 ∃⁰ hitBody (rawAugMatrix θ a r) r c := by
    simpa only [hitBody] using h''')
s=s.replace('  cl_prover [h,hr,hm]\n','  cl_prover [h\',hr,hm]\n')
# Generic syntax identities keep large body parameters opaque in existential elimination.
a=s.index('private theorem pair_aug_cover');b=s.index('\nprivate theorem pair_aug_step',a)
s=s[:a]+'''private def supportCore (K : Semiformula V ℒₛₑₜ 2) (z : Term V ℒₛₑₜ) :
    Semiformula V ℒₛₑₜ 1 := K.subst ![z.bShift,Bootstrapping.Semiterm.bvar 0]
private def rawProperty (θ : Semiformula V ℒₛₑₜ 1) (a z : Term V ℒₛₑₜ) :
    Formula V ℒₛₑₜ := eqTerm z a ⋎ (memTerm z a ⋏ θ.subst ![z])
@[simp] private theorem supportCore_free (K : Semiformula V ℒₛₑₜ 2) (z : Term V ℒₛₑₜ) :
    (supportCore K z).free=K.shift.subst ![z.shift,Bootstrapping.Semiterm.fvar 0] := by
  rcases term_is_fvar z with ⟨z,rfl⟩
  simp [supportCore,Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_substs,
    Bootstrapping.Semiformula.substs_substs,SemitermVec.q,Matrix.vecHead,Matrix.vecTail]
@[simp] private theorem rawProperty_shift (θ : Semiformula V ℒₛₑₜ 1) (a z : Term V ℒₛₑₜ) :
    (rawProperty θ a z).shift=rawProperty θ.shift a.shift z.shift := by
  simp [rawProperty,eqTerm,memTerm,Bootstrapping.Semiformula.shift_substs,
    Matrix.comp_vecCons',Matrix.vecHead,Matrix.vecTail]
attribute [local irreducible] supportCore rawProperty

private theorem pair_aug_cover (θ : Semiformula V ℒₛₑₜ 1) (a r c z : Term V ℒₛₑₜ) :
    Source V ⊢ pairAt (rawAugMatrix θ a r) r c 🡒 memTerm z c 🡒
      (eqTerm z a ⋎ (memTerm z a ⋏ θ.subst ![z])) := by
  have he : Source V ⊢ (∃⁰ supportCore (rawAugMatrix θ a r) z) 🡒 rawProperty θ a z := by
    apply exists_elim
    rw [supportCore_free,rawProperty_shift,rawAugMatrix_shift,rawAugMatrix_subst]
    unfold rawProperty
    cl_prover
  have hs := pair_support (rawAugMatrix θ a r) r c z
  have he' : Source V ⊢ (∃⁰ (rawAugMatrix θ a r).subst ![z.bShift,Bootstrapping.Semiterm.bvar 0]) 🡒
      (eqTerm z a ⋎ (memTerm z a ⋏ θ.subst ![z])) := by
    simpa only [supportCore,rawProperty] using he
  cl_prover [hs,he']
''' +s[b:]
# Remove diagnostic-listed unused simplifier arguments only in targeted proofs.
for name,nextname in [('supportBody_free','hitBody_free'),('closure_step','singleton_spec'),('rawAugMatrix_subst','matrix_unique')]:
 a=s.index('theorem '+name);b=s.index('theorem '+nextname,a)
 seg=s[a:b].replace("Matrix.comp_vecCons',",'');s=s[:a]+seg+s[b:]
a=s.index("theorem singletonBody_free'");b=s.index('attribute [local irreducible] singletonAt',a)
s=s[:a]+s[a:b].replace(',←Bootstrapping.Semiterm.bShift_shift_comm','')+s[b:]
# Rewrite raw substitutions through typed identities, avoiding hidden raw side-condition search.
pos=s.index('theorem rawAugMatrixCode_eq')
s=s[:pos]+'''private theorem at2_eq {n : ℕ} (u v : Semiterm V ℒₛₑₜ n) :
    at2Code u.val v.val eqCode=(eqTerm u v).val := by
  rw [eq_cast]
  change (((⌜eqMeta⌝ : Semiformula V ℒₛₑₜ 2).subst ![u,v]).val)=(eqTerm u v).val
  congr 1
  simp [eqMeta,eqTerm,FirstOrder.Semiformula.quote_def,Matrix.vecHead,Matrix.vecTail]
private theorem at2_mem {n : ℕ} (u v : Semiterm V ℒₛₑₜ n) :
    at2Code u.val v.val memCode=(memTerm u v).val := by
  rw [mem_cast]
  change (((⌜seedMem 2 0 1⌝ : Semiformula V ℒₛₑₜ 2).subst ![u,v]).val)=(memTerm u v).val
  congr 1
  simp [seedMem,memTerm,FirstOrder.Semiformula.quote_def,Matrix.vecHead,Matrix.vecTail]

'''+s[pos:]
# These matching rewrites have explicit typed argument values before broader expansion.
for name in ['rawAugMatrixCode_eq','rawAugBodyCode_eq']:
 a=s.index('theorem '+name);b=s.find('\n\n',s.index(' := by',a))
 # body ends at next blank; use known simp line position
 pos=s.index('  simp [rawAug',a)
 prep='''  have he0 := at2_eq (Bootstrapping.Semiterm.bvar (0 : Fin 2)) (Bootstrapping.Semiterm.fvar a)
  have hm0 := at2_mem (Bootstrapping.Semiterm.bvar (0 : Fin 2)) (Bootstrapping.Semiterm.fvar a)
'''
 if name=='rawAugMatrixCode_eq':prep+='''  have he1 := at2_eq (Bootstrapping.Semiterm.bvar (1 : Fin 2)) (Bootstrapping.Semiterm.fvar r)
  simp only [Bootstrapping.Semiterm.val_bvar,Bootstrapping.Semiterm.val_fvar] at he0 hm0 he1
  simp only [rawAugMatrixCode,b0_cast,b1_cast,he0,hm0,he1]
'''
 else:prep+='''  simp only [Bootstrapping.Semiterm.val_bvar,Bootstrapping.Semiterm.val_fvar] at he0 hm0
  simp only [rawAugBodyCode,b0_cast,he0,hm0]
'''
 s=s[:pos]+prep+s[pos:]
s=s.replace('FirstOrder.Semiformula.quote_def,FirstOrder.Semiterm.quote_def,Matrix.vecHead,Matrix.vecTail','FirstOrder.Semiformula.quote_def,Matrix.vecHead,Matrix.vecTail')
p.write_text(s)
