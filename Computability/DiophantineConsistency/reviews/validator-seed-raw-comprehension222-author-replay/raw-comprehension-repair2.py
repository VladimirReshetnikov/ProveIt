from pathlib import Path
p=Path('Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorSeedRawComprehension222.lean')
s=p.read_text()
# Exact literal quotations, not relying on simplifier normalization of source sugar.
start=s.index('private theorem source_mem_congr')
a=s.index('  have hq :',start); b=s.index("  have h' :",a)
hq=s[a:b]
pos=s.index("  have h' :",s.index('private theorem source_mem_ext'))
s=s[:pos]+hq+s[pos:]
pos=s.index("  have h' :",s.index('private theorem source_trans'))
s=s[:pos]+'''  have hq : (⌜(Rewriting.emb (Theory.Eq.trans ℒₛₑₜ) : SetTheoryProposition)⌝ : Formula V ℒₛₑₜ)=
      ∀⁰ ∀⁰ ∀⁰ (Bootstrapping.Semiformula.nrel Language.Eq.eq
        ![Bootstrapping.Semiterm.bvar 2,Bootstrapping.Semiterm.bvar 1] ⋎
        (Bootstrapping.Semiformula.nrel Language.Eq.eq
          ![Bootstrapping.Semiterm.bvar 1,Bootstrapping.Semiterm.bvar 0] ⋎
          eqTerm (Bootstrapping.Semiterm.bvar 2) (Bootstrapping.Semiterm.bvar 0))) := rfl
  rw [hq] at h
'''+s[pos:]
s=s.replace('simpa [supportBody,closureTerm,subsetTerm,memTerm,seedMem,seedSubset,','simpa [pairAt,pairMatrix,supportBody,closureTerm,subsetTerm,memTerm,seedMem,seedSubset,')
s=s.replace('  have ha := hs ⨀ hp\n','  have hp\' := hp\n  simp [closureTerm,subsetTerm,memTerm] at hp\'\n  have ha := show _ ⊢[Source V] _ from ⟨hs.get ⨀ hp\'.get⟩\n')
s=s.replace('simpa [hitBody,memTerm,Bootstrapping.Semiformula.substs_substs,SemitermVec.q,','simpa [closureTerm,subsetTerm,hitBody,memTerm,Bootstrapping.Semiformula.substs_substs,SemitermVec.q,')
s=s.replace('simpa [eqTerm,memTerm] using TProof.specialize_with_ctx! h w','simpa [singletonAt,eqTerm,memTerm] using TProof.specialize_with_ctx! h w')
s=s.replace('  cl_prover [hz,ha,hm,hr]\n','''  have hm' : Source V ⊢ eqTerm p r 🡒 memTerm z p 🡒 memTerm z r := by
    cl_prover [hm,hr]
  have hz' : Source V ⊢ eqTerm p r 🡒 singletonAt p z 🡒 memTerm z r := by
    cl_prover [hm',hz]
  cl_prover [hz',ha]
''')
# Freeze finite atoms locally to avoid expanding huge source/body context during generalization.
pos=s.index('private theorem singleton_subset')
s=s[:pos]+'''@[simp] private theorem singletonBody_free' (t : Term V ℒₛₑₜ) :
    (singletonBody t).free=singletonAt (Bootstrapping.Semiterm.fvar 0) t.shift := by
  rcases term_is_fvar t with ⟨t,rfl⟩
  simp [singletonBody,singletonAt,eqTerm,memTerm,Bootstrapping.Semiformula.free,
    SemitermVec.q,←Bootstrapping.Semiterm.bShift_shift_comm]

attribute [local irreducible] singletonAt subsetTerm closureTerm supportBody hitBody

'''+s[pos:]
s=s.replace('memTerm z.shift a.shift := by simp only [List.map_cons,List.map_nil]; exact by_axm₀!', 'memTerm z.shift a.shift := by simp [memTerm] ; exact by_axm₀!')
s=s.replace('  cl_prover [hy,hz,hp,hr,hs,ht]\n','''  have hp' : Source V ⊢ singletonAt p y 🡒 singletonAt p z 🡒 eqTerm y z := by
    cl_prover [hp,hr]
  have hz' : Source V ⊢ eqTerm p r 🡒 singletonAt p z 🡒 singletonAt r a 🡒 eqTerm a z := by
    cl_prover [hz,hs]
  have hh : Source V ⊢ eqTerm p r 🡒 singletonAt p y 🡒 singletonAt r a 🡒
      eqTerm z a 🡒 eqTerm y z := by
    cl_prover [hy,hs,ht]
  cl_prover [hp',hz',hh,ht]
''')
# Keep raw formulas opaque outside their explicit rewriting lemmas.
pos=s.index('private theorem matrix_unique')
s=s[:pos]+'attribute [local irreducible] rawAugMatrix rawAugBody rawAugAt\n\n'+s[pos:]
s=s.replace('      cl_prover [hm,hc,hs,hst,hh,hk]\n','''      have hc' : Source V ⊢ singletonAt r.shift a.shift 🡒
          pairAt (rawAugMatrix θ.shift a.shift r.shift) r.shift c.shift 🡒
            closureTerm (rawAugMatrix θ.shift a.shift r.shift) c.shift a.shift := by
        cl_prover [hm,hc]
      have hst' : Source V ⊢ singletonAt p z.shift 🡒 memTerm z.shift a.shift 🡒
          θ.shift.subst ![z.shift] 🡒 closureTerm (rawAugMatrix θ.shift a.shift r.shift) c.shift a.shift 🡒
          ∃⁰ hitBody (rawAugMatrix θ.shift a.shift r.shift) p c.shift := by
        cl_prover [hs,hk,hst]
      have hh' : Source V ⊢ singletonAt p z.shift 🡒 memTerm z.shift a.shift 🡒
          θ.shift.subst ![z.shift] 🡒 singletonAt r.shift a.shift 🡒
          (∃⁰ hitBody (rawAugMatrix θ.shift a.shift r.shift) p c.shift) 🡒 memTerm z.shift c.shift := by
        cl_prover [hk,hh]
      cl_prover [hc',hst',hh']
''')
a=s.index('    simpa [singletonBody,singletonAt,eqTerm,memTerm,Bootstrapping.Semiformula.free,',s.index('private theorem pair_aug_step'))
b=s.index(' using h\n',a)+len(' using h\n')
s=s[:a]+'''    simpa [singletonBody_free',singletonAt_shift,memTerm,
      Bootstrapping.Semiformula.shift_substs,Matrix.comp_vecCons',Matrix.vecHead,Matrix.vecTail,p] using h
'''+s[b:]
a=s.index('    simpa [singletonBody,singletonAt,eqTerm,memTerm,Bootstrapping.Semiformula.free,',s.index('theorem raw_augmented'))
b=s.index(" using h'\n",a)+len(" using h'\n")
s=s[:a]+'''    simpa only [singletonBody_free',Bootstrapping.Semiformula.shift_exs,rawAugBody_shift] using h'
'''+s[b:]
s=s.replace('  simpa [Proof] using (rawAugProof θ a).derivationOf','  simpa only [Source,Theory.internalize,Proof,Sequent.val_insert,Sequent.val_empty,singleton_eq_insert] using (rawAugProof θ a).derivationOf')
s=s.replace('  rw [b1Code,FirstOrder.Semiterm.coe_quote_eq_quote]\n  rfl','  rw [b1Code,FirstOrder.Semiterm.coe_quote_eq_quote]\n  simp [FirstOrder.Semiterm.quote_def]')
s=s.replace('FirstOrder.Semiformula.quote_def]\n','FirstOrder.Semiformula.quote_def,FirstOrder.Semiterm.quote_def,Matrix.vecHead,Matrix.vecTail]\n')
s=s.replace('FirstOrder.Semiformula.quote_def,Bootstrapping.iff]\n','FirstOrder.Semiformula.quote_def,FirstOrder.Semiterm.quote_def,Matrix.vecHead,Matrix.vecTail,Bootstrapping.iff]\n')
p.write_text(s)
