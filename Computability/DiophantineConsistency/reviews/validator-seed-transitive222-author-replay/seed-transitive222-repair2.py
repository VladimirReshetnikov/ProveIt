from pathlib import Path
p=Path('Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorSeedTransitive222.lean');s=p.read_text()
a=s.index('private theorem singleton_hit');b=s.index('private theorem pair_contains',a)
s=s[:a]+'''private theorem singleton_transfer (p v z c : Term V ℒₛₑₜ) :
    Source V ⊢ singletonAt p v 🡒 singletonAt p z 🡒 memTerm v c 🡒 memTerm z c := by
  apply deduct'!
  apply FiniteContext.deduct!
  apply FiniteContext.deduct!
  let Γ := [memTerm v c,singletonAt p z,singletonAt p v]
  have hv : Γ ⊢[Source V] singletonAt p v := by_axm!
  have hz : Γ ⊢[Source V] singletonAt p z := by_axm!
  have hm : Γ ⊢[Source V] memTerm v c := by_axm₀!
  have hu := FiniteContext.of'! (Γ := Γ) (singleton_unique p v z)
  have he : Γ ⊢[Source V] eqTerm v z := ⟨(hu.get ⨀ hv.get) ⨀ hz.get⟩
  have ht := FiniteContext.of'! (Γ := Γ) (source_mem_congr v z c)
  exact ⟨(ht.get ⨀ he.get) ⨀ hm.get⟩

private theorem singleton_hit (p z c : Term V ℒₛₑₜ) :
    Source V ⊢ (∃⁰ hitBody transitiveMatrix p c) 🡒 singletonAt p z 🡒 memTerm z c := by
  apply exists_elim
  rw [hitBody_free,transitiveMatrix_shift,transitiveMatrix_subst]
  have h := singleton_transfer p.shift (Bootstrapping.Semiterm.fvar 0) z.shift c.shift
  have h' : Source V ⊢ (singletonAt p.shift (Bootstrapping.Semiterm.fvar 0) ⋏
      memTerm (Bootstrapping.Semiterm.fvar 0) c.shift) 🡒
      singletonAt p.shift z.shift 🡒 memTerm z.shift c.shift := by cl_prover [h]
  simpa [Bootstrapping.Semiformula.shift_imp,singletonAt_shift,memTerm] using h'

'''+s[b:]
a=s.index('private theorem pair_closed_singleton');b=s.index('private theorem pair_closed_point',a)
s=s[:a]+'''private theorem pair_closed_singleton (s c y z p : Term V ℒₛₑₜ) :
    Source V ⊢ singletonAt p z 🡒 pairAt transitiveMatrix s c 🡒
      memTerm y c 🡒 memTerm z y 🡒 memTerm z c := by
  apply deduct'!
  apply FiniteContext.deduct!
  apply FiniteContext.deduct!
  apply FiniteContext.deduct!
  let Γ := [memTerm z y,memTerm y c,pairAt transitiveMatrix s c,singletonAt p z]
  have hp : Γ ⊢[Source V] singletonAt p z := by_axm!
  have hpair : Γ ⊢[Source V] pairAt transitiveMatrix s c := by_axm!
  have hy : Γ ⊢[Source V] memTerm y c := by_axm!
  have hz : Γ ⊢[Source V] memTerm z y := by_axm₀!
  have hcl := FiniteContext.of'! (Γ := Γ) (pair_closure (transitiveMatrix (V := V)) s c y)
  have hc : Γ ⊢[Source V] closureTerm transitiveMatrix c y := ⟨(hcl.get ⨀ hpair.get) ⨀ hy.get⟩
  have hsub := FiniteContext.of'! (Γ := Γ) (singleton_subset p z y)
  have hpy : Γ ⊢[Source V] subsetTerm p y := ⟨(hsub.get ⨀ hp.get) ⨀ hz.get⟩
  have hstep := closure_step (transitiveMatrix (V := V)) c y p z
  rw [transitiveMatrix_subst] at hstep
  have hs := FiniteContext.of'! (Γ := Γ) hstep
  have hex : Γ ⊢[Source V] ∃⁰ hitBody transitiveMatrix p c := ⟨((hs.get ⨀ hc.get) ⨀ hpy.get) ⨀ hp.get⟩
  have hhit := FiniteContext.of'! (Γ := Γ) (singleton_hit p z c)
  exact ⟨(hhit.get ⨀ hex.get) ⨀ hp.get⟩

'''+s[b:]
# Make both projections of the cut explicit before combining source implications.
a=s.index('def taggedSubsetTerm')
s=s[:a]+'''private theorem cut_forward (U t c z : Term V ℒₛₑₜ) :
    Source V ⊢ guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) U t c 🡒 memTerm t z 🡒 memTerm z c 🡒 memTerm z U := by
  cl_prover [cut_spec U t c z]
private theorem cut_backward (U t c z : Term V ℒₛₑₜ) :
    Source V ⊢ guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) U t c 🡒 memTerm t z 🡒 memTerm z U 🡒 memTerm z c := by
  cl_prover [cut_spec U t c z]

private theorem cut_point (U t c y z : Term V ℒₛₑₜ) :
    Source V ⊢ guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) U t c 🡒 transitiveTerm U 🡒
      memTerm t y 🡒 memTerm y c 🡒 memTerm t z 🡒 memTerm z y 🡒 memTerm z c := by
  apply deduct'!
  apply FiniteContext.deduct!
  apply FiniteContext.deduct!
  apply FiniteContext.deduct!
  apply FiniteContext.deduct!
  apply FiniteContext.deduct!
  let Γ := [memTerm z y,memTerm t z,memTerm y c,memTerm t y,transitiveTerm U,
    guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) U t c]
  have hg : Γ ⊢[Source V] guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) U t c := by_axm!
  have htr : Γ ⊢[Source V] transitiveTerm U := by_axm!
  have hty : Γ ⊢[Source V] memTerm t y := by_axm!
  have hyc : Γ ⊢[Source V] memTerm y c := by_axm!
  have htz : Γ ⊢[Source V] memTerm t z := by_axm!
  have hzy : Γ ⊢[Source V] memTerm z y := by_axm₀!
  have hf := FiniteContext.of'! (Γ := Γ) (cut_forward U t c y)
  have hyU : Γ ⊢[Source V] memTerm y U := ⟨((hf.get ⨀ hg.get) ⨀ hty.get) ⨀ hyc.get⟩
  have hts := FiniteContext.of'! (Γ := Γ) (transitive_spec U y z)
  have hzU : Γ ⊢[Source V] memTerm z U := ⟨((hts.get ⨀ htr.get) ⨀ hyU.get) ⨀ hzy.get⟩
  have hb := FiniteContext.of'! (Γ := Γ) (cut_backward U t c z)
  exact ⟨((hb.get ⨀ hg.get) ⨀ htz.get) ⨀ hzU.get⟩

'''+s[a:]
s=s.replace('''cl_prover [cut_spec U.shift t.shift c.shift y.shift,
            cut_spec U.shift t.shift c.shift (Bootstrapping.Semiterm.fvar 0),
            transitive_spec U.shift y.shift (Bootstrapping.Semiterm.fvar 0)]''','''cl_prover [cut_point U.shift t.shift c.shift y.shift (Bootstrapping.Semiterm.fvar 0)]''')
s=s.replace('cl_prover [cut_tag U t c,cut_spec U t c a,cut_transitive U t c]', 'cl_prover [cut_tag U t c,cut_backward U t c a,cut_transitive U t c]')
s=s.replace('simpa only [Γ,List.map_cons,List.map_nil,rawTransitiveAt_shift] using', 'simpa only [Γ,List.map_cons,List.map_nil,rawTransitiveAt_shift,Bootstrapping.Semiformula.shift_verum] using')
s=s.replace('simpa only [Γ,List.map_cons,List.map_nil,rawPairAt_shift] using', 'simpa only [Γ,List.map_cons,List.map_nil,rawPairAt_shift,Bootstrapping.Semiformula.shift_verum] using')
s=s.replace('FirstOrder.Semiformula.quote_def,Matrix.vecHead,Matrix.vecTail,Bootstrapping.iff]', 'Matrix.vecHead,Matrix.vecTail,Bootstrapping.iff]')
p.write_text(s)
# Parenthesize quantification as an actual conjunction operand in the focused check.
p=Path('Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorSeedTransitive222Checks.lean');s=p.read_text()
s=s.replace('    memTerm a.bShift (Bootstrapping.Semiterm.bvar 0) ⋏\n      ∀⁰ (', '    memTerm a.bShift (Bootstrapping.Semiterm.bvar 0) ⋏\n      (∀⁰ (')
s=s.replace('(Bootstrapping.Semiterm.bvar 2))) := rfl', '(Bootstrapping.Semiterm.bvar 2)))) := rfl')
p.write_text(s)
