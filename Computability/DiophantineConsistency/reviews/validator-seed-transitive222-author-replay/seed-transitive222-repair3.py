from pathlib import Path
p=Path('Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorSeedTransitive222.lean');s=p.read_text()
# The named finite contexts must be unfolded for the actual membership rule.
for line in s.splitlines():
 if 'have ' in line and 'Γ ⊢[Source V]' in line and ':= by_axm!' in line:
  s=s.replace(line,line.replace(':= by_axm!',':= by simp only [Γ]; exact by_axm!'))
a=s.index('private theorem cut_subset');b=s.index('private theorem cut_transitive',a)
s=s[:a]+'''private theorem cut_subset (U t c y : Term V ℒₛₑₜ) :
    Source V ⊢ guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) U t c 🡒 transitiveTerm U 🡒
      memTerm t y 🡒 memTerm y c 🡒 taggedSubsetTerm t c y := by
  apply deduct'!
  apply FiniteContext.deduct!
  apply FiniteContext.deduct!
  apply FiniteContext.deduct!
  unfold taggedSubsetTerm
  apply TProof.generalize!
  let Γ := [memTerm y c,memTerm t y,transitiveTerm U,
    guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) U t c].map Bootstrapping.Semiformula.shift
  have hg : Γ ⊢[Source V] guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) U.shift t.shift c.shift := by
    simp only [Γ,List.map_cons,List.map_nil,guardedAt_shift,Bootstrapping.Semiformula.shift_verum]
    exact by_axm!
  have htr : Γ ⊢[Source V] transitiveTerm U.shift := by
    simp only [Γ,List.map_cons,List.map_nil,transitiveTerm_shift]
    exact by_axm!
  have hty : Γ ⊢[Source V] memTerm t.shift y.shift := by
    simp [Γ,memTerm]; exact by_axm!
  have hyc : Γ ⊢[Source V] memTerm y.shift c.shift := by
    simp [Γ,memTerm]; exact by_axm₀!
  have hp := FiniteContext.of'! (Γ := Γ)
    (cut_point U.shift t.shift c.shift y.shift (Bootstrapping.Semiterm.fvar 0))
  have h : Γ ⊢[Source V] memTerm t.shift (Bootstrapping.Semiterm.fvar 0) 🡒
      memTerm (Bootstrapping.Semiterm.fvar 0) y.shift 🡒
      memTerm (Bootstrapping.Semiterm.fvar 0) c.shift :=
    ⟨(((hp.get ⨀ hg.get) ⨀ htr.get) ⨀ hty.get) ⨀ hyc.get⟩
  simpa [Γ,memTerm,Bootstrapping.Semiformula.free,←Bootstrapping.Semiterm.bShift_shift_comm] using h

'''+s[b:]
p.write_text(s)
