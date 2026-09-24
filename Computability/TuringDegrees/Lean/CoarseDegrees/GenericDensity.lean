import CoarseDegrees.Generic

/-!
# 1-generic sets are not coarsely computable

Jockusch--Schupp 2012, the remark after Proposition 2.15: a coarsely computable set is not
1-generic.  The proof formalized here is the direct one used in the research reports
(synthesis, Lemma 5.1): for a computable set `C`, every string `τ` can be extended by
`|τ| + m + 1` bits that all disagree with `C`; the set of strings obtained in this way is c.e.
and dense, so a 1-generic `X` has, for every `m`, an initial segment of some length `n ≥ m` on
which it disagrees with `C` more than half of the time.  Hence `C △ X` does not have density
zero.  Everything in this file is proved.
-/

noncomputable section

open Filter Topology
open scoped Classical

namespace CoarseDegrees

/-- Extend `σ` by `j` further bits, the bit at position `i` being `b i`. -/
def ext (b : ℕ → Bool) (σ : List Bool) (j : ℕ) : List Bool :=
  Nat.rec σ (fun _ acc => acc ++ [b acc.length]) j

@[simp] theorem ext_zero (b : ℕ → Bool) (σ : List Bool) : ext b σ 0 = σ := rfl

theorem ext_succ (b : ℕ → Bool) (σ : List Bool) (j : ℕ) :
    ext b σ (j + 1) = ext b σ j ++ [b (ext b σ j).length] := rfl

theorem length_ext (b : ℕ → Bool) (σ : List Bool) (j : ℕ) :
    (ext b σ j).length = σ.length + j := by
  induction j with
  | zero => simp
  | succ j ih => rw [ext_succ, List.length_append, ih, List.length_singleton, Nat.add_assoc]

theorem prefix_ext (b : ℕ → Bool) (σ : List Bool) (j : ℕ) : σ <+: ext b σ j := by
  induction j with
  | zero => exact List.prefix_refl _
  | succ j ih => exact ih.trans (by rw [ext_succ]; exact List.prefix_append _ _)

theorem getElem?_ext (b : ℕ → Bool) (σ : List Bool) (j i : ℕ) (h1 : σ.length ≤ i)
    (h2 : i < σ.length + j) : (ext b σ j)[i]? = some (b i) := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [ext_succ]
    by_cases hi : i < σ.length + j
    · rw [List.getElem?_append_left (by rw [length_ext]; exact hi)]
      exact ih hi
    · have hieq : i = σ.length + j := by omega
      rw [List.getElem?_append_right (by rw [length_ext]; omega), length_ext, hieq]
      simp

/-- The extension map is computable when the bit pattern is. -/
theorem computable_ext {b : ℕ → Bool} (hb : Computable b) (m : ℕ) :
    Computable (fun σ : List Bool => ext b σ (σ.length + m + 1)) := by
  have hf : Computable (fun σ : List Bool => σ.length + m + 1) :=
    (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.list_length (Primrec.const m))
      (Primrec.const 1)).to_comp
  have hh : Computable₂ (fun (_ : List Bool) (p : ℕ × List Bool) => p.2 ++ [b p.2.length]) :=
    (Computable.list_concat.comp (Computable.snd.comp Computable.snd)
      (hb.comp (Computable.list_length.comp (Computable.snd.comp Computable.snd)))).to₂
  exact Computable.nat_rec hf Computable.id hh

/-- The range of a computable map on strings is a c.e. set of strings. -/
theorem rePred_range {F : List Bool → List Bool} (hF : Computable F) :
    REPred (fun σ => ∃ τ, F τ = σ) := by
  have hp : Partrec₂ (fun (σ : List Bool) (n : ℕ) =>
      (Part.some (decide ((Encodable.decode (α := List Bool) n).map F = some σ)) : Part Bool)) := by
    have : Computable (fun p : List Bool × ℕ =>
        decide ((Encodable.decode (α := List Bool) p.2).map F = some p.1)) :=
      Primrec.eq.decide.to_comp.comp
        (Computable.option_map (Computable.decode.comp Computable.snd)
          (hF.comp Computable.snd).to₂)
        (Computable.option_some.comp Computable.fst)
    exact this.partrec
  refine (Partrec.rfind hp).dom_re.of_eq fun σ => ?_
  rw [Nat.rfind_dom]
  constructor
  · rintro ⟨n, hn, -⟩
    have hn' : (Encodable.decode (α := List Bool) n).map F = some σ := by simpa using hn
    cases hdec : Encodable.decode (α := List Bool) n with
    | none => rw [hdec] at hn'; exact absurd hn' (by simp)
    | some τ =>
      rw [hdec] at hn'
      exact ⟨τ, Option.some.inj hn'⟩
  · rintro ⟨τ, hτ⟩
    refine ⟨Encodable.encode τ, ?_, fun _ => trivial⟩
    simp [hτ]

/-- The counting lemma: if an initial segment of `X` of the form `ext b τ j` is given, where
`b i` is `true` exactly when `i ∉ C`, then `C △ X` has at least `j` elements below
`|τ| + j`. -/
theorem le_count_symmDiff {C X : Set ℕ} {b : ℕ → Bool} (hb : ∀ i, b i = true ↔ i ∉ C)
    {τ : List Bool} {j : ℕ} (hpre : IsPrefixOf (ext b τ j) X) :
    j ≤ count (symmDiff C X) (τ.length + j) := by
  have hsub : Finset.Ico τ.length (τ.length + j) ⊆
      (Finset.range (τ.length + j)).filter (· ∈ symmDiff C X) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨hi.2, ?_⟩
    have hlen : i < (ext b τ j).length := by rw [length_ext]; exact hi.2
    have hget : (ext b τ j)[i] = b i := by
      have := getElem?_ext b τ j i hi.1 hi.2
      rw [List.getElem?_eq_getElem hlen] at this
      exact Option.some.inj this
    have hX : b i = true ↔ i ∈ X := by
      rw [← hget]
      exact hpre i hlen
    rw [Set.mem_symmDiff]
    by_cases hC : i ∈ C
    · left
      refine ⟨hC, fun hiX => ?_⟩
      exact ((hb i).mp (hX.mpr hiX)) hC
    · right
      exact ⟨hX.mp ((hb i).mpr hC), hC⟩
  calc j = (Finset.Ico τ.length (τ.length + j)).card := by simp
    _ ≤ count (symmDiff C X) (τ.length + j) := Finset.card_le_card hsub

/-- A 1-generic set is not coarsely computable (Jockusch--Schupp 2012, remark after
Proposition 2.15). -/
theorem OneGeneric.not_setCoarselyComputable {X : Set ℕ} (hX : OneGeneric X) :
    ¬ SetCoarselyComputable X := by
  rintro ⟨C, hC, hCX⟩
  obtain ⟨f, hf, hfeq⟩ := ComputablePred.computable_iff.mp hC
  -- the bit pattern opposite to `C`
  let b : ℕ → Bool := fun i => !f i
  have hbcomp : Computable b := Primrec.not.to_comp.comp hf
  have hb : ∀ i, b i = true ↔ i ∉ C := by
    intro i
    have := congrFun hfeq i
    rw [this]
    simp [b]
  -- density zero gives an eventual bound `count / n < 1/2`
  have hev : ∀ᶠ n : ℕ in atTop, (count (symmDiff C X) n : ℝ) / n < 1 / 2 :=
    (tendsto_order.1 hCX).2 (1 / 2) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  -- meet the dense c.e. set of strings `ext b τ (|τ| + N + 1)`
  obtain ⟨σ, hσX, hσ⟩ := hX _ (rePred_range (computable_ext hbcomp N))
  have hW : ∃ τ, ext b τ (τ.length + N + 1) = σ := by
    rcases hσ with h | h
    · exact h
    · exact absurd ⟨σ, rfl⟩ (h _ (prefix_ext b σ _))
  obtain ⟨τ, rfl⟩ := hW
  have hcount := le_count_symmDiff hb hσX
  set n := τ.length + (τ.length + N + 1) with hn
  have hnN : N ≤ n := by omega
  have hlt := hN n hnN
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  rw [div_lt_iff₀ hnpos] at hlt
  have h2 : (n : ℝ) < 2 * (count (symmDiff C X) n : ℝ) := by
    have : n < 2 * count (symmDiff C X) n := by omega
    exact_mod_cast this
  linarith

end CoarseDegrees
