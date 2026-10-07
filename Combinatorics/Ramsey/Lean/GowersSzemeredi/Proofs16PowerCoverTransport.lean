import GowersSzemeredi.Proofs16Translations

/-! Relation covers with the actual power exponent, graph budget, and
starting width. Translation preserves all four quantitative parameters. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A relation admits proper multilinear covers on every sufficiently wide
proper box. The explicit width threshold is part of the assertion. -/
def LargeBoxMultilinearCover {N k : Nat} [NeZero N]
    (Gamma : Finset (Point N k × ZMod N)) (rho C e T : Real) : Prop :=
  ∀ P : Box N k, P.IsProper → T ≤ (P.width : Real) →
    ∃ M q : Nat, ∃ H : Finset (Point N k), ∃ Q : Fin M → Box N k,
      ∃ mu : Fin M → Fin q → Point N k → ZMod N,
        H ⊆ P.carrier ∧ (1 - rho) * (P.carrier.card : Real) ≤ H.card ∧
        IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧ (q : Real) ≤ C ∧
        (∀ j, (P.width : Real) ^ e ≤ (Q j).width) ∧
        (∀ j i, IsMultilinear (mu j i)) ∧
        ∀ j x, x ∈ (Q j).carrier → x ∈ H → ∀ y,
          (x, y) ∈ Gamma → ∃ i, y = mu j i x

theorem LargeBoxMultilinearCover.mono {N k : Nat} [NeZero N]
    {Gamma Delta : Finset (Point N k × ZMod N)} {rho C e T : Real}
    (h : LargeBoxMultilinearCover Gamma rho C e T) (hsub : Delta ⊆ Gamma) :
    LargeBoxMultilinearCover Delta rho C e T := by
  intro P hP hT
  obtain ⟨M, q, H, Q, mu, hH, hm, hp, hproper, hq, hw, hmu, hc⟩ := h P hP hT
  exact ⟨M, q, H, Q, mu, hH, hm, hp, hproper, hq, hw, hmu,
    fun j x hx hh y hy => hc j x hx hh y (hsub hy)⟩

/-- Translation changes neither exceptional mass, graph count, exponent,
nor minimum parent width. No unit-parameter comparison is used. -/
theorem LargeBoxMultilinearCover.translate {N k : Nat} [NeZero N] [Fact N.Prime]
    {Gamma : Finset (Point N k × ZMod N)} {rho C e T : Real}
    (h : LargeBoxMultilinearCover Gamma rho C e T) (t : Point N k) :
    LargeBoxMultilinearCover (Gamma.image (fun z => (z.1 + t, z.2))) rho C e T := by
  classical
  intro P hP hT
  obtain ⟨M, q, H, Q, mu, hH, hm, hp, hproper, hq, hw, hmu, hc⟩ :=
    h (P.translate (-t)) (hP.translate (-t)) (by simpa using hT)
  refine ⟨M, q, H.image (fun x => x + t), fun j => (Q j).translate t,
    fun j i x => mu j i (x + -t), ?_, ?_, ?_, fun j => (hproper j).translate t,
    hq, ?_, fun j i => (hmu j i).translate (-t), ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa using (Box.translate_mem_carrier (P.translate (-t)) t y).mpr (hH hy)
  · rw [Finset.card_image_of_injective _ (add_left_injective t)]
    simpa using hm
  · simpa using hp.translate t
  · intro j
    simpa using hw j
  · intro j x hx hh y hxy
    obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp hxy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    obtain ⟨i, hi⟩ := hc j a ((Box.translate_mem_carrier _ _ _).mp hx)
      ((add_left_injective t).mem_finset_image.mp hh) b hab
    exact ⟨i, by simpa using hi⟩

end LeanProofs.GowersSzemeredi
