import Surreal.Algebra.DiophantineConstants

/-!
# The existential graph of the constant-term retraction

The algebraic part of `odg:def:thm:ctgraph` and `odg:def:eq:ctgraph`.
An ordinary-constant definition combined with the quadratic kernel test
determines a unique output. The displayed Xi version uses exactly six
existential ring witnesses.
-/

namespace Surreal.ConstantTermGraph

noncomputable section

variable {R O S : Type*} [CommRing R] [CommRing O] [CommRing S]

/-- The parameter-free graph formula printed in the source. -/
def Graph (x n : R) : Prop :=
  DiophantineConstants.Xi n ∧ ∃ y : R, (x - n) ^ 2 = 2 * y ^ 2

/-- Expanding Xi exhibits exactly six existential witnesses. -/
theorem graph_iff_six_witnesses (x n : R) : Graph x n ↔
    ∃ u v w s t y : R, DiophantineConstants.System n u v w s t ∧
      (x - n) ^ 2 = 2 * y ^ 2 := by
  constructor
  · rintro ⟨⟨u, v, w, s, t, h⟩, y, hy⟩
    exact ⟨u, v, w, s, t, y, h, hy⟩
  · rintro ⟨u, v, w, s, t, y, h, hy⟩
    exact ⟨⟨u, v, w, s, t, h⟩, y, hy⟩

/-- Every unital ring homomorphism carries graph witnesses to graph witnesses. -/
theorem Graph.map (φ : R →+* S) {x n : R} (h : Graph x n) : Graph (φ x) (φ n) := by
  obtain ⟨hn, y, hy⟩ := h
  refine ⟨hn.map φ, φ y, ?_⟩
  have he := congrArg φ hy
  simpa only [map_pow, map_sub, map_mul, map_ofNat] using he

/-- Any definition of the ordinary constants works with a quadratic kernel definition. -/
theorem standard_graph_iff (ct : R →+* O) (ι : O →+* R)
    (hsection : ∀ b : O, ct (ι b) = b) (Std : R → Prop)
    (hStd : ∀ n : R, Std n ↔ ∃ b : O, n = ι b)
    (hkernel : ∀ a : R, (∃ y : R, a ^ 2 = 2 * y ^ 2) ↔ ct a = 0)
    (x n : R) : (Std n ∧ ∃ y : R, (x - n) ^ 2 = 2 * y ^ 2) ↔ n = ι (ct x) := by
  constructor
  · rintro ⟨hn, hy⟩
    obtain ⟨b, rfl⟩ := (hStd n).mp hn
    have he := (hkernel (x - ι b)).mp hy
    rw [map_sub, hsection, sub_eq_zero] at he
    rw [he]
  · rintro rfl
    refine ⟨(hStd _).mpr ⟨ct x, rfl⟩, (hkernel _).mpr ?_⟩
    rw [map_sub, hsection, sub_self]

/-- The literal graph is the embedded retraction graph whenever Xi and the quadratic test hold. -/
theorem graph_iff (ct : R →+* O) (ι : O →+* R)
    (hsection : ∀ b : O, ct (ι b) = b)
    (hXi : ∀ n : R, DiophantineConstants.Xi n ↔ ∃ b : O, n = ι b)
    (hkernel : ∀ a : R, (∃ y : R, a ^ 2 = 2 * y ^ 2) ↔ ct a = 0) (x n : R) :
    Graph x n ↔ n = ι (ct x) :=
  standard_graph_iff ct ι hsection DiophantineConstants.Xi hXi hkernel x n

/-- The output is unique; uniqueness of the six witnesses is not required. -/
theorem existsUnique_output (ct : R →+* O) (ι : O →+* R)
    (hsection : ∀ b : O, ct (ι b) = b)
    (hXi : ∀ n : R, DiophantineConstants.Xi n ↔ ∃ b : O, n = ι b)
    (hkernel : ∀ a : R, (∃ y : R, a ^ 2 = 2 * y ^ 2) ↔ ct a = 0) (x : R) :
    ∃! n : R, Graph x n :=
  ⟨ι (ct x), (graph_iff ct ι hsection hXi hkernel x _).mpr rfl,
    fun n hn => (graph_iff ct ι hsection hXi hkernel x n).mp hn⟩

end
end Surreal.ConstantTermGraph
