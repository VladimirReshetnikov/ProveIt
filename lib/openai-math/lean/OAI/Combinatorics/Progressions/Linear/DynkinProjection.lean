import OAI.Combinatorics.Progressions.Estimates.DynkinTrees

namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

def WordHomogeneous (n : ℕ) (p : WordPolynomial X) : Prop :=
  ∀ w, p.coeff w ≠ 0 → w.length = n

theorem WordHomogeneous.sub {n : ℕ} {p q : WordPolynomial X}
    (hp : WordHomogeneous n p) (hq : WordHomogeneous n q) : WordHomogeneous n (p - q) := by
  intro w hw
  by_cases h : p.coeff w = 0
  · apply hq w
    intro he
    apply hw
    change p.coeff w - q.coeff w = 0
    rw [h, he, sub_zero]
  · exact hp w h

theorem WordHomogeneous.mul {n m : ℕ} {p q : WordPolynomial X}
    (hp : WordHomogeneous n p) (hq : WordHomogeneous m q) : WordHomogeneous (n + m) (p * q) := by
  classical
  intro w hw
  by_contra hlen
  apply hw
  rw [MonoidAlgebra.coeff_mul]
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  have hu' := hp u (Finsupp.mem_support_iff.mp hu)
  have hv' := hq v (Finsupp.mem_support_iff.mp hv)
  have hne : u * v ≠ w := by
    intro he
    apply hlen
    rw [← he, FreeSemigroup.length_mul, hu', hv']
  simp only [hne, ite_false]

theorem commutatorTree_homogeneous (t : FreeMagma X) :
    WordHomogeneous t.length (commutatorTree t) := by
  induction t using FreeMagma.rec with
  | of x =>
    intro w hw
    have he : FreeSemigroup.of x = w := by
      classical
      by_contra hn
      apply hw
      simp [commutatorTree, hn]
    rw [← he]
    rfl
  | mul u v hu hv =>
    apply (hu.mul hv).sub
    simpa only [Nat.add_comm v.length u.length] using hv.mul hu

noncomputable def dynkinProjection (f : X → L) : WordPolynomial X →ₗ[ℚ] L :=
  wordLinearMap (fun w => (w.length : ℚ)⁻¹ • dynkinWord f w)

theorem dynkinProjection_homogeneous (f : X → L) {n : ℕ} {p : WordPolynomial X}
    (hp : WordHomogeneous n p) : dynkinProjection f p = (n : ℚ)⁻¹ • dynkinMap f p := by
  classical
  change p.coeff.sum (fun w r => r • ((w.length : ℚ)⁻¹ • dynkinWord f w)) =
    (n : ℚ)⁻¹ • p.coeff.sum (fun w r => r • dynkinWord f w)
  rw [Finsupp.sum, Finsupp.sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [hp w (Finsupp.mem_support_iff.mp hw), smul_comm]

theorem dynkinProjection_commutatorTree (f : X → L) (t : FreeMagma X) :
    dynkinProjection f (commutatorTree t) = lieTreeEval f t := by
  rw [dynkinProjection_homogeneous f (commutatorTree_homogeneous t),
    dynkinMap_commutatorTree, inv_smul_smul₀]
  exact_mod_cast (Nat.ne_zero_of_lt t.length_pos)

end Erdos3

end

end OAI
