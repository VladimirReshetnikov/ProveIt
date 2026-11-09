import DiophantineConsistency.ModelBoundedForallArith
import DiophantineConsistency.ArithmeticBinomExpansion

/-! # Fermat's little theorem in models of `𝗜𝚺₁`

In every model `V` of `𝗜𝚺₁`, with the internal power `ArithmeticPow.power`, binomial
coefficient `ArithmeticBinomPascal.binom` and factorial `ArithmeticBinomFactorial.fact`, and with
"irreducible" meaning `1 < p` and only the divisors `1` and `p` (the notion used by
`ModelBoundedForallArith.exists_irred_dvd`, `bez_of_irred` and `euclid_of_irred`):

* `dvd_binom`: `p ∣ binom p k` for `0 < k < p`, from `binom (k+j) k · k! · j! = (k+j)!` and
  `p ∤ k!` for `k < p`;
* `bsum_eq`: the partial binomial sums `Σ_{i<j} binom p i · Xⁱ` are `≡ 1 (mod p)` for
  `1 ≤ j ≤ p`, so the internal binomial theorem gives `(X+1)ᵖ ≡ Xᵖ + 1`;
* `fermat`: `aᵖ = q·p + a` for some `q`, by induction on `a` (also as residues, `fermat_mod`,
  and as a divisibility in the ring of differences, `fermat_ring`);
* `cube_root_of_two_mod_three`: if `p = 3m+2`, every `a` is a cube modulo `p`, namely of
  `b = a^(2m+1)`;
* `neg_three_square_of_witness`: if `p = 3m+1` and some `0 < g < p` has `p ∤ g^m − 1`, then
  `−3` is a square modulo `p`, i.e. `p ∣ x² + 3` with `x = 2g^m + 1`.

The witness of the last item exists in every model, but its existence is a root-count bound
for `X^m − 1` (Lagrange's theorem for polynomials over `𝔽ₚ`, or the `m`-th finite difference
of `X^m`), which is not available internally; see the progress notes. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ModelFermat
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing ArithmeticPow ArithmeticBinomPascal ArithmeticBinomFactorial
open ArithmeticBinomExpansion ModelBoundedForallArith

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Irreducible elements of the model: only the trivial divisors. -/
def Irred (p : V) : Prop := 1 < p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

theorem Irred.pos {p : V} (hp : Irred p) : 0 < p :=
  lt_of_le_of_lt (Arithmetic.zero_le 1) hp.1

theorem not_dvd_of_pos_lt {p m : V} (hm : 0 < m) (hmp : m < p) : ¬ p ∣ m := fun h =>
  absurd (LO.FirstOrder.Arithmetic.le_of_dvd hm h) (not_le.mpr hmp)

theorem Irred.euclid {p : V} (hp : Irred p) {x y : V} (h : p ∣ x * y) : p ∣ x ∨ p ∣ y :=
  euclid_of_irred hp.2 h

/-- An irreducible `p` divides no factorial `m!` with `m < p`. -/
theorem not_dvd_fact {p : V} (hp : Irred p) {m : V} (hm : m < p) : ¬ p ∣ fact m := by
  intro h
  have h' : p ∣ fact m * binom m m := by rw [binom_self, mul_one]; exact h
  have h1 : ¬ p ∣ 1 := not_dvd_of_pos_lt _root_.zero_lt_one hp.1
  obtain ⟨j, hj, hpj⟩ := dvd_factor_of_dvd_desc p m h1 (fun x y h => hp.euclid h) m h'
  exact not_dvd_of_pos_lt (tsub_pos_of_lt hj) (lt_of_le_of_lt tsub_le_self hm) hpj

/-- **`p ∣ binom p k` for `0 < k < p`.** -/
theorem dvd_binom {p : V} (hp : Irred p) {k : V} (hk0 : 0 < k) (hkp : k < p) :
    p ∣ binom p k := by
  obtain ⟨j, rfl⟩ := exists_add_of_le hkp.le
  have hjp : j < k + j := lt_add_of_pos_left j hk0
  have hfact := binom_mul_fact k j
  have hpos : 1 ≤ k + j := pos_iff_one_le.mp hp.pos
  have hdvd : k + j ∣ fact (k + j) := by
    have hi : k + j = (k + j - 1) + 1 := (tsub_add_cancel_of_le hpos).symm
    rw [hi, fact_succ]
    exact dvd_mul_right _ _
  rw [← hfact] at hdvd
  rcases hp.euclid hdvd with h | h
  · rcases hp.euclid h with h | h
    · exact h
    · exact absurd h (not_dvd_fact hp hkp)
  · exact absurd h (not_dvd_fact hp hjp)

/-- Partial binomial sums of the row `p` are `≡ 1 (mod p)`. -/
theorem bsum_eq {p : V} (hp : Irred p) (X : V) (j : V) :
    1 ≤ j → j ≤ p → ∃ q, bsum X p j = q * p + 1 := by
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro h
    exact absurd h (not_le.mpr _root_.zero_lt_one)
  case succ j ih =>
    intro _ hjp
    have hjlt : j < p := lt_of_lt_of_le (lt_add_one j) hjp
    rcases eq_or_ne j 0 with h0 | h0
    · subst h0
      refine ⟨0, ?_⟩
      rw [bsum_succ, bsum_zero, binom_zero_right, power_zero]
      simp
    · have hj0 : 0 < j := pos_iff_ne_zero.mpr h0
      obtain ⟨q, hq⟩ := ih (pos_iff_one_le.mp hj0) hjlt.le
      obtain ⟨c, hc⟩ := dvd_binom hp hj0 hjlt
      refine ⟨q + c * power X j, ?_⟩
      rw [bsum_succ, hq, hc]
      ring

/-- `(X+1)ᵖ = q·p + Xᵖ + 1`: the freshman's dream modulo an irreducible `p`. -/
theorem power_succ_eq {p : V} (hp : Irred p) (X : V) :
    ∃ q, power (X + 1) p = q * p + (power X p + 1) := by
  obtain ⟨r, hr⟩ := bsum_eq hp X p (pos_iff_one_le.mp hp.pos) le_rfl
  refine ⟨r, ?_⟩
  rw [binomial_theorem, bsum_succ, hr, binom_self]
  ring

/-- **Fermat's little theorem**, exact form: `aᵖ = q·p + a`. -/
theorem fermat {p : V} (hp : Irred p) (a : V) : ∃ q, power a p = q * p + a := by
  induction a using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    exact ⟨0, by rw [zero_power_of_pos p hp.pos]; simp⟩
  case succ a ih =>
    obtain ⟨q, hq⟩ := ih
    obtain ⟨r, hr⟩ := power_succ_eq hp a
    refine ⟨r + q, ?_⟩
    rw [hr, hq]
    ring

/-- **Fermat's little theorem**, residues: `aᵖ ≡ a (mod p)`. -/
theorem fermat_mod {p : V} (hp : Irred p) (a : V) : power a p % p = a % p := by
  obtain ⟨q, hq⟩ := fermat hp a
  rw [hq, add_comm, mod_add_mul a q hp.pos]

/-- **Fermat's little theorem** in the ring of differences: `ι p ∣ ι aᵖ − ι a`. -/
theorem fermat_ring {p : V} (hp : Irred p) (a : V) :
    (ι p : DiffRing V) ∣ ι (power a p) - ι a := by
  obtain ⟨q, hq⟩ := fermat hp a
  refine ⟨ι q, ?_⟩
  rw [hq, map_add, map_mul]
  ring

/-- **Cube roots modulo `p ≡ 2 (mod 3)`**: `b = a^(2m+1)` has `b³ ≡ a (mod p)`. -/
theorem cube_root_of_two_mod_three {p : V} (hp : Irred p) (m : V) (hm : p = 3 * m + 2)
    (a : V) : ∃ b, (b * b * b) % p = a % p := by
  refine ⟨power a (2 * m + 1), ?_⟩
  obtain ⟨q, hq⟩ := fermat hp a
  have hP : power a p = a * power a (3 * m + 1) := by
    rw [hm, show 3 * m + 2 = (3 * m + 1) + 1 by ring, power_succ]
  have hb : power a (2 * m + 1) * power a (2 * m + 1) * power a (2 * m + 1) =
      power a p * power a (3 * m + 1) := by
    rw [← power_add, ← power_add, ← power_add, hm]
    congr 1
    ring
  have hfin : power a (2 * m + 1) * power a (2 * m + 1) * power a (2 * m + 1) =
      a + p * (q * power a (3 * m + 1) + q) := by
    rw [hb]
    have h2 : power a p * power a (3 * m + 1) =
        (q * p + a) * power a (3 * m + 1) := by rw [hq]
    rw [h2, add_mul, ← hP, hq]
    ring
  rw [hfin, mod_add_mul' a _ hp.pos]

/-- **`−3` is a square modulo `p = 3m+1`, given a non-`m`-th-power witness.** If `0 < g < p` and
`p ∤ g^m − 1`, then `ω = g^m` is a root of `X² + X + 1` modulo `p` and `p ∣ (2ω+1)² + 3`. -/
theorem neg_three_square_of_witness {p : V} (hp : Irred p) (m : V) (hm : p = 3 * m + 1)
    (g : V) (hg0 : 0 < g) (hgp : g < p) (hw : ¬ p ∣ power g m - 1) :
    ∃ x, p ∣ x * x + 3 := by
  set ω := power g m with hωdef
  have hω1 : 1 ≤ ω := one_le_power g m (pos_iff_one_le.mp hg0)
  -- `g · (ω³ − 1) = q · p`
  obtain ⟨q, hq⟩ := fermat hp g
  have hω3 : power g p = g * (ω * ω * ω) := by
    rw [hm, power_succ, hωdef, ← power_add, ← power_add, show m + m + m = 3 * m by ring]
  have hc1 : 1 ≤ ω * ω * ω := one_le_mul (one_le_mul hω1 hω1) hω1
  have hdiv : p ∣ g * (ω * ω * ω - 1) := by
    refine ⟨q, ι_injective ?_⟩
    have e1 : ι (ω * ω * ω - 1) + 1 = (ι (ω * ω * ω) : DiffRing V) := by
      rw [← map_one (ι (V := V)), ← map_add, tsub_add_cancel_of_le hc1]
    have e2 := congrArg (ι (V := V)) (hω3.symm.trans hq)
    simp only [map_mul, map_add] at e1 e2 ⊢
    linear_combination ι g * e1 + e2
  have hpg : ¬ p ∣ g := not_dvd_of_pos_lt hg0 hgp
  have hcube : p ∣ ω * ω * ω - 1 := (hp.euclid hdiv).resolve_left hpg
  have hfac : ω * ω * ω - 1 = (ω - 1) * (ω * ω + ω + 1) := by
    apply ι_injective
    have e1 : ι (ω * ω * ω - 1) + 1 = (ι (ω * ω * ω) : DiffRing V) := by
      rw [← map_one (ι (V := V)), ← map_add, tsub_add_cancel_of_le hc1]
    have e2 : ι (ω - 1) + 1 = (ι ω : DiffRing V) := by
      rw [← map_one (ι (V := V)), ← map_add, tsub_add_cancel_of_le hω1]
    simp only [map_mul, map_add, map_one] at e1 e2 ⊢
    linear_combination e1 - (ι ω * ι ω + ι ω + 1) * e2
  rw [hfac] at hcube
  have hroot : p ∣ ω * ω + ω + 1 := (hp.euclid hcube).resolve_left hw
  refine ⟨2 * ω + 1, ?_⟩
  have hx : (2 * ω + 1) * (2 * ω + 1) + 3 = 4 * (ω * ω + ω + 1) := by ring
  rw [hx]
  exact Dvd.dvd.mul_left hroot 4

#print axioms dvd_binom
#print axioms fermat
#print axioms fermat_mod
#print axioms fermat_ring
#print axioms cube_root_of_two_mod_three
#print axioms neg_three_square_of_witness

end DiophantineConsistency.ModelFermat
