import DiophantineConsistency.ZRows.CoprimeSquares

/-! # `−3` is a square modulo every irreducible `p ≡ 1 (mod 3)`, in models of `𝗜𝚺₁`

`ModelFermat.neg_three_square_of_witness` reduces the claim to a witness `0 < g < p` with
`p ∤ g^m − 1`, `p = 3m + 1`. This module supplies the witness in every model `V` of `𝗜𝚺₁`,
through internal power sums instead of a root count for `X^m − 1`:

* `sumPow j N = Σ_{g<N} g^j` and `wsum J N I = Σ_{i<I} C(J, i)·sumPow i N` are primitive
  recursions with `𝚺₁` graphs;
* `wsum_total`: `Σ_{i≤j} C(j+1, i)·Σ_{g<N} g^i = N^{j+1}` (telescoping
  `(g+1)^{j+1} − g^{j+1}` through the internal binomial theorem, with the double sum exchanged
  by an induction on `N`);
* `sumPow_dvd`: for irreducible `p` and `1 ≤ j`, `j + 1 < p`, `p ∣ Σ_{g<p} g^j` (strong
  induction on `j`: the identity at `N = p` leaves `(j+1)·Σ g^j ≡ 0`);
* `exists_non_root`: if `1 ≤ m` and `m + 1 < p`, some `0 < g < p` has `p ∤ g^m − 1`, since
  otherwise `Σ_{g<p} g^m ≡ p − 1 ≢ 0`;
* `neg_three_square`: for irreducible `p = 3m + 1`, `p ∣ x² + 3` for some `x`;
* `cube_root_or_neg_three`: for irreducible `p ≠ 3`, every residue is a cube modulo `p`, or
  `−3` is a square modulo `p`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ZRowsRootWitness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing ArithmeticPow ArithmeticBinomPascal ArithmeticBinomExpansion
open ModelBoundedForallArith ModelBetaFunction ModelFermat ZRowsCoprimeSquares

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ι_tsub' {a b : V} (h : b ≤ a) : (ι (a - b) : DiffRing V) = ι a - ι b := by
  have e := congrArg (ι (V := V)) (tsub_add_cancel_of_le h)
  rw [map_add] at e
  linear_combination e

/-! ### Power sums -/

namespace SumPow
def zeroDef : 𝚺₁.Semisentence 2 := .mkSigma “out j. out=0”
def succDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index j. ∃ p, !powerDef p index j ∧ out=previous+p”
def blueprint : PR.Blueprint 1 where
  zero := zeroDef
  succ := succDef

noncomputable def construction : PR.Construction V blueprint where
  zero _ := 0
  succ parameters index previous := previous + power index (parameters 0)
  zero_defined := .mk fun e => by simp [blueprint, zeroDef]
  succ_defined := .mk fun e => by simp [blueprint, succDef]
end SumPow

/-- `sumPow j N = Σ_{g<N} g^j`. -/
noncomputable def sumPow (j N : V) : V := SumPow.construction.result ![j] N
def sumPowDef : 𝚺₁.Semisentence 3 := SumPow.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])
instance sumPow_defined : 𝚺₁-Function₂[V] sumPow via sumPowDef := .mk fun v ↦ by
  simp [SumPow.construction.result_defined_iff, sumPowDef, sumPow]; rfl
instance sumPow_definable : 𝚺₁-Function₂[V] sumPow := sumPow_defined.to_definable

@[simp] theorem sumPow_zero (j : V) : sumPow j 0 = 0 := by simp [sumPow, SumPow.construction]
theorem sumPow_succ (j N : V) : sumPow j (N + 1) = sumPow j N + power N j := by
  simp [sumPow, SumPow.construction]

theorem sumPow_zero_exp (N : V) : sumPow 0 N = N := by
  induction N using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ N ih => rw [sumPow_succ, ih, power_zero]

namespace WSum
def zeroDef : 𝚺₁.Semisentence 3 := .mkSigma “out J N. out=0”
def succDef : 𝚺₁.Semisentence 5 := .mkSigma
  “out previous index J N. ∃ b, !binomDef b J index ∧ ∃ s, !sumPowDef s index N ∧
    out=previous+b*s”
def blueprint : PR.Blueprint 2 where
  zero := zeroDef
  succ := succDef

noncomputable def construction : PR.Construction V blueprint where
  zero _ := 0
  succ parameters index previous :=
    previous + binom (parameters 0) index * sumPow index (parameters 1)
  zero_defined := .mk fun e => by simp [blueprint, zeroDef]
  succ_defined := .mk fun e => by simp [blueprint, succDef]
end WSum

/-- `wsum J N I = Σ_{i<I} C(J, i)·sumPow i N`. -/
noncomputable def wsum (J N I : V) : V := WSum.construction.result ![J, N] I
def wsumDef : 𝚺₁.Semisentence 4 := WSum.blueprint.resultDef |>.rew (Rew.subst ![#0, #3, #1, #2])
instance wsum_defined : 𝚺₁-Function₃[V] wsum via wsumDef := .mk fun v ↦ by
  simp [WSum.construction.result_defined_iff, wsumDef, wsum]
instance wsum_definable : 𝚺₁-Function₃[V] wsum := wsum_defined.to_definable

@[simp] theorem wsum_zero (J N : V) : wsum J N 0 = 0 := by simp [wsum, WSum.construction]
theorem wsum_succ (J N I : V) : wsum J N (I + 1) = wsum J N I + binom J I * sumPow I N := by
  simp [wsum, WSum.construction]

theorem wsum_zero_mid (J I : V) : wsum J 0 I = 0 := by
  induction I using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ I ih => rw [wsum_succ, ih, sumPow_zero, mul_zero, add_zero]

/-- Exchanging the double sum one row at a time. -/
theorem wsum_succ_mid (J N I : V) : wsum J (N + 1) I = wsum J N I + bsum N J I := by
  induction I using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ I ih =>
    rw [wsum_succ, ih, sumPow_succ, wsum_succ, bsum_succ]
    ring

/-- **The telescoped power-sum identity** `Σ_{i≤j} C(j+1, i)·Σ_{g<N} g^i = N^{j+1}`. -/
theorem wsum_total (j N : V) : wsum (j + 1) N (j + 1) = power N (j + 1) := by
  induction N using ISigma1.sigma1_succ_induction
  · definability
  case zero => rw [wsum_zero_mid, zero_power_of_pos _ (by simp)]
  case succ N ih =>
    rw [wsum_succ_mid, ih, binomial_theorem, bsum_succ N (j + 1) (j + 1), binom_self,
      one_mul, add_comm]

theorem binom_succ_self (n : V) : binom (n + 1) n = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => rw [binom_succ_succ, ih, binom_self]

/-- Divisibility cancels across a sum (through the ring of differences). -/
theorem dvd_of_dvd_add_left' {p a b : V} (h : p ∣ a + b) (ha : p ∣ a) : p ∣ b := by
  have h' : (ι p : DiffRing V) ∣ ι a + ι b := by rw [← map_add]; exact ι_dvd_iff.mpr h
  exact ι_dvd_iff.mp ((dvd_add_right (ι_dvd_iff.mpr ha)).mp h')

/-- **Power sums vanish**: `p ∣ Σ_{g<p} g^j` for `1 ≤ j` and `j + 1 < p`. -/
theorem sumPow_dvd {p : V} (hp : Irred p) (j : V) : 1 ≤ j → j + 1 < p → p ∣ sumPow j p := by
  induction j using ISigma1.sigma1_order_induction
  · definability
  case ind j ih =>
    intro hj1 hjp
    have hpart : ∀ I, I ≤ j → p ∣ wsum (j + 1) p I := by
      intro I
      induction I using ISigma1.sigma1_succ_induction
      · definability
      case zero => intro _; rw [wsum_zero]; exact dvd_zero p
      case succ I ihI =>
        intro hI
        have hIj : I < j := LO.FirstOrder.Arithmetic.succ_le_iff_lt.mp hI
        rw [wsum_succ]
        refine dvd_add (ihI hIj.le) (Dvd.dvd.mul_left ?_ _)
        rcases eq_or_ne I 0 with h0 | h0
        · rw [h0, sumPow_zero_exp]
        · exact ih I hIj (pos_iff_one_le.mp (pos_iff_ne_zero.mpr h0))
            (lt_of_le_of_lt hI (lt_trans (lt_add_one j) hjp))
    have htot := wsum_total j p
    rw [wsum_succ, binom_succ_self, power_succ] at htot
    have hsum : p ∣ wsum (j + 1) p j + (j + 1) * sumPow j p := by
      rw [htot]; exact dvd_mul_right p _
    have hprod : p ∣ (j + 1) * sumPow j p := dvd_of_dvd_add_left' hsum (hpart j le_rfl)
    exact (hp.euclid hprod).resolve_left
      (not_dvd_of_pos_lt (lt_of_le_of_lt (Arithmetic.zero_le j) (lt_add_one j)) hjp)

/-- If every `0 < g < N` has `p ∣ g^m − 1`, then `Σ_{g<N} g^m ≡ N − 1 (mod p)`. -/
theorem sumPow_mod_of_roots {p m : V} (hm : 1 ≤ m)
    (hall : ∀ g, 0 < g → g < p → p ∣ power g m - 1) (N : V) :
    1 ≤ N → N ≤ p → (sumPow m N + 1) % p = N % p := by
  induction N using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro h; exact absurd h (not_le.mpr _root_.zero_lt_one)
  case succ N ih =>
    intro _ hNp
    rcases eq_or_ne N 0 with h0 | h0
    · subst h0
      rw [sumPow_succ, sumPow_zero, zero_power_of_pos m (pos_iff_one_le.mpr hm)]
      simp
    · have hN0 : 0 < N := pos_iff_ne_zero.mpr h0
      have hNlt : N < p := LO.FirstOrder.Arithmetic.succ_le_iff_lt.mp hNp
      obtain ⟨q, hq⟩ := ringSub_of_mod_eq (ih (pos_iff_one_le.mp hN0) hNlt.le)
      obtain ⟨c, hc⟩ := hall N hN0 hNlt
      have hpow : (ι (power N m) : DiffRing V) = 1 + ι p * ι c := by
        rw [← map_mul, ← hc, ι_tsub' (one_le_power N m (pos_iff_one_le.mp hN0)), map_one]
        ring
      apply mod_eq_of_sub_eq (q := q + ι c)
      rw [sumPow_succ]
      simp only [map_add, map_one] at hq ⊢
      rw [hpow]
      linear_combination hq

/-- **A non-root of `X^m − 1` below `p`**, for `1 ≤ m` and `m + 1 < p`. -/
theorem exists_non_root {p : V} (hp : Irred p) (m : V) (hm : 1 ≤ m) (hmp : m + 1 < p) :
    ∃ g, 0 < g ∧ g < p ∧ ¬ p ∣ power g m - 1 := by
  by_contra hn
  have hall : ∀ g, 0 < g → g < p → p ∣ power g m - 1 := by
    intro g hg0 hgp
    by_contra hg
    exact hn ⟨g, hg0, hgp, hg⟩
  have h1 := sumPow_mod_of_roots hm hall p (pos_iff_one_le.mp hp.pos) le_rfl
  obtain ⟨k, hk⟩ := sumPow_dvd hp m hm hmp
  rw [hk, add_comm, mod_add_mul' 1 k hp.pos, mod_eq_self_of_lt hp.1, mod_self] at h1
  exact _root_.one_ne_zero h1

/-- **`−3` is a square modulo every irreducible `p = 3m + 1`.** -/
theorem neg_three_square {p : V} (hp : Irred p) (m : V) (hm : p = 3 * m + 1) :
    ∃ x, p ∣ x * x + 3 := by
  have hm1 : 1 ≤ m := by
    rcases eq_or_ne m 0 with h0 | h0
    · rw [h0, mul_zero, zero_add] at hm
      exact absurd hm (ne_of_gt hp.1)
    · exact pos_iff_one_le.mp (pos_iff_ne_zero.mpr h0)
  have hmp : m + 1 < p := by
    apply ι_lt_ι.mp
    have h1 : (1 : DiffRing V) ≤ ι m := by
      rw [← map_one (ι (V := V))]; exact ι_le_ι.mpr hm1
    rw [hm]
    simp only [map_add, map_mul, map_one, map_ofNat]
    linarith
  obtain ⟨g, hg0, hgp, hw⟩ := exists_non_root hp m hm1 hmp
  exact neg_three_square_of_witness hp m hm g hg0 hgp hw

/-- An irreducible `p` other than `3` is `3m + 1` or `3m + 2`. -/
theorem mod_three_cases {p : V} (hp : Irred p) (hp3 : p ≠ 3) :
    p = 3 * (p / 3) + 1 ∨ p = 3 * (p / 3) + 2 := by
  have h3 : (0 : V) < 3 := by simp
  have hlt : p % 3 ≤ 2 := by
    have h : p % 3 < 2 + 1 := by rw [two_add_one_eq_three]; exact mod_lt p h3
    exact LO.FirstOrder.Arithmetic.lt_succ_iff_le.mp h
  have hd := div_add_mod p 3
  rcases le_two_iff_eq_zero_or_one_or_two.mp hlt with h | h | h
  · exfalso
    have h3p : 3 ∣ p := mod_eq_zero_iff_dvd.mp h
    rcases hp.2 3 h3p with h1 | h1
    · have h31 := congrArg (ι (V := V)) h1
      simp only [map_ofNat, map_one] at h31
      norm_num at h31
    · exact hp3 h1.symm
  · left; rw [h] at hd; exact hd.symm
  · right; rw [h] at hd; exact hd.symm

/-- **Cube roots or `√−3`**: for irreducible `p ≠ 3`, every residue is a cube modulo `p`
(`p ≡ 2`), or `−3` is a square modulo `p` (`p ≡ 1`). -/
theorem cube_root_or_neg_three {p : V} (hp : Irred p) (hp3 : p ≠ 3) :
    (∀ a, ∃ b, (b * b * b) % p = a % p) ∨ ∃ x, p ∣ x * x + 3 := by
  rcases mod_three_cases hp hp3 with h | h
  · exact Or.inr (neg_three_square hp _ h)
  · exact Or.inl (cube_root_of_two_mod_three hp _ h)

#print axioms wsum_total
#print axioms sumPow_dvd
#print axioms exists_non_root
#print axioms neg_three_square
#print axioms cube_root_or_neg_three

end DiophantineConsistency.ZRowsRootWitness
