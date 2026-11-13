import DiophantineConsistency.P137.P137Front
import DiophantineConsistency.P138.P138EarlyFold
import DiophantineConsistency.ZRows.ReducedFraction

/-! # The weak front: unconditional facts and the recovery of the strong front

The registers are those of `P137Front.front p x`, shared by package 137's 648/115 equation and
package 135's 398/121 equation. In every model `V` of `𝗜𝚺₁`, for every point
`x : Fin 11 → DiffRing V` and every port tuple satisfying `P138Ports.PortFacts`:

* `q_mod_six`, `q_ne`, `X_mod`: the registers that do not read `v` are those of package 138, so
  the facts of `P138Bootstrap` hold verbatim;
* `A_even`, `A_ne`, `Delta_ge`, `Dm_ge`: with the weak `Y = v q` the size bound `|a| ≥ |q|³` of
  package 138 is not available (`v = 0` is a legitimate point). Instead `X ≡ 2 (mod 3)` gives
  `a = Y (1 + X) ≡ 0 (mod 3)`, so `A = a + 2 ≠ 0`; `A` is even, so `Delta = A² − 1 ≥ 3`;
* `Dt_facts`: `Dt ≥ 1`, `Dt ≡ 1 (mod 8)`;
* `Ac_ne`: the carrier value `Ac = (zc² + 3 Dcar²)(zc³ − 19 Dcar³)` is nonzero;
* `coprime_H_M`: `H = 3 + q u` is coprime to `M = 2 q²`, because `q ≡ 2 (mod 6)`.

**Recovery.** If `S ∣ Ac` (which every zero of either equation forces), then, since
`S = M⁵ H r s` and `Ac` is a monic quintic in `zc` whose lower coefficients carry the matching
powers of `M` (`P137Front.Ac_quintic`), the rational root theorem
(`ZRowsReducedFraction.dvd_of_pow5`) gives `M ∣ zc`; as `zc ≡ H (v − q²) (mod M)`:

* `recover`: `v = (1 + 2 v') q²` for some `v'`, i.e. the weak `Y = v q` *is* the strong
  `Y = q³ (2 v' + 1)` of package 138 at the point `Function.update x 5 v'`;
* `H_dvd_Kq5`: `H ∣ Kq⁵`, the projector divisibility of package 138's leaf chain;
* `Kq_transfer`: the projector register agrees with `P138EarlyFold.Kq` at the updated point. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P137Bootstrap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares ZRowsReducedFraction P137Front P138Ports

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section Front
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V)
local notation "𝓕" => front p x

/-! ## The registers that do not read `v` -/

theorem q_mod_six (hp : PortFacts p) : ∃ t : DiffRing V, (𝓕).q = 6 * t + 2 :=
  P138Bootstrap.q_mod_six p x 0 hp

theorem q_even (hp : PortFacts p) : ∃ t : DiffRing V, (𝓕).q = 2 * t :=
  P138Bootstrap.q_even p x 0 hp

theorem q_ne (hp : PortFacts p) : (𝓕).q ≠ 0 := P138Bootstrap.q_ne p x 0 hp

theorem abs_q_ge (hp : PortFacts p) : 2 ^ 64 ≤ |(𝓕).q| := P138Bootstrap.abs_q_ge p x 0 hp

theorem X_mod (hp : PortFacts p) :
    (∃ m : DiffRing V, (𝓕).X = 8 * m) ∧ ∃ m : DiffRing V, (𝓕).X = 3 * m + 2 :=
  P138Bootstrap.X_mod p x 0 hp

/-! ## `H`, `A`, `Delta`, `Dm`, `Dt` -/

theorem H_odd : ∃ m : DiffRing V, (𝓕).H = 2 * m + 1 := ⟨2 * (𝓕).a + 1, by rw [H_def]; ring⟩

theorem H_ne : (𝓕).H ≠ 0 := by
  obtain ⟨m, hm⟩ := H_odd p x; rw [hm]; exact P138Bootstrap.odd_ne_zero' m

/-- `a ≡ 0 (mod 3)`, from `X ≡ 2 (mod 3)`. -/
theorem a_mod_three (hp : PortFacts p) : ∃ n : DiffRing V, (𝓕).a = 3 * n := by
  obtain ⟨_, ⟨m, hm⟩⟩ := X_mod p x hp
  exact ⟨(𝓕).Y * (m + 1), by rw [a_eq, hm]; ring⟩

theorem A_even (hp : PortFacts p) : ∃ m : DiffRing V, (𝓕).A = 2 * m := by
  obtain ⟨t, ht⟩ := q_mod_six p x hp
  have ha := a_eq_q p x
  exact ⟨(3 * t + 1) * (x 5 * (1 + (𝓕).X)) + 1, by
    rw [A_def]; linear_combination ha + (x 5 * (1 + (𝓕).X)) * ht⟩

/-- `A = a + 2 ≡ 2 (mod 3)` does not vanish. -/
theorem A_ne (hp : PortFacts p) : (𝓕).A ≠ 0 := by
  obtain ⟨n, hn⟩ := a_mod_three p x hp
  rw [A_def, hn]
  intro h
  rcases P138Bootstrap.int_split n with h0 | h0 <;> linarith

theorem Delta_ge (hp : PortFacts p) : 3 ≤ (𝓕).Delta := by
  obtain ⟨m, hm⟩ := A_even p x hp
  have hm0 : m ≠ 0 := by intro h0; apply A_ne p x hp; rw [hm, h0, mul_zero]
  have h1 := P138Bootstrap.one_le_abs hm0
  have h2 : 1 ≤ m ^ 2 := by
    rw [← sq_abs]
    have := mul_le_mul h1 h1 (by norm_num) (abs_nonneg m)
    rw [sq]; linarith
  have e : (2 * m) ^ 2 = 4 * m ^ 2 := by ring
  rw [Delta_eq, hm, e]; linarith

theorem Dm_ge (hp : PortFacts p) : 1 ≤ (𝓕).Dm := by
  rw [Dm_eq]
  have := Delta_ge p x hp
  have : 0 ≤ (𝓕).Delta * x 8 ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  linarith

theorem Dt_facts (hp : PortFacts p) : 1 ≤ (𝓕).Dt ∧ ∃ m : DiffRing V, (𝓕).Dt = 8 * m + 1 := by
  obtain ⟨⟨m, hm⟩, _⟩ := X_mod p x hp
  have h0 := P138Bootstrap.mul_succ_nonneg ((𝓕).X * (𝓕).Y ^ 2)
  refine ⟨?_, ⟨m * (𝓕).Y ^ 2 * ((𝓕).X * (𝓕).Y ^ 2 + 1) * (𝓕).k ^ 2, ?_⟩⟩
  · rw [Dt_eq]; have := mul_nonneg h0 (sq_nonneg (𝓕).k); linarith
  · have hD := Dt_eq p x
    linear_combination hD + ((𝓕).Y ^ 2 * ((𝓕).X * (𝓕).Y ^ 2 + 1) * (𝓕).k ^ 2) * hm

/-! ## The carrier -/

theorem M_ne (hp : PortFacts p) : (𝓕).M ≠ 0 := by
  rw [M_eq]; exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (q_ne p x hp))

theorem Dcar_ne (hp : PortFacts p) : (𝓕).Dcar ≠ 0 := by
  rw [Dcar_def]; exact mul_ne_zero (H_ne p x) (M_ne p x hp)

/-- **`Ac ≠ 0`**: `19` is not a rational cube. -/
theorem Ac_ne (hp : PortFacts p) : (𝓕).Ac ≠ 0 := by
  rw [Ac_eq]
  have hD := Dcar_ne p x hp
  refine mul_ne_zero ?_ (sub_ne_zero.mpr (P138NoRoot.no_cube_19 hD))
  have : 0 < 3 * (𝓕).Dcar ^ 2 := by positivity
  have := sq_nonneg (𝓕).zc
  exact (show (0 : DiffRing V) < (𝓕).zc ^ 2 + 3 * (𝓕).Dcar ^ 2 by linarith).ne'

/-! ## Coprimality of `H` and `M` -/

theorem coprime_H_q (hp : PortFacts p) : IsCoprime (𝓕).H (𝓕).q := by
  obtain ⟨t, ht⟩ := q_mod_six p x hp
  have ha := a_eq_q p x
  have hH := H_def p x
  refine ⟨2 * t + 1, -(4 * (x 5 * (1 + (𝓕).X)) * (2 * t + 1) + 1), ?_⟩
  linear_combination (2 * t + 1) * hH + 4 * (2 * t + 1) * ha - ht

theorem coprime_H_two : IsCoprime (𝓕).H (2 : DiffRing V) :=
  ⟨1, -(2 * (𝓕).a + 1), by rw [H_def]; ring⟩

theorem coprime_H_M (hp : PortFacts p) : IsCoprime (𝓕).H (𝓕).M := by
  have hq := coprime_H_q p x hp
  rw [M_def, q2_def]
  exact (hq.mul_right hq).mul_right (coprime_H_two p x)

/-! ## Recovery of the strong front from `S ∣ Ac` -/

/-- The rational root theorem on the carrier quintic. -/
theorem M_dvd_zc (hp : PortFacts p) (hS : (𝓕).S ∣ (𝓕).Ac) : (𝓕).M ∣ (𝓕).zc := by
  have h5 : (𝓕).M ^ 5 ∣ (𝓕).Ac := dvd_trans ⟨_, S_eq p x⟩ hS
  rw [Ac_quintic] at h5
  exact dvd_of_pow5 (c3 := 3 * (𝓕).H ^ 2) (c2 := -(19 * (𝓕).H ^ 3)) (c0 := -(57 * (𝓕).H ^ 5))
    (M_ne p x hp) h5

/-- **Recovery of `v`**: `v = (1 + 2 v') q²`. -/
theorem recover (hp : PortFacts p) (hS : (𝓕).S ∣ (𝓕).Ac) :
    ∃ v' : DiffRing V, x 5 = (1 + v' * 2) * (𝓕).q2 := by
  obtain ⟨e, he⟩ := M_dvd_zc p x hp hS
  have hz := zc_eq p x
  have h1 : (𝓕).M ∣ (𝓕).H * (x 5 - (𝓕).q2) :=
    ⟨e - (x 7 * (𝓕).H + (𝓕).K), by linear_combination he - hz⟩
  obtain ⟨v', hv'⟩ := dvd_of_dvd_mul_coprime (coprime_H_M p x hp) h1
  have hM := M_def p x
  exact ⟨v', by linear_combination hv' + v' * hM⟩

/-- **`H ∣ Kq⁵` from `S ∣ Ac`.** -/
theorem H_dvd_Kq5 (hp : PortFacts p) (hS : (𝓕).S ∣ (𝓕).Ac) : (𝓕).H ∣ Kq p x ^ 5 := by
  have hHS : (𝓕).H ∣ (𝓕).S := ⟨(𝓕).M ^ 5 * (x 4 * x 10), by rw [S_eq]; ring⟩
  have hHAc : (𝓕).H ∣ (𝓕).Ac := dvd_trans hHS hS
  have h1 : (𝓕).H ∣ (𝓕).Ac - (𝓕).zc ^ 5 :=
    ⟨3 * (𝓕).H * (𝓕).M ^ 2 * (𝓕).zc ^ 3 - 19 * (𝓕).H ^ 2 * (𝓕).M ^ 3 * (𝓕).zc ^ 2 -
      57 * (𝓕).H ^ 4 * (𝓕).M ^ 5, by rw [Ac_quintic]; ring⟩
  have h2 : (𝓕).H ∣ (𝓕).zc ^ 5 - ((𝓕).K * (𝓕).M) ^ 5 :=
    dvd_trans (show (𝓕).H ∣ (𝓕).zc - (𝓕).K * (𝓕).M from
      ⟨(𝓕).M * x 7 + (x 5 - (𝓕).q2), by rw [zc_eq]; ring⟩) (sub_dvd_pow_sub_pow _ _ 5)
  have h3 : (𝓕).H ∣ ((𝓕).K * (𝓕).M) ^ 5 - (-2 * Kq p x * (𝓕).M) ^ 5 :=
    dvd_trans (show (𝓕).H ∣ (𝓕).K * (𝓕).M - -2 * Kq p x * (𝓕).M from
      ⟨(𝓕).X * x 8 * (𝓕).M, by rw [K_Kq]; ring⟩) (sub_dvd_pow_sub_pow _ _ 5)
  have h4 : (𝓕).H ∣ Kq p x ^ 5 * (2 * (𝓕).M) ^ 5 := by
    have e : Kq p x ^ 5 * (2 * (𝓕).M) ^ 5 =
        -(((𝓕).Ac - (((𝓕).Ac - (𝓕).zc ^ 5) + ((𝓕).zc ^ 5 - ((𝓕).K * (𝓕).M) ^ 5))) -
          (((𝓕).K * (𝓕).M) ^ 5 - (-2 * Kq p x * (𝓕).M) ^ 5)) := by ring
    rw [e]
    exact (dvd_sub (dvd_sub hHAc (dvd_add h1 h2)) h3).neg_right
  have hc : IsCoprime (𝓕).H ((2 * (𝓕).M) ^ 5) :=
    ((coprime_H_two p x).mul_right (coprime_H_M p x hp)).pow_right
  exact hc.dvd_of_dvd_mul_right h4

end Front

/-! ## The projector register at the recovered point -/

section Transfer
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V) (v' : DiffRing V)

theorem Kq_transfer (hv : x 5 = (1 + v' * 2) * (front p x).q2) (κ : DiffRing V) :
    P138EarlyFold.Kq p (Function.update x 5 v') κ = Kq p x := by
  unfold P138EarlyFold.Kq P137Front.Kq
  rw [tr_X, tr_a p x v' hv, upd_8]

end Transfer

#print axioms A_ne
#print axioms Delta_ge
#print axioms Dt_facts
#print axioms Ac_ne
#print axioms coprime_H_M
#print axioms recover
#print axioms H_dvd_Kq5
#print axioms Kq_transfer

end DiophantineConsistency.P137Bootstrap
