import Lib.PadicHodge.Kisin.PeriodMatrixBasis

/-!
# The radius lemma: after Frobenius a frame is a constant basis times a unit over A

The radius lemma for a chart (`New.Lift.Chart`): a subring S of A_inf, the image of Λ⟦X⟧, where
Λ = W(𝔽_{p^𝔣}) are the constants; the image z of X is a Teichmüller lift, and E = z^e·(unit) + p is
an associate of ξ. Further A = `New.Period.Amax`, B⁺ = A[1/p] = `New.Period.BPlus`, φ is the
Frobenius, and t is a Galois element with `c.FixesThetaZ t`.

* `New.Lift.Chart.exists_E_pow_mul_eq_tau_pow_mul_iff`: A_inf[1/τ] ∩ S_B[1/E] = S.
* `New.Lift.Chart.tau_mul_z_dvd_smul_sub`: τz divides ty − y in B⁺ for every y in S_B.
* `New.Lift.Chart.radius_lemma`: if tz = [ε]z, Z has entries in S_B with Z'·Z = E^h and tZ = Z·G for
  some G over A_inf, and 3e ≤ p^l, then φ^l(Z) = φ^l(E)^b·C·V with C constant and V invertible over
  A (`New.Lift.Chart.IsRadiusFactorization`).

Notions from other files:
* `New.Period.tau`, `New.Period.mu`, `New.Period.xi`: the elements τ = [ε^{1/p}] − 1, μ = [ε] − 1
  and ξ of A_inf, with ξτ = μ; `New.Period.theta` is Fontaine's map θ : A_inf → O_C.
* `New.Lift.Chart.ainfToBPlus`: the structure ring homomorphism from A_inf to B⁺.
* `New.Lift.Chart.bicommutant`: the S-subalgebra S_B of the y in B⁺ whose multiplication commutes
  with every S-linear endomorphism of B⁺ that preserves the image of A. It contains p⁻¹ and is the
  p-adic closure of S[E/p] with p inverted (`New.Lift.Chart.adjoinEDivPClosure_eq_bicommutant`).
* `New.Lift.Chart.FixesThetaZ`: `c.FixesThetaZ t` says that t fixes the constants Λ and θ(z).

## Relation to the literature

Known result: Dwork's trick, giving an integral crystalline comparison with a uniform denominator.
Here `radius_lemma` gives φ^l(Z) = φ^l(E)^b·C·V, with C fixed by every g that fixes Λ and V
invertible over A_max. Whenever e·A ≤ p^l·δ, the y with Vy natural modulo E^A span at least
p^{4δ}S^d.
Source: M. Kisin, Crystalline representations and F-crystals, Progr. Math. 253 (2006), Lemma 1.2.6;
M. Kisin, Potentially semi-stable deformation rings, JAMS 21 (2008), Lemma 2.2; B. Bhatt,
P. Scholze, Prismatic F-crystals and crystalline Galois representations (2023), proof of Thm 5.6.

See also `Lib.PadicHodge.Kisin.PeriodMatrixFrame`.
-/

namespace New.Lift.Chart

open Period BPlus Matrix Algebra PowerSeries WittVector Ideal Function NeZero RingHom Finset Nat

variable {p : ℕ} [ThePrime p] {c : Chart} {d : Type} [Fintype d] [DecidableEq d] {t : Gp p}

/-- `E` divides `xi - p * b` for some `b` in `Ainf` (for `b = 0`, as `E` and `xi` are
associates). -/
private lemma exists_E_dvd_xi_sub_p_mul : ∃ b : Ainf, c.E.val ∣ xi - p * b :=
  ⟨0, by simp [associated_E_xi, Associated.dvd]⟩

/-- The identity `n - v_p(n!) + 2 = (n + 1 - v_p((n + 1)!)) + v_p(n + 1) + 1` of `p`-adic
valuations, from `v_p((n + 1)!) = v_p(n + 1) + v_p(n!)` and `v_p((n + 1)!) ≤ n + 1`. -/
private lemma sub_padicValNat_factorial_add_two_eq (n : ℕ) :
    n - padicValNat p n ! + 2 = n + 1 - padicValNat p (n + 1)! + padicValNat p (n + 1) + 1 := by
  grind [padicValNat_factorial_le, factorial, padicValNat.mul]

private lemma coe_z_eq_seriesMap_X : (c.z : Ainf) = c.seriesMap X := rfl

/-- If `tau` divides `E ^ h * a` in `BPlus`, for `a` in `Ainf`, then `tau` divides `a` in
`Ainf`. -/
lemma tau_dvd_of_dvd_E_pow_mul {h : ℕ} {a : Ainf}
    (h_dvd : ainfToBPlus tau ∣ ainfToBPlus (c.E ^ h * a)) : tau ∣ a :=
  c.dvd_of_dvd_E_pow_mul not_p_dvd_tau exists_tau_dvd_xi_sub_p_mul theta_tau_ne_zero h_dvd

/-- Let `c` be a chart with z = `c.z` and E = `c.E` (the image in A_inf of the series
X^e·(unit) + p, ξ times a unit), and let τ = [ε^{1/p}] − 1. If τ^m·z^n divides E^h·a in `BPlus`,
for a in `Ainf`, then τ^m·z^n divides a in `Ainf`. -/
lemma tau_pow_mul_z_pow_dvd_of_dvd_E_pow_mul {m n h : ℕ} {a : Ainf}
    (h_dvd : ainfToBPlus (tau ^ m * c.z ^ n) ∣ ainfToBPlus (c.E ^ h * a)) :
    tau ^ m * c.z ^ n ∣ a := by
  -- Remove the factors `tau` one at a time, cancel `tau ^ m` in the domain `BPlus`, and remove
  -- the factors `c.z` one at a time.
  obtain ⟨b, rfl⟩ : tau ^ m ∣ a := by
    refine pow_dvd_of_map (T := fun x ↦ ainfToBPlus (c.E ^ h * x)) (ϖ := ainfToBPlus tau)
      ?_ ?_ (fun _ ↦ tau_dvd_of_dvd_E_pow_mul) ?_
    · simp [mul_left_comm]
    · simp
    · rw [← map_pow]
      exact (map_dvd ainfToBPlus (dvd_mul_right _ _)).trans h_dvd
  refine mul_dvd_mul_left _ (pow_dvd_of_map (T := fun x ↦ ainfToBPlus (c.E ^ h * x))
    (ϖ := ainfToBPlus c.z) ?_ ?_ (fun _ ↦ c.z_dvd_of_dvd_E_pow_mul) ?_)
  · simp [mul_left_comm]
  · simp [ne_zero_of_map c.theta_z_ne_zero]
  · simpa [mul_left_comm, mul_dvd_mul_iff_left, -isUnit_map_iff] using h_dvd

/-- If `tau * z ^ n` divides `E ^ h * a` in `BPlus`, for `a` in `Ainf`, then it divides `a`
in `Ainf`. -/
lemma tau_mul_z_pow_dvd_of_dvd_E_pow_mul {n h : ℕ} {a : Ainf}
    (h_dvd : ainfToBPlus (tau * c.z ^ n) ∣ ainfToBPlus (c.E ^ h * a)) : tau * c.z ^ n ∣ a := by
  rw [← pow_one tau] at h_dvd ⊢
  exact tau_pow_mul_z_pow_dvd_of_dvd_E_pow_mul h_dvd

/-- Let `tau` be the element τ = [ε^{1/p}] − 1 of `Ainf` = W(O^♭), the Witt vectors of the tilt of
O_{C_p}. Let `c` be a chart, with the image `c.S` of Λ⟦X⟧ in `Ainf`, and let `c.E` be its element
of `c.S` that is ξ times a unit, seen in `Ainf`. If the image of `tau ^ m` under the structure map
`ainfToBPlus : Ainf → BPlus` divides the image of `c.E ^ h * a`, for some `a` in `Ainf`, then
`tau ^ m` already divides `a` in `Ainf`. -/
lemma tau_pow_dvd_of_dvd_E_pow_mul {m h : ℕ} {a : Ainf}
    (h_dvd : ainfToBPlus (tau ^ m) ∣ ainfToBPlus (c.E ^ h * a)) : tau ^ m ∣ a := by
  rw [← mul_one (tau ^ m), ← pow_zero (c.z : Ainf)] at h_dvd ⊢
  exact tau_pow_mul_z_pow_dvd_of_dvd_E_pow_mul h_dvd

/-- Let `c` be a chart with ring S = `c.S` (the image of Λ⟦X⟧ in A_inf), E = `c.E` and
S_B = `c.bicommutant` (the p-adic closure of S[E/p] in `BPlus`, with p inverted). If E^h·a lies in
S_B, for a in `Ainf`, then a lies in S. -/
lemma mem_S_of_E_pow_mul_mem_bicommutant {h : ℕ} {a : Ainf}
    (h_mem : ainfToBPlus (c.E ^ h * a) ∈ c.bicommutant) : a ∈ c.S := by
  -- Cancel `E ^ h` in `S_B`; the projection onto `S_B` then fixes `a` and sends it into `S`.
  have hE_ne : ainfToBPlus c.E ^ h ≠ 0 := by simp [c.E_ne_zero']
  have ha_mem : ainfToBPlus a ∈ c.bicommutant :=
    c.mem_bicommutant_of_mul (pow_mem (ainfToBPlus_mem_bicommutant c.E) h) hE_ne
      (by simpa using h_mem)
  have h_coord : ainfToBPlus (c.adicBasis.coord c.oneIndex a) = ainfToBPlus a :=
    (c.extendToBPlus_ainfToBPlus _ a).symm.trans (c.extendedCoord_oneIndex_eq_self ha_mem)
  rw [← FaithfulSMul.algebraMap_injective Ainf BPlus h_coord]
  exact (c.adicBasis.coord c.oneIndex a).property

/-- The equality A_inf[1/τ] ∩ S_B[1/E] = S, with denominators cleared. Let `c` be a chart with ring
S = `c.S` (the image of Λ⟦X⟧ in A_inf), E = `c.E` and S_B = `c.bicommutant` (the p-adic closure of
S[E/p] in `BPlus`, with p inverted), and let τ = [ε^{1/p}] − 1. For a in `Ainf`, the fraction a/τ^m
equals y/E^h for some h and some y in S_B if and only if a = τ^m·s for some s in S. -/
theorem exists_E_pow_mul_eq_tau_pow_mul_iff {m : ℕ} {a : Ainf} :
    (∃ h : ℕ, ∃ y ∈ c.bicommutant, ainfToBPlus (c.E ^ h * a) = ainfToBPlus (tau ^ m) * y) ↔
      ∃ s : c.S, a = tau ^ m * s := by
  refine ⟨fun ⟨h, y, hy_mem, h_eq⟩ ↦ ?_, fun ⟨s, hs⟩ ↦
    ⟨0, ainfToBPlus s, ainfToBPlus_mem_bicommutant s, by simp [hs]⟩⟩
  -- The fraction `a / tau ^ m` is an element `b` of `Ainf`, and `E ^ h * b = y` lies in `S_B`.
  obtain ⟨b, rfl⟩ : tau ^ m ∣ a := tau_pow_dvd_of_dvd_E_pow_mul ⟨y, h_eq⟩
  have h_quotient : ainfToBPlus (c.E ^ h * b) = y := by
    rw [mul_left_comm, map_mul] at h_eq
    exact mul_left_cancel₀ (by simp) h_eq
  have hb_mem : b ∈ c.S := mem_S_of_E_pow_mul_mem_bicommutant (h := h) (by rwa [h_quotient])
  exact ⟨⟨b, hb_mem⟩, rfl⟩

/-- `φ ^ l` on `BPlus` restricts on `S` to the Frobenius `c.φ ^ l` of the chart. -/
lemma frobEnd_pow_ainfToBPlus (l : ℕ) (s : c.S) :
    (frobEnd ^ l) (ainfToBPlus s.val) = ainfToBPlus ((c.φ ^ l) s).val := by
  rw [coe_phi_pow, coe_pow, iterate_frobEnd_algebraMap]

/-- `φ ^ l` raises `z`, a Teichmüller lift, to the power `p ^ l`. -/
@[simp]
lemma frobEnd_pow_ainfToBPlus_z (l : ℕ) :
    (frobEnd ^ l) (ainfToBPlus c.z) = ainfToBPlus c.z ^ p ^ l := by
  simp [coe_pow, z_eq_teichmuller]

/-! ### The action of t and the radius lemma -/

/-- Let `c` be a chart with z = `c.z` and S_B = `c.bicommutant`, let τ = [ε^{1/p}] − 1, and let
t ∈ G_p fix Λ and θ(z) (`c.FixesThetaZ t`). Then τ·z divides t•y − y in `BPlus` for every y in
S_B. -/
lemma tau_mul_z_dvd_smul_sub (ht_fixes : c.FixesThetaZ t) {y : BPlus} (hy : y ∈ c.bicommutant) :
    ainfToBPlus (tau * c.z) ∣ t • y - y := by
  -- Write `t • y - y = z * b`; it remains to see `tau ∣ b`, which is tested by `θ ∘ φ ^ (i + 1)`.
  obtain ⟨b, hb⟩ : ainfToBPlus c.z ∣ t • y - y := c.z_dvd_sub ht_fixes.left hy
  have tau_dvd_b : ainfToBPlus tau ∣ b := by
    refine dvd_of_thetaBPlus_frobEnd_eq_zero b tau_dvd_of_theta_frobEnd fun i ↦ ?_
    -- Up to a power of `p`, `φ ^ (i + 1) y` lies in `S + E * S_B`; `θ` kills `E`, and `t` fixes
    -- `θ S`.
    have h_theta_eq_zero : thetaBPlus (frobEnd^[i + 1] (t • y - y)) = 0 := by
      -- Stated with `algebraMap`, the form that `hs` uses.
      obtain ⟨k, a, ha⟩ : ∃ k : ℕ, ∃ a : Amax, p ^ k * frobEnd^[i + 1] y = algebraMap _ BPlus a :=
        exists_p_pow_mul_eq_amax
      obtain ⟨s, v, -, hs⟩ :=
        c.exists_pow_mul_extendedCoord_eq_add c.E c.exists_E_dvd_xi_sub_p_mul a 1
      have h_iterate_mem : frobEnd^[i + 1] y ∈ c.bicommutant :=
        Set.MapsTo.iterate (fun _ ↦ c.frobEnd_mem_bicommutant) _ hy
      rw [← ha, map_p_pow_mul, c.extendedCoord_oneIndex_eq_self h_iterate_mem] at hs
      -- Apply `x ↦ θ (t • x - x)` to `p ^ (k + 1) * φ ^ (i + 1) y = s + E * v`.
      simpa [c.smul_theta_of_fixesThetaZ ht_fixes, NeZero.ne, theta_E, sub_eq_zero,
        ← Commute.iterate_right (smul_frobEnd t) _ _] using
          congrArg (fun x : BPlus ↦ thetaBPlus (t • x - x)) hs
    -- The factor `θ (φ ^ (i + 1) z)` is a power of `θ z ≠ 0`.
    have h_untilt : PreTilt.untilt c.varpiFlat ≠ 0 := by
      simpa [z_eq_teichmuller] using c.theta_z_ne_zero
    simpa [hb, z_eq_teichmuller, h_untilt] using h_theta_eq_zero
  grw [hb, map_mul, mul_comm, tau_dvd_b]

/-- `p` divides `xi`, hence `E` and `z ^ e`, in `Amax`; so `p ^ n` divides `z ^ N` there for
`e * n ≤ N`. -/
lemma exists_z_pow_eq {n N : ℕ} (h_le : c.e * n ≤ N) :
    ∃ y : Amax, ainfToBPlus c.z ^ N = p ^ n * algebraMap Amax BPlus y := by
  -- `xi = p * Amax.xiDivP` in `Amax`, and `xi` divides the image of `z ^ e * (unit) + p`.
  have h_p_dvd_xi : (p : Amax) ∣ algebraMap Ainf Amax xi := ⟨Amax.xiDivP, p_mul_X.symm⟩
  have p_dvd : (p : Amax) ∣ algebraMap Ainf Amax c.z ^ c.e := by
    simpa [(c.unitSeries.isUnit.map _).map, ← coe_z_eq_seriesMap_X] using
      h_p_dvd_xi.trans (map_dvd (algebraMap Ainf Amax) c.associated_xi.dvd')
  obtain ⟨y, hy⟩ : (p : Amax) ^ n ∣ algebraMap Ainf Amax c.z ^ N := by grw [p_dvd, ← pow_mul, h_le]
  exact ⟨y, by simpa [← IsScalarTower.algebraMap_apply] using congrArg (algebraMap Amax BPlus) hy⟩

/-- Truncation of a power series at order `D`, evaluated at `X = z ^ N / p ^ 2`: after clearing the
denominator `p ^ (2 * D)` the truncation lies in `S` and the tail is a multiple of `z ^ (N * D)`. -/
lemma exists_p_pow_mul_ev_eq_add_z_pow_mul {N : ℕ} {ev : c.S⟦X⟧ →ₐ[c.S] BPlus}
    (hX : ainfToBPlus c.z ^ N = p ^ 2 * ev X) (D : ℕ) (G : c.S⟦X⟧) :
    ∃ s : c.S, ∃ G' : c.S⟦X⟧,
      p ^ (2 * D) * ev G = ainfToBPlus s + ainfToBPlus c.z ^ (N * D) * ev G' := by
  induction D with
  | zero => exact ⟨0, G, by simp⟩
  | succ D ih =>
    -- Move the constant term of `G'` into `s`; the factor `p ^ 2` turns `ev X` into `z ^ N`.
    obtain ⟨s, G', hs⟩ := ih
    refine ⟨p ^ 2 * (s + constantCoeff G' * c.z ^ (N * D)), .mk fun i ↦ coeff (i + 1) G', ?_⟩
    rw [G'.eq_X_mul_shift_add_const] at hs
    linear_combination (norm :=
      (simp [pow_mul, hX, C_eq_algebraMap, Subalgebra.algebraMap_def, sub_eq_zero]
       ring) ) p ^ 2 * hs

/-- Values of `ev` at `X = z ^ N / p ^ 2` are fixed by the projection onto `S_B`. -/
lemma extendedCoord_oneIndex_ev {N : ℕ} (hN : 0 < N) {ev : c.S⟦X⟧ →ₐ[c.S] BPlus}
    (hX : ainfToBPlus c.z ^ N = p ^ 2 * ev X) (G : c.S⟦X⟧) :
    c.extendedCoord c.oneIndex (ev G) = ev G := by
  -- The projection fixes the truncations, so the difference is divisible by every power of `z`.
  refine sub_eq_zero.mp (c.eq_zero_of_z_pow_dvd fun n ↦ ?_)
  obtain ⟨s, G', hs⟩ := exists_p_pow_mul_ev_eq_add_z_pow_mul hX n G
  grw [Nat.le_mul_of_pos_left n hN, ← (isUnit_p.pow (2 * n)).dvd_mul_left]
  simp [mul_sub, ← map_p_pow_mul, hs, _root_.dvd_sub, extendedCoord_oneIndex_eq_self, pow_mem,
    extendToBPlus_mul]

/-- The vectors `y` over `S` for which `M y` is congruent modulo `E ^ A` to a vector with entries
in `ℕ`. -/
def natCongruentSet (c : Chart) (M : Matrix d d BPlus) (A : ℕ) : Set (d → c.S) :=
  {y : d → c.S |
    ∃ r : d → ℕ, ∀ i : d, ainfToBPlus c.E ^ A ∣ (M *ᵥ fun k : d ↦ ainfToBPlus (y k)) i - r i}

omit [DecidableEq d] in
lemma mem_natCongruentSet {M : Matrix d d BPlus} {A : ℕ} {y : d → c.S} :
    y ∈ natCongruentSet c M A ↔
      ∃ r : d → ℕ, ∀ i : d, ainfToBPlus c.E ^ A ∣ (M *ᵥ fun k : d ↦ ainfToBPlus (y k)) i - r i :=
  Iff.rfl

/-- Let `ev` evaluate at `X = z ^ N / p ^ 2` with values in `Amax`, and let `V` be a unit over
`S⟦X⟧`. For `e * A ≤ N * δ`, the `y` with `ev V y` congruent to a vector in `ℕ ^ d` modulo `E ^ A`
span a submodule that contains `p ^ (4 * δ) • S ^ d`. -/
lemma pow_smul_mem_span_of_unit {N : ℕ} (hN : 0 < N) {ev₀ : c.S⟦X⟧ →ₐ[c.S] Amax}
    {ev : c.S⟦X⟧ →ₐ[c.S] BPlus} (h_ev : ∀ G : c.S⟦X⟧, ev G = algebraMap Amax BPlus (ev₀ G))
    (hX : ainfToBPlus c.z ^ N = p ^ 2 * ev X) (V : (Matrix d d c.S⟦X⟧)ˣ) {A δ : ℕ}
    (h_le : c.e * A ≤ N * δ) (x : d → c.S) :
    p ^ (4 * δ) • x ∈ Submodule.span c.S (natCongruentSet c (V.val.map ev) A) := by
  -- Modulo `E ^ A`, each `p ^ (2 * δ) * ev G` is congruent to an element `s G` of `S`: the tail of
  -- the truncation lies in `p ^ A * Amax` and is fixed by the projection, and `p ^ A` times the
  -- projection of an element of `Amax` lies in `S + E ^ A * S_B`
  -- (`exists_pow_mul_extendedCoord_eq_add`).
  have h_approx (G : c.S⟦X⟧) :
      ∃ s : c.S, ainfToBPlus c.E ^ A ∣ ainfToBPlus s - p ^ (2 * δ) * ev G := by
    obtain ⟨y, hy⟩ := exists_z_pow_eq h_le
    obtain ⟨s, G', hs⟩ := exists_p_pow_mul_ev_eq_add_z_pow_mul hX δ G
    obtain ⟨a, w, -, ha⟩ :=
      c.exists_pow_mul_extendedCoord_eq_add c.E c.exists_E_dvd_xi_sub_p_mul (y * ev₀ G') A
    have h_tail : ainfToBPlus c.z ^ (N * δ) * ev G' = ainfToBPlus a + ainfToBPlus c.E ^ A * w := by
      rw [← extendedCoord_oneIndex_ev hN hX G', ← c.extendToBPlus_mul _ (by simp [pow_mem]), hy]
      simpa [mul_assoc, map_p_pow_mul, h_ev] using ha
    exact ⟨s + a, by simp [hs, h_tail]⟩
  choose s hs using h_approx
  refine Submodule.mem_span.mpr fun L hL ↦ ?_
  simp_rw [natCongruentSet, ← mem_span_singleton, ← Ideal.Quotient.eq] at hs hL
  -- `f` evaluates matrices modulo `E ^ A`, and `g` reduces matrices over `S`.
  let f : Matrix d d (c.S)⟦X⟧ →+* Matrix d d (BPlus ⧸ span {ainfToBPlus c.E ^ A}) :=
    ((Ideal.Quotient.mk (span {ainfToBPlus c.E ^ A})).comp ev.toRingHom).mapMatrix (m := d)
  let g : Matrix d d c.S →+* Matrix d d (BPlus ⧸ span {ainfToBPlus c.E ^ A}) := f.comp C.mapMatrix
  have g_map (F : Matrix d d c.S⟦X⟧) : g (F.map s) = p ^ (2 * δ) • f F := by
    ext i j
    simpa [f, g, C_eq_algebraMap, Subalgebra.algebraMap_def] using hs (F i j)
  -- If `V * M` is congruent to a scalar in `ℕ`, the columns of `M` are among the generators.
  have mem_of_scalar (M : Matrix d d c.S) (r : ℕ) (h_scalar : f V * g M = r) (y : d → c.S) :
      M *ᵥ y ∈ L := by
    have h_cols : Set.range M.col ⊆ (L : Set (d → c.S)) := by
      refine Set.range_subset_iff.mpr fun k ↦ hL ⟨col (r : Matrix d d ℕ) k, fun i ↦ ?_⟩
      simpa [f, g, mul_apply, mulVec, dotProduct, Matrix.natCast_apply, apply_ite,
        C_eq_algebraMap, Subalgebra.algebraMap_def] using congrFun₂ h_scalar i k
    exact (range_mulVecLin M).trans_le (L.span_le.mpr h_cols) ⟨y, rfl⟩
  -- `M` and `M'` approximate `p ^ (2 * δ) • V⁻¹` and `p ^ (2 * δ) • V`, so `V * M ≡ p ^ (2 * δ)`
  -- and `V * (p ^ (4 * δ) - M * M') ≡ 0`; `p ^ (4 * δ) • x` is a combination of the columns of
  -- `M` and of `p ^ (4 * δ) - M * M'`.
  let M : Matrix d d c.S := V⁻¹.val.map s
  let M' : Matrix d d c.S := V.val.map s
  have hM : f V * g M = (p ^ (2 * δ) : ℕ) := by
    -- Without `-nsmul_eq_mul` simp loops (maximum recursion depth); the scalar stays as in `g_map`.
    simp [M, g_map, ← f.map_mul, -nsmul_eq_mul, ← nsmul_one]
  have hMM' : f V * g (p ^ (4 * δ) • 1 - M * M') = (0 : ℕ) := by
    simp [M, M', g_map, ← f.map_mul, -nsmul_eq_mul, ← nsmul_one, smul_smul, ← pow_add,
      ← add_mul]
  have h_smul_eq_add : p ^ (4 * δ) • x = (p ^ (4 * δ) • 1 - M * M') *ᵥ x + M *ᵥ M' *ᵥ x := by
    rw [sub_mulVec, smul_mulVec, one_mulVec, mulVec_mulVec, sub_add_cancel]
  rw [h_smul_eq_add]
  exact add_mem (mem_of_scalar _ 0 hMM' x) (mem_of_scalar M _ hM _)

/-- One step of the radius lemma. Let `c` be a chart with z = `c.z`, S = `c.S` and
S_B = `c.bicommutant`, and let t ∈ G_p fix Λ and θ(z) (`c.FixesThetaZ t`) with t•z = [ε]z. Let Y
over B⁺ and G over A_inf satisfy t•Y = YG with τ·z dividing every entry of G − 1
(τ = [ε^{1/p}] − 1), fix a row index i, q, n ∈ ℕ and a row W over S_B, and suppose q•Y_i − z^{n+1}·W
is the image of a row over A_inf. Then each entry p^{v+1}·W_j lies in S + z·S_B, where v is the
p-adic valuation of n + 1. -/
lemma exists_ainfToBPlus_eq_p_pow_mul_sub_z_mul (ht_fixes : c.FixesThetaZ t)
    (ht_z : t • c.z.val = teichmuller p epsTilt * c.z.val)
    {G : Matrix d d Ainf} {Y : Matrix d d BPlus} (hY : t • Y = Y * G.map ainfToBPlus)
    (hG : ∀ i j : d, tau * c.z ∣ (G - 1) i j) {i : d} {n q : ℕ} {A : d → Ainf} {W : d → BPlus}
    (hW : ∀ j : d, W j ∈ c.bicommutant)
    (hA : ∀ j : d, ainfToBPlus (A j) = q • Y i j - ainfToBPlus c.z ^ (n + 1) * W j) (j : d) :
    ∃ s : c.S, ∃ W' ∈ c.bicommutant,
      ainfToBPlus s = p ^ (padicValNat p (n + 1) + 1) * W j - ainfToBPlus c.z * W' := by
  set v : ℕ := padicValNat p (n + 1)
  -- Lifting the exponent for `[ε]`.
  obtain ⟨α, β, hα⟩ :
      ∃ α β : Ainf, tau * c.E * (p ^ v + β * c.z) = α * (teichmuller p epsTilt ^ (n + 1) - 1) :=
    c.exists_tau_mul_E_eq_mul_epsTilt_pow_sub_one n.succ_ne_zero
  obtain ⟨r, hr⟩ : c.z ∣ c.E - p := c.z_dvd_E_sub_p
  -- Both `G - 1` and `t • W - W` are divisible by `tau * z`.
  obtain ⟨D, hD⟩ : ainfToBPlus (tau * c.z) ∣
      ∑ l : d, W l * ainfToBPlus ((G - 1) l j) - ainfToBPlus (mu + 1) ^ (n + 1) * (t • W j - W j) :=
    (univ.dvd_sum fun l _ ↦ (map_dvd ainfToBPlus (hG l j)).mul_left (W l)).sub
      ((tau_mul_z_dvd_smul_sub ht_fixes (hW j)).mul_left _)
  -- In `A * G - t • A` the terms in `Y` cancel. What is left is `z ^ (n + 1)` times
  -- `([ε] ^ (n + 1) - 1) * W j - tau * z * D`; multiply by `α`, use `hα` and `E = p + z * r`.
  let W'' : BPlus := ainfToBPlus α * D - ainfToBPlus (p ^ v • r + β * c.E) * W j
  have h_lte : ainfToBPlus (tau * c.E * (p ^ v + β * c.z) - p ^ v • tau * (c.E - p : c.S)) =
      ainfToBPlus (α * (teichmuller p epsTilt ^ (n + 1) - 1) - p ^ v • tau * (c.z * r : c.S)) := by
    rw [hα, hr]
  have hY_ij : q • (t • Y) i j = q • (Y * G.map ainfToBPlus) i j := by rw [hY]
  have h_expand : ainfToBPlus (α * (∑ l : d, A l * G l j - t • A j)) =
      ainfToBPlus (tau * c.z ^ (n + 1)) * (p ^ (v + 1) * W j - ainfToBPlus c.z * W'') := by
    linear_combination (norm :=
      (simp [W'', ← smul_algebraMap_eq_algebraMap_smul t (A _), smul_sub, hA, ht_z, mu, mul_sub,
         mul_assoc, mul_apply, ← mul_sum, sub_mul, Matrix.one_apply, sub_eq_zero]
       ring) )
      -ainfToBPlus c.z ^ (n + 1) *
          (ainfToBPlus α * hD + W j * h_lte) -
        ainfToBPlus α * hY_ij
  -- Divide by `tau * z ^ (n + 1)` in `Ainf` and apply the `S_B`-linear projection onto `S_B`.
  have h_dvd : ainfToBPlus (tau * c.z ^ (n + 1)) ∣
      ainfToBPlus (c.E ^ 0 * (α * (∑ l : d, A l * G l j - t • A j))) := by
    rw [pow_zero, one_mul]
    exact ⟨_, h_expand⟩
  obtain ⟨x, hx⟩ : tau * c.z ^ (n + 1) ∣ α * (∑ l : d, A l * G l j - t • A j) :=
    tau_mul_z_pow_dvd_of_dvd_E_pow_mul h_dvd
  have h_quotient : ainfToBPlus x = p ^ (v + 1) * W j - ainfToBPlus c.z * W'' := by
    simpa [hx, ne_zero_of_map c.theta_z_ne_zero] using h_expand
  refine ⟨c.adicBasis.coord c.oneIndex x, _, c.extendedCoord_mem_bicommutant c.oneIndex W'', ?_⟩
  have h_proj : c.extendedCoord c.oneIndex (ainfToBPlus x) =
      c.extendedCoord c.oneIndex (p ^ (v + 1) * W j - ainfToBPlus c.z * W'') := by
    rw [h_quotient]
  simpa [extendToBPlus_ainfToBPlus, map_p_pow_mul, hW, extendedCoord_oneIndex_eq_self,
    extendToBPlus_mul] using h_proj

/-- Let `c` be a chart with z = `c.z`, S = `c.S` and S_B = `c.bicommutant`, and let t ∈ G_p fix Λ
and θ(z) (`c.FixesThetaZ t`) with t•z = [ε]z. Let `ev` : S⟦X⟧ → B⁺ be an S-algebra map with
z^{p^l} = p²·ev(X) and z ∣ ev(X). Let Y, W be matrices over B⁺ and G a matrix over A_inf with
t•Y = YG, with τ·z dividing every entry of G − 1 (τ = [ε^{1/p}] − 1), W over S_B and Y = 1 + z·W.
Then every entry p²·φ^l(W_ij), with φ = `frobEnd`, equals ev(f) for some f ∈ S⟦X⟧. -/
lemma exists_ev_eq_frobEnd_pow (ht_fixes : c.FixesThetaZ t)
    (ht_z : t • c.z.val = teichmuller p epsTilt * c.z.val) {l : ℕ}
    {ev : c.S⟦X⟧ →ₐ[c.S] BPlus} (hX : ainfToBPlus c.z ^ p ^ l = p ^ 2 * ev X)
    (hz : ainfToBPlus c.z ∣ ev X) {G : Matrix d d Ainf} {Y W : Matrix d d BPlus}
    (hY : t • Y = Y * G.map ainfToBPlus) (hG : ∀ i j : d, tau * c.z ∣ (G - 1) i j)
    (hW : ∀ i j : d, W i j ∈ c.bicommutant) (hYW : Y = 1 + ainfToBPlus c.z • W) (i j : d) :
    ∃ f : c.S⟦X⟧, ev f = p ^ 2 * (frobEnd ^ l) (W i j) := by
  -- Successive approximation in powers of `ev X`, for which `BPlus` is separated as `z ∣ ev X`.
  have h_hausdorff : IsHausdorff (span {ev X}) BPlus := by
    refine ⟨fun x hx ↦ c.eq_zero_of_z_pow_dvd fun n ↦ ?_⟩
    grw [hz, smodEq_span_pow_iff_dvd.mp (hx n), sub_zero]
  -- The family: `p ^ (n - v_p n! + 2) * φ ^ l (W' j)` for the rows `W'` over `S_B` such that
  -- `q • Y i - z ^ (n + 1) * W'` is a row over `Ainf`; row `i` of `W` is one, with `n = 0`.
  let Row : Type :=
    {x : ℕ × (d → BPlus) //
      (∀ j : d, x.snd j ∈ c.bicommutant) ∧
      ∃ q : ℕ, ∃ A : d → Ainf, ∀ j : d,
        ainfToBPlus (A j) = q • Y i j - ainfToBPlus c.z ^ (x.fst + 1) * x.snd j}
  let g (x : Row) : BPlus :=
    p ^ (x.val.fst - padicValNat p x.val.fst ! + 2) * (frobEnd ^ l) (x.val.snd j)
  have h_start :
      ∀ k : d, ainfToBPlus (row 1 i k) = 1 • Y i k - ainfToBPlus c.z ^ (0 + 1) * W i k := by
    simp [hYW, one_apply, apply_ite, -algebraMap_smul]
  have h_ev_smul :
      ∀ F : c.S⟦X⟧, ev.toAddMonoidHom ((X : c.S⟦X⟧) • F) = ev X • ev.toAddMonoidHom F := by
    simp
  suffices step : ∀ x : Row, ∃ (f : c.S⟦X⟧) (x' : Row), g x = ev f + ev X * g x' by
    simpa [g] using mem_range_of_approx (π := (X : c.S⟦X⟧)) (π' := ev X) ev.toAddMonoidHom
      h_ev_smul g step ⟨(0, W i), hW i, 1, row 1 i, h_start⟩
  -- Each member is a value of `ev` plus `ev X` times a member with `n + 1` in place of `n`.
  rintro ⟨⟨n, W_row⟩, hW_row, q, A, hA⟩
  choose s W' hW' hs using exists_ainfToBPlus_eq_p_pow_mul_sub_z_mul ht_fixes ht_z hY hG hW_row hA
  set v : ℕ := padicValNat p (n + 1)
  let a : ℕ := n + 1 - padicValNat p (n + 1)!
  -- The exponents match because `v_p (n + 1)! = v + v_p n! ≤ n + 1`.
  have h_exp : n - padicValNat p n ! + 2 = a + v + 1 := sub_padicValNat_factorial_add_two_eq n
  refine ⟨C (p ^ a * (c.φ ^ l) (s j)), ⟨(n + 1, W'), hW', p ^ (v + 1) * q,
    p ^ (v + 1) • A + fun j ↦ c.z.val ^ (n + 1) * s j, fun j ↦ ?_⟩, ?_⟩
  · -- The new row is `p ^ (v + 1) • A + z ^ (n + 1) * s`, and `p ^ (v + 1) * W_row - s = z * W'`.
    suffices h_ring :
        (p : BPlus) ^ (v + 1) * ((q : BPlus) * Y i j - ainfToBPlus c.z ^ (n + 1) * W_row j) +
            ainfToBPlus c.z ^ (n + 1) * ((p : BPlus) ^ (v + 1) * W_row j - ainfToBPlus c.z * W' j) =
          (p : BPlus) ^ (v + 1) * q * Y i j - ainfToBPlus c.z ^ (n + 1 + 1) * W' j by
      simpa [hA, hs] using h_ring
    ring
  · -- Apply `φ ^ l` to `hs j`; the factor `p ^ 2` turns `ev X` into `φ ^ l z`.
    suffices h_ring :
        (p : BPlus) ^ (a + v + 1) * (frobEnd ^ l) (W_row j) =
          (p : BPlus) ^ a *
              ((p : BPlus) ^ (v + 1) * (frobEnd ^ l) (W_row j) -
                (p : BPlus) ^ 2 * ev X * (frobEnd ^ l) (W' j)) +
            ev X * ((p : BPlus) ^ (n + 1 - padicValNat p (n + 1)! + 2) * (frobEnd ^ l) (W' j)) by
      simpa [g, h_exp, ← frobEnd_pow_ainfToBPlus, hX, hs, C_eq_algebraMap,
        Subalgebra.algebraMap_def, -RingHom.coe_pow] using h_ring
    ring

/-- For `3 * e ≤ p ^ l` there is an `S`-algebra map `ev₀ : S⟦X⟧ → Amax` with
`z ^ (p ^ l) = p ^ 2 * ev₀ X` in `BPlus`: it evaluates at `X = p * T`, where
`z ^ (p ^ l) = p ^ 3 * T` with `T` in the `p`-adically complete ring `Amax`. -/
private lemma exists_algHom_z_pow_eq_p_pow_two_mul {l : ℕ} (hl : 3 * c.e ≤ p ^ l) :
    ∃ ev₀ : c.S⟦X⟧ →ₐ[c.S] Amax,
      ainfToBPlus c.z ^ p ^ l = p ^ 2 * algebraMap Amax BPlus (ev₀ X) := by
  obtain ⟨T, hT⟩ := exists_z_pow_eq ((mul_comm c.e 3).trans_le hl)
  obtain ⟨ev₀, h₀⟩ : ∃ ev₀ : c.S⟦X⟧ →ₐ[c.S] Amax, ev₀ X = p * T :=
    exists_algHom_X_eq c.S (mem_span_singleton.mpr (dvd_mul_right (p : Amax) T))
  exact ⟨ev₀, by simp [h₀, hT, pow_succ, mul_assoc]⟩

/-- Let `Z` be a matrix over `S_B` with `Z' * Z = E ^ h`. Then there are a matrix `B` over `BPlus`
whose entries are fixed by every `g` that fixes the constants Λ, and a matrix `W` over `S_B`, with
`B * Z = 1 + z • W`. -/
private lemma exists_mul_eq_one_add_z_smul {Z Z' : Matrix d d BPlus} {h : ℕ}
    (hZ : ∀ i j : d, Z i j ∈ c.bicommutant) (hZ' : Z' * Z = c.E ^ h • 1) :
    ∃ B W : Matrix d d BPlus,
      (∀ g : Gp p, FixesLambda c.f g → ∀ i j : d, g • B i j = B i j) ∧
      (∀ i j : d, W i j ∈ c.bicommutant) ∧
      B * Z = 1 + ainfToBPlus c.z • W := by
  obtain ⟨u, hu, hup⟩ := c.exists_bicommutant_mul_p_eq_one
  obtain ⟨q, hq⟩ : c.z ∣ c.E ^ h - p ^ h := c.z_dvd_E_sub_p.trans (sub_dvd_pow_sub_pow _ _ h)
  have hu_fix (g : Gp p) : g • u = u := by
    simpa [mul_assoc, mul_eq_one_symm hup] using congrArg (g • · * u) hup
  -- `B` holds the constant terms of the `S_B`-components of `p⁻¹ ^ h Z'`.
  choose m w y hy h_dec using fun i j ↦
    (c.eventually_exists_pow_mul_eq_add_z_mul
      (c.extendedCoord_mem_bicommutant c.oneIndex (u ^ h * Z' i j))).exists
  let B : Matrix d d BPlus := of fun i j ↦ u ^ m i j * ainfToBPlus (algebraMap _ _ (w i j))
  let W : Matrix d d BPlus := (u ^ h * ainfToBPlus q) • 1 - (of fun i j ↦ u ^ m i j * y i j) * Z
  have hW_mem (i j : d) : W i j ∈ c.bicommutant := by
    simp (maxDischargeDepth := 5) [W, mul_apply, sub_mem, _root_.sum_mem, mul_mem, hu, hy, hZ,
      Matrix.one_apply, ite_mem, pow_mem]
  refine ⟨B, W, fun g hg i j ↦ ?_, hW_mem, ?_⟩
  · simp [B, hg, hu_fix]
  · -- Project `Z' Z = E ^ h` to `S_B`, multiply by `u ^ h`, and insert `hq` and `h_dec`.
    ext i j
    have h_proj :
        u ^ h * (c.extendedCoord c.oneIndex ((Z' * Z) i j) +
            ainfToBPlus (c.E ^ h - p ^ h : c.S) * row 1 i j) =
          u ^ h * (c.extendedCoord c.oneIndex ((c.E ^ h • (1 : Matrix d d BPlus)) i j) +
            ainfToBPlus (c.z * q : c.S) * row 1 i j) :=
      by rw [hZ', hq]
    linear_combination (norm :=
      (simp [B, W, mul_apply, ← sub_eq_of_eq_add (h_dec _ _), mul_sub, mul_add, ← mul_assoc,
         ← mul_pow, hup, mul_sum, hu, hZ, mul_comm (Z' _ _), smul_def (A := BPlus),
         mul_right_comm _ (Z _ _), pow_mem, extendToBPlus_mul, sub_mul, Matrix.one_apply,
       Subalgebra.algebraMap_def, ite_mem, extendedCoord_oneIndex_eq_self, sub_eq_zero]
       split
       · ring_nf
       · ring_nf) )
      h_proj

/-- The conclusion of the radius lemma for a matrix `Z` over `BPlus`, exponents `l` and `b`, a
matrix `V` invertible over `Amax` and a matrix `C` over `BPlus`. -/
structure IsRadiusFactorization (c : Chart) (Z : Matrix d d BPlus) (l b : ℕ)
    (V : (Matrix d d Amax)ˣ) (C : Matrix d d BPlus) : Prop where
  /-- Every `g` in `G_p` that fixes the constants Λ fixes `C`. -/
  smul_C_eq : ∀ g : Gp p, FixesLambda c.f g → g • C = C
  /-- After `l` Frobenius steps, `Z` is `φ ^ l (E) ^ b` times `C * V`. -/
  map_frobEnd_eq :
    Z.map frobEnd^[l] = (c.frobE l).val ^ b • (C * V.val.map (algebraMap Amax BPlus))
  /-- For `e * A ≤ p ^ l * δ`, the `y` with `V y` natural modulo `E ^ A` span at least
  `p ^ (4 * δ) • S ^ d`. -/
  pow_smul_mem_span (A δ : ℕ) (h_le : c.e * A ≤ p ^ l * δ) (x : d → c.S) :
    p ^ (4 * δ) • x ∈
      Submodule.span c.S (natCongruentSet c (V.val.map (algebraMap Amax BPlus)) A)

/-- Radius lemma. Let t fix the image of Λ = W(F_{p^f}) in A_inf and θ(z), with z the chart
coordinate (`c.FixesThetaZ`), and let tz = [ε]z. Let Z be a matrix over S_B (`c.bicommutant`) with
Z′Z = E^h and tZ = ZG for some G over A_inf, and let 3e ≤ p^l and b ∈ ℕ. Then there are V invertible
over `New.Period.Amax` and C over B⁺ with `IsRadiusFactorization`: C is fixed by every g that fixes
Λ, φ^l(Z) = φ^l(E)^b·C·V, and, whenever e·A ≤ p^l·δ, the y with Vy natural modulo E^A span at least
p^{4δ}S^d. -/
lemma radius_lemma (ht_fixes : c.FixesThetaZ t)
    (ht_z : t • c.z.val = teichmuller p epsTilt * c.z.val) {Z Z' : Matrix d d BPlus}
    {h : ℕ} (hZ : ∀ i j : d, Z i j ∈ c.bicommutant) (hZ' : Z' * Z = c.E ^ h • 1)
    {G : Matrix d d Ainf} (hG : t • Z = Z * G.map ainfToBPlus) {l : ℕ} (hl : 3 * c.e ≤ p ^ l)
    (b : ℕ) :
    ∃ (V : (Matrix d d Amax)ˣ) (C : Matrix d d BPlus), IsRadiusFactorization c Z l b V C := by
  -- Correct `Z` by a matrix `B` of constants so that `B Z ≡ 1` modulo `z`. By
  -- `exists_ev_eq_frobEnd_pow`, `φ ^ l (B Z)` is the value at `X = φ ^ l (z) / p ^ 2` of a unit
  -- `1 + X F` over `S⟦X⟧`; likewise `φ ^ l (E)` is `p` times the value of a unit `ε`.
  -- Write `1 + X F = ε ^ b V` and take `C = (p ^ b φ ^ l (B))⁻¹`.
  obtain ⟨ev₀, h₀⟩ := exists_algHom_z_pow_eq_p_pow_two_mul hl
  let ev : c.S⟦X⟧ →ₐ[c.S] BPlus := (IsScalarTower.toAlgHom _ _ BPlus).comp ev₀
  have hX : ainfToBPlus c.z ^ p ^ l = p ^ 2 * ev X := by simpa [ev] using h₀
  have hz : ainfToBPlus c.z ∣ ev X := by
    simpa [hX, (isUnit_p.pow 2).dvd_mul_left, -isUnit_map_iff] using
      dvd_pow_self (ainfToBPlus c.z) (NeZero.ne (p ^ l))
  obtain ⟨r, hr⟩ := c.z_dvd_E_sub_p
  obtain ⟨B, W, hB_fix, hW_mem, hW⟩ := exists_mul_eq_one_add_z_smul hZ hZ'
  have hBZ : t • (B * Z) = B * Z * G.map ainfToBPlus := by
    rw [Matrix.mul_assoc, ← hG]
    ext i j
    simp [mul_apply, smul_sum, smul_mul', hB_fix t ht_fixes.left]
  -- `E ^ h (G - 1) = Z' (t Z - Z)` is divisible by `tau * z`, hence so is `G - 1`.
  have hG_one (i j : d) : tau * c.z ∣ (G - 1) i j := by
    have h_dvd : ainfToBPlus (tau * c.z) ∣ (Z' * (t • Z - Z)) i j :=
      dvd_sum fun k _ ↦ (tau_mul_z_dvd_smul_sub ht_fixes (hZ k j)).mul_left _
    rw [← pow_one c.z.val]
    refine tau_mul_z_pow_dvd_of_dvd_E_pow_mul (h := h) ?_
    -- The entries of `Z' * (t • Z - Z)` are those of `ainfToBPlus (E ^ h * (G - 1))`.
    simpa [mul_sub, ← mul_assoc, hZ', hG, smul_def (A := BPlus), apply_ite, Matrix.one_apply,
      Subalgebra.algebraMap_def, -isUnit_map_iff] using h_dvd
  choose F hF using fun i j ↦ exists_ev_eq_frobEnd_pow ht_fixes ht_z hX hz hBZ hG_one hW_mem hW i j
  obtain ⟨V', hV'⟩ : IsUnit (1 + (X : c.S⟦X⟧) • of F) := by
    simp [isUnit_iff_isUnit_det, det_one_add_smul X, isUnit_iff_constantCoeff, -smul_of]
  obtain ⟨ε, hε⟩ : IsUnit (1 + X * C (p * (c.φ ^ l) r)) := by simp [isUnit_iff_constantCoeff]
  -- Apply `φ ^ l` to `hW`: `φ ^ l (z) • φ ^ l (W) = ev X • ev F` by `hX` and `hF`.
  have hBZ_frob : B.map (frobEnd ^ l) * Z.map (frobEnd ^ l) = ev.mapMatrix V' := by
    rw [← Matrix.map_mul]
    ext i j
    simp [hW, hV', hX, hF, Matrix.one_apply, mul_assoc, mul_left_comm, -algebraMap_smul,
      -RingHom.coe_pow]
  -- Apply `φ ^ l` to `E = p + z * r`.
  have h_pa : ainfToBPlus (c.frobE l) = p * ev ε := by
    simp [frobE, hε, hX, eq_add_of_sub_eq' hr, ← frobEnd_pow_ainfToBPlus, C_eq_algebraMap,
      Subalgebra.algebraMap_def, mul_add, pow_two, mul_assoc, mul_left_comm, -RingHom.coe_pow]
  have h_unit : IsUnit (B.map (frobEnd ^ l) * Z.map (frobEnd ^ l)) := by
    rw [hBZ_frob]
    exact V'.isUnit.map _
  obtain ⟨D, hD_eq⟩ : IsUnit ((isUnit_p.pow b).unit • B.map (frobEnd ^ l)) :=
    (isUnit_of_mul_isUnit_left h_unit).smul _
  obtain ⟨V, rfl⟩ : ∃ V : (Matrix d d c.S⟦X⟧)ˣ, ε ^ b • V = V' := MulAction.surjective _ V'
  refine ⟨V.map ev₀.mapMatrix.toMonoidHom, ↑D⁻¹, ⟨fun g hg ↦ ?_, ?_, fun A δ hA x ↦
    pow_smul_mem_span_of_unit (NeZero.pos _) (fun _ ↦ rfl) hX V hA x⟩⟩
  · -- `g` fixes `D`, hence `D⁻¹`: it fixes the entries of `B` and commutes with `φ`
    suffices h_map_D :
        D.map (MulSemiringAction.toRingHom (Gp p) BPlus g).mapMatrix.toMonoidHom = D from
      congrArg (fun U ↦ (U⁻¹).val) h_map_D
    ext
    simp [hD_eq, hB_fix g hg, RingHom.coe_pow, Commute.iterate_right (smul_frobEnd g) l _]
  · -- multiply by `D = p ^ b φ ^ l (B)`, use `hBZ_frob`; `h_pa` accounts for `(p * ev ε) ^ b`
    rw [← mul_smul_comm, D.eq_inv_mul_iff_mul_eq, hD_eq, smul_mul_assoc, ← RingHom.coe_pow,
      hBZ_frob]
    ext
    simp [h_pa, ev, mul_pow, mul_assoc, smul_def (A := BPlus), Units.smul_def]

end New.Lift.Chart
