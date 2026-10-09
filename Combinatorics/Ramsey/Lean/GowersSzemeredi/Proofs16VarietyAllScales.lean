import GowersSzemeredi.Proofs16OscillationPartition
import GowersSzemeredi.Proofs16BoundedChunks

/-! The variety route at all scales: `MultiplyLinearWith` with explicit controls.

`oscillation_partition_of_scales` needs `P.width ≥ T`. This module covers
every proper box.

* **Wide boxes** (`T ≤ w = P.width`). Take `H₂` to be the largest `h` with
  `h^e ≤ w`, and `H₁ = H₂^{e₂}`, where `e = e₂ e₁`,
  `e₁ = p(|Γ|+|Ψ|+1)^8` and `e₂ = p(r+1)^8`. Every cell is good, so one
  multilinear map covers it. Maximality gives `w < (H₂+1)^e ≤ H₂^{2e}`, hence
  `w^{1/(2e)} ≤ H₂`.
* **Narrow boxes** (`w < T`). `Box.bounded_partition` at scale `w` gives
  cells of width `≥ w` with axis lengths `< 2w`, so fewer than `4T²` points
  each. Constant maps cover them (`cell_cover_small`).

Result (`variety_multiplyLinear_all_scales`): the graph of `Φ` over `V(ρ/2)`
is `MultiplyLinearWith` with constant controls `Qb = 4T²` and
`Eb = 1/(2e)`, where `T = H₀^e` and
`H₀ = ⌈max(K(r+1), K(|Γ|+|Ψ|+1), 16/ρ)⌉`. The inverse width exponent
`2e` is polynomial in the rank. `Qb` is polynomial in `1/ρ`, of degree
polynomial in the rank. With Milićević's bounds (`ρ ≥ exp(−B)`, rank `≤ B`)
both are `exp(poly(B))`, i.e. quasi-polynomial in `1/c`. The only hypothesis
beyond the Freiman data is `MultilinearDiameterPartition K p`, which is the
peer's theorem (`Proofs16OscillationPartitionInst`). No `θ` is spent: the
loss set is the whole box. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- A two-dimensional box has at most `len₀ · len₁` points. -/
theorem box_two_card_le {N : Nat} [NeZero N] (Q : Box N 2) :
    Q.carrier.card ≤ (Q.axis 0).length * (Q.axis 1).length := by
  have hsub : Q.carrier ⊆ (Finset.range (Q.axis 0).length ×ˢ Finset.range (Q.axis 1).length).image
      (fun ij => (![(Q.axis 0).start + (ij.1 : ZMod N) * Q.commonDiff,
        (Q.axis 1).start + (ij.2 : ZMod N) * Q.commonDiff] : Point N 2)) := by
    intro x hx
    obtain ⟨⟨i, hi, hix⟩, ⟨j, hj, hjx⟩⟩ := (mem_box_two Q x).mp hx
    refine Finset.mem_image.mpr ⟨(i, j), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hi, Finset.mem_range.mpr hj⟩, ?_⟩
    funext t
    fin_cases t
    · exact hix
    · exact hjx
  calc Q.carrier.card ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_image_le
    _ = _ := by rw [Finset.card_product, Finset.card_range, Finset.card_range]

/-- **Small cells are covered by constant maps.** -/
theorem cell_cover_small {N : Nat} [NeZero N] {S : Finset (ZMod N × ZMod N)}
    {Φ : ZMod N × ZMod N → ZMod N} {Gamma : Finset (Point N 2 × ZMod N)}
    (hΓ : IsGraphOver Gamma S Φ) (Q : Box N 2) (q : Nat) (hcard : Q.carrier.card ≤ q) :
    ∃ mu : Fin q → Point N 2 → ZMod N, (∀ i, IsMultilinear (mu i)) ∧
      ∀ x ∈ Q.carrier, ∀ y, (x, y) ∈ Gamma → ∃ i, y = mu i x := by
  let e := Q.carrier.equivFin
  let pt : Fin q → Point N 2 := fun i =>
    if h : i.val < Q.carrier.card then (e.symm ⟨i.val, h⟩).1 else 0
  refine ⟨fun i x => Φ ((pt i) 0, (pt i) 1) + 0 * x 0 + 0 * x 1 + 0 * (x 0 * x 1),
    fun i => isMultilinear_two _ _ _ _, fun x hx y hxy => ?_⟩
  let i : Fin q := ⟨(e ⟨x, hx⟩).val, lt_of_lt_of_le (e ⟨x, hx⟩).isLt hcard⟩
  refine ⟨i, ?_⟩
  have hpt : pt i = x := by
    simp only [pt, i, dif_pos (e ⟨x, hx⟩).isLt]
    simp
  have hy : y = Φ (x 0, x 1) := (hΓ _ hxy).2
  simp only [hpt, hy]
  ring

/-- `w^E ≤ w` for natural `w` and `0 < E ≤ 1`. -/
theorem natCast_rpow_le_self (w : Nat) {E : Real} (hE : 0 < E) (hE1 : E ≤ 1) :
    (w : Real) ^ E ≤ w := by
  rcases Nat.eq_zero_or_pos w with h | h
  · subst h
    simp [Real.zero_rpow hE.ne']
  · have hw : (1 : Real) ≤ w := by exact_mod_cast h
    calc (w : Real) ^ E ≤ (w : Real) ^ (1 : Real) := Real.rpow_le_rpow_of_exponent_le hw hE1
      _ = w := Real.rpow_one _

/-- If `w < (h+1)^e` with `2 ≤ h` and `0 < e`, then `w^{1/(2e)} ≤ h`. -/
theorem rpow_inv_two_mul_le (w h e : Nat) (hh : 2 ≤ h) (he : 0 < e) (hw : w < (h + 1) ^ e) :
    (w : Real) ^ ((1 : Real) / (2 * e)) ≤ h := by
  set z := (w : Real) ^ ((1 : Real) / (2 * e)) with hz
  have hz0 : 0 ≤ z := Real.rpow_nonneg (Nat.cast_nonneg w) _
  have heR : (0 : Real) < e := by exact_mod_cast he
  have hzpow : z ^ (2 * e) = w := by
    rw [hz, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg w)]
    push_cast
    rw [one_div_mul_cancel (by positivity), Real.rpow_one]
  have hstep : ((h : Nat) + 1) ^ e ≤ h ^ (2 * e) := by
    rw [pow_mul]
    apply Nat.pow_le_pow_left
    nlinarith
  by_contra hcon
  push Not at hcon
  have h1 : (h : Real) ^ (2 * e) ≤ z ^ (2 * e) := pow_le_pow_left₀ (Nat.cast_nonneg h) hcon.le _
  rw [hzpow] at h1
  have h2 : (w : Real) < (h : Real) ^ (2 * e) := by
    have : ((w : Nat) : Real) < (((h + 1) ^ e : Nat) : Real) := by exact_mod_cast hw
    have h3 : (((h + 1) ^ e : Nat) : Real) ≤ ((h ^ (2 * e) : Nat) : Real) := by exact_mod_cast hstep
    push_cast at this h3
    linarith
  linarith

/-- The scale `H₀ = ⌈max(K(r+1), K(|Γ|+|Ψ|+1), 16/ρ)⌉`. -/
def varietyBaseScale (K ρ : Real) (r q₁ : Nat) : Nat :=
  ⌈max (K * ((r : Real) + 1)) (max (K * ((q₁ : Real) + 1)) (16 / ρ))⌉₊

/-- The total exponent `e = e₂ e₁`. -/
def varietyExponent (p r q₁ : Nat) : Nat :=
  (p * (r + 1) ^ (2 * (2 ^ 2))) * (p * (q₁ + 1) ^ (2 * (2 ^ 2)))

/-- **The variety route at all scales.** -/
theorem variety_multiplyLinear_all_scales {N : Nat} [NeZero N] [Fact N.Prime]
    {Γ Ψ : Finset (ZMod N)} {r : Nat} {L : Fin r → ZMod N → ZMod N} {ρ : Real} (hρ : 0 < ρ)
    (hL : ∀ k, IsFreimanLinearOn (bohr Ψ ρ) (L k)) {Φ : ZMod N × ZMod N → ZMod N}
    (hΦ : IsEBihomomorphism (bilinearBohrVariety Γ Ψ L ρ) Φ {0})
    {Gamma : Finset (Point N 2 × ZMod N)}
    (hΓ : IsGraphOver Gamma (bilinearBohrVariety Γ Ψ L (ρ / 2)) Φ)
    {K : Real} {p : Nat} (hK : 2 ≤ K) (hp : 0 < p) (hMD : MultilinearDiameterPartition K p) :
    MultiplyLinearWith
      (fun _ => ((4 * (varietyBaseScale K ρ r (Γ.card + Ψ.card) ^
        varietyExponent p r (Γ.card + Ψ.card)) ^ 2 : Nat) : Real))
      (fun _ => (1 : Real) / (2 * varietyExponent p r (Γ.card + Ψ.card))) Gamma := by
  obtain ⟨q₁, hq₁⟩ : ∃ q₁, q₁ = Γ.card + Ψ.card := ⟨_, rfl⟩
  obtain ⟨e₂, he₂⟩ : ∃ e₂, e₂ = p * (r + 1) ^ (2 * (2 ^ 2)) := ⟨_, rfl⟩
  obtain ⟨e₁, he₁⟩ : ∃ e₁, e₁ = p * (q₁ + 1) ^ (2 * (2 ^ 2)) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = varietyExponent p r q₁ := ⟨_, rfl⟩
  have hee : e = e₂ * e₁ := by rw [he, he₂, he₁]; rfl
  obtain ⟨H₀, hH₀⟩ : ∃ H₀, H₀ = varietyBaseScale K ρ r q₁ := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, T = H₀ ^ e := ⟨_, rfl⟩
  rw [← hq₁, ← he, ← hH₀, ← hT]
  have he₂pos : 0 < e₂ := by rw [he₂]; exact Nat.mul_pos hp (by positivity)
  have he₁pos : 0 < e₁ := by rw [he₁]; exact Nat.mul_pos hp (by positivity)
  have hepos : 0 < e := by rw [hee]; exact Nat.mul_pos he₂pos he₁pos
  have heR : (0 : Real) < e := by exact_mod_cast hepos
  -- properties of the base scale
  have hmax : max (K * ((r : Real) + 1)) (max (K * ((q₁ : Real) + 1)) (16 / ρ)) ≤ (H₀ : Real) := by
    rw [hH₀, varietyBaseScale]
    exact Nat.le_ceil _
  have hH₀r : K * ((r : Real) + 1) ≤ H₀ := (le_max_left _ _).trans hmax
  have hH₀q : K * ((q₁ : Real) + 1) ≤ H₀ :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hmax
  have hH₀ρ : 16 / ρ ≤ H₀ := ((le_max_right _ _).trans (le_max_right _ _)).trans hmax
  have hH₀2 : 2 ≤ H₀ := by
    have hr1 : (1 : Real) ≤ (r : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) r
      linarith
    have : (2 : Real) ≤ H₀ := by
      nlinarith only [mul_nonneg (sub_nonneg.2 hK) (sub_nonneg.2 hr1), hH₀r, hr1, hK]
    exact_mod_cast this
  -- exponent bounds
  have hEb : (0 : Real) < 1 / (2 * e) := by positivity
  have hEb1 : 1 / (2 * (e : Real)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (1 : Real) ≤ e := by exact_mod_cast hepos
    linarith
  intro theta htheta _ P hP
  by_cases hwide : T ≤ P.width
  · -- wide boxes: oscillation partitions, one map per cell
    obtain ⟨w, hw⟩ : ∃ w, w = P.width := ⟨_, rfl⟩
    rw [← hw] at hwide
    obtain ⟨H₂, hH₂def⟩ : ∃ H₂, H₂ = Nat.findGreatest (fun h => h ^ e ≤ w) w := ⟨_, rfl⟩
    have hH₀w' : H₀ ^ e ≤ w := by rw [← hT]; exact hwide
    have hH₀w : H₀ ≤ w := (Nat.le_self_pow hepos.ne' H₀).trans hH₀w'
    have hH₀H₂ : H₀ ≤ H₂ := by
      rw [hH₂def]; exact Nat.le_findGreatest (P := fun h => h ^ e ≤ w) hH₀w hH₀w'
    have hH₂good : H₂ ^ e ≤ w := by
      rw [hH₂def]; exact Nat.findGreatest_spec (P := fun h => h ^ e ≤ w) hH₀w hH₀w'
    have hH₂next : w < (H₂ + 1) ^ e := by
      by_contra hcon
      push Not at hcon
      by_cases hle : H₂ + 1 ≤ w
      · exact Nat.findGreatest_is_greatest (P := fun h => h ^ e ≤ w)
          (by rw [← hH₂def]; exact Nat.lt_succ_self H₂) hle hcon
      · push Not at hle
        have : H₂ + 1 ≤ (H₂ + 1) ^ e := Nat.le_self_pow hepos.ne' _
        omega
    have hH₂2 : 2 ≤ H₂ := hH₀2.trans hH₀H₂
    have hH₂R : (H₀ : Real) ≤ H₂ := by exact_mod_cast hH₀H₂
    obtain ⟨H₁, hH₁def⟩ : ∃ H₁, H₁ = H₂ ^ e₂ := ⟨_, rfl⟩
    have hH₂H₁ : H₂ ≤ H₁ := by rw [hH₁def]; exact Nat.le_self_pow he₂pos.ne' H₂
    have hH₁R : (H₂ : Real) ≤ H₁ := by exact_mod_cast hH₂H₁
    have hρH₀ : 16 ≤ ρ * H₀ := by
      rw [div_le_iff₀ hρ] at hH₀ρ
      linarith
    obtain ⟨M, Q, hpart, hprop, hwid, hcells⟩ :=
      oscillation_partition_of_scales hL hMD P hP H₁ H₂ (by omega)
        (hH₀r.trans hH₂R) (by nlinarith only [hρH₀, hH₂R, hρ])
        (by rw [← hq₁]; exact (hH₀q.trans hH₂R).trans hH₁R)
        (by nlinarith only [hρH₀, hH₂R, hH₁R, hρ])
        (by rw [← he₂, hH₁def]) hH₂H₁
        (by rw [← hq₁, ← he₁, hH₁def, ← pow_mul, ← hee, ← hw]; exact hH₂good)
    have hgood : ∀ j, CellGood (bilinearBohrVariety Γ Ψ L (ρ / 2))
        (bilinearBohrVariety Γ Ψ L ρ) (Q j) :=
      fun j => cellGood_of_small_oscillation (Q j) (hcells j)
    choose mu hmu hcov using fun j => cell_cover_of_good hΦ hΓ (Q j) (hgood j)
    refine ⟨M, 1, P.carrier, Q, fun j _ => mu j, subset_rfl, ?_, hpart, hprop, ?_, ?_,
      fun j _ => hmu j, ?_⟩
    · have hc : (0 : Real) ≤ P.carrier.card := Nat.cast_nonneg _
      linarith only [mul_nonneg htheta.le hc]
    · have hT1 : 1 ≤ 4 * T ^ 2 := by
        have : 1 ≤ T := by rw [hT]; exact Nat.one_le_pow _ _ (by omega)
        nlinarith
      show ((1 : Nat) : Real) ≤ ((4 * T ^ 2 : Nat) : Real)
      exact_mod_cast hT1
    · intro j
      rw [← hw]
      exact (rpow_inv_two_mul_le w H₂ e hH₂2 hepos hH₂next).trans (hwid j)
    · intro j x hx _ y hxy
      exact ⟨0, hcov j x hx y hxy⟩
  · -- narrow boxes: bounded chunks covered by constant maps
    push Not at hwide
    obtain ⟨w, hw⟩ : ∃ w, w = P.width := ⟨_, rfl⟩
    rw [← hw] at hwide ⊢
    have hwR : (w : Real) ^ ((1 : Real) / (2 * e)) ≤ w := natCast_rpow_le_self w hEb hEb1
    by_cases hne : P.carrier.Nonempty
    · have hw1 : 1 ≤ w := by
        obtain ⟨x, hx⟩ := hne
        obtain ⟨⟨i, hi, _⟩, ⟨j, hj, _⟩⟩ := (mem_box_two P x).mp hx
        rw [hw]
        apply Box.le_width_of_le_axis P (by norm_num)
        intro t
        fin_cases t
        · exact Nat.one_le_of_lt hi
        · exact Nat.one_le_of_lt hj
      obtain ⟨M, Q, hpart, hQ, hlen, _⟩ := Box.bounded_partition P hP (by norm_num) w hw1 hw.le
      have hcard : ∀ j, (Q j).carrier.card ≤ 4 * T ^ 2 := by
        intro j
        have h0 := (hlen j 0).2
        have h1 := (hlen j 1).2
        calc (Q j).carrier.card ≤ ((Q j).axis 0).length * ((Q j).axis 1).length :=
              box_two_card_le (Q j)
          _ ≤ (2 * w) * (2 * w) := Nat.mul_le_mul h0.le h1.le
          _ ≤ (2 * T) * (2 * T) := Nat.mul_le_mul (by omega) (by omega)
          _ = 4 * T ^ 2 := by ring
      choose mu hmu hcov using fun j => cell_cover_small hΓ (Q j) (4 * T ^ 2) (hcard j)
      refine ⟨M, 4 * T ^ 2, P.carrier, Q, mu, subset_rfl, ?_, hpart, fun j => (hQ j).1, ?_, ?_,
        hmu, ?_⟩
      · have hc : (0 : Real) ≤ P.carrier.card := Nat.cast_nonneg _
        linarith only [mul_nonneg htheta.le hc]
      · exact le_rfl
      · intro j
        exact hwR.trans (by exact_mod_cast (hQ j).2)
      · intro j x hx _ y hxy
        exact hcov j x hx y hxy
    · have hempty : P.carrier = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hcard : P.carrier.card ≤ 4 * T ^ 2 := by rw [hempty]; simp
      obtain ⟨mu, hmu, hcov⟩ := cell_cover_small hΓ P (4 * T ^ 2) hcard
      refine ⟨1, 4 * T ^ 2, P.carrier, fun _ => P, fun _ => mu, subset_rfl, ?_,
        isBoxPartition_self P, fun _ => hP, ?_,
        fun _ => (by rw [← hw]; exact hwR : (w : Real) ^ ((1 : Real) / (2 * e)) ≤ (P.width : Real)),
        fun _ => hmu, ?_⟩
      · have hc : (0 : Real) ≤ P.carrier.card := Nat.cast_nonneg _
        linarith only [mul_nonneg htheta.le hc]
      · exact le_rfl
      · intro _ x hx _ y hxy
        exact hcov x hx y hxy

end LeanProofs.GowersSzemeredi
