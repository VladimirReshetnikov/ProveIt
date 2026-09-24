import Diophantine.Paper1980.TagDecode91
import Diophantine.Paper1980.TagSound

/-!
# Soundness of the 91-operation tag certificate

Every positive solution of `Sys91` at an encoded instance `(Ninit, Linit)` of a normalized
binary tag system whose fixed constants match the certificate (`Matches`) makes the actual
tag machine halt from the initial queue: the decoded row data (`decode91`, `TagDecode91`)
assemble the context `Ctx` of the generic soundness theorem `halts_of_ctx`.
-/

namespace Jones1980

open Ternary TagSys

theorem pow3_inj {x y : ℕ} (h : 3 ^ x = 3 ^ y) : x = y :=
  Nat.pow_right_injective (by norm_num : 2 ≤ 3) h

/-- The tag system `TS` has the fixed constants of the certificate `T`. -/
structure Matches (T : Tag91) (TS : TagSys) : Prop where
  β_eq : 3 * T.Khalf = 3 ^ TS.β
  U_eq : content TS.u = 3 * T.Uthird + T.ε
  B_eq : 3 * T.B = 3 ^ TS.u.length

/-- **Soundness** of the tag certificate: a positive solution halts the actual tag machine. -/
theorem sound91 {T : Tag91} {TS : TagSys} {W₀ : List Bool} {Ninit Linit : ℕ}
    (hT : T.Ok) (hM : Matches T TS) (hI : Input91 T Ninit Linit)
    (hW : content W₀ = Ninit) (hL : 3 ^ W₀.length = Linit)
    (hsol : Solvable91 T Ninit Linit) : TS.Halts W₀ := by
  obtain ⟨Q, S1, Tc, E, H, R, L, q, v, r, β, a, c, d, f, h, i, j, k, o, s, w, τ, η, ζ, γ, y, D,
    Z, hP, hS⟩ := hsol
  have hU : 3 * T.Uthird + T.ε < 3 * T.B := by
    rw [← hM.U_eq, hM.B_eq]; exact content_lt TS.u
  obtain ⟨e, m, t, γ', β', a', hG, hF⟩ := decode91 hT hU hI hP hS
  -- the exponents of the fixed constants are those of the tag system
  have hβ' : β' = TS.β := by
    have h1 : 3 ^ β' = 3 ^ TS.β := by
      rw [← hM.β_eq, hG.hk, ← pow_succ', Nat.sub_add_cancel (by have := hG.hβ; omega)]
    exact pow3_inj h1
  have ha' : a' = TS.u.length := by
    have h1 : 3 ^ a' = 3 ^ TS.u.length := by
      rw [← hM.B_eq, hG.hB, ← pow_succ', Nat.sub_add_cancel (by have := hG.ha; omega)]
    exact pow3_inj h1
  subst hβ' ha'
  -- the guarded content as a natural number
  obtain ⟨GN, hGN⟩ : ∃ GN : ℕ, (GN : ℤ) = T.N Q S1 Tc + T.jg * Z :=
    ⟨(T.N Q S1 Tc + T.jg * Z).toNat, Int.toNat_of_nonneg hF.GN_pos.le⟩
  have hGNb : Bool3 GN := hF.bGN GN hGN
  have hGNlt : GN < 3 ^ (m * t) := by
    have h1 : (GN : ℤ) ≤ rep e := hGN ▸ hF.GN_le
    have h2 : GN ≤ rep e := by exact_mod_cast h1
    have h3 : rep e < 3 ^ (m * t) := by rw [← hG.he]; exact rep_lt e
    omega
  -- the initial length and the input bound
  have hℓ₀ : TS.β ≤ W₀.length := by
    obtain ⟨ℓ, β'', hβ2, hk, hβℓ, hLi⟩ := hI.Linit_pow
    have h1 : ℓ = W₀.length := pow3_inj (by rw [← hLi, hL])
    have h2 : β'' = TS.β := by
      have : 3 ^ (β'' - 1) = 3 ^ (TS.β - 1) := by rw [← hk, hG.hk]
      have := pow3_inj this
      omega
    omega
  have hℓ₀m : W₀.length + 2 * TS.β < m := by
    have h1 := hI.bound
    have h2 := C_le_R91 hT hP hS
    rw [hM.β_eq, ← hL, ← pow_mul, ← pow_add] at h1
    rw [hG.hR] at h2
    have h3 : 3 ^ (TS.β * 2 + W₀.length) < 3 ^ m := lt_of_lt_of_le h1 h2
    have := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h3
    omega
  -- the projector rows and the offset bound of the `M₁`-markers
  have hM1row : ∀ i, i < t → ∃ ℓ, row (2 * Q + S1) m i = if dg S1 (m * i) = 1 then 3 ^ ℓ else 0 :=
    fun i hi => by
      obtain ⟨ℓ, -, -, hr⟩ := rows_QM hG hF hP.Q hi
      exact ⟨ℓ, hr⟩
  have hM1α : ∀ p, dg (2 * Q + S1) p = 1 → p % m + TS.u.length + TS.β < m := by
    intro p hp
    have hplt : p < m * t := by
      by_contra hge; push Not at hge
      have : dg (2 * Q + S1) p = 0 := dg_eq_zero_of_lt (lt_of_lt_of_le (M1_lt hG hF)
        (Nat.pow_le_pow_right (by norm_num) hge))
      omega
    have hi : p / m < t := by
      rw [Nat.div_lt_iff_lt_mul (by have := hG.hm; omega)]; linarith [Nat.mul_comm m t]
    obtain ⟨ℓ, hℓα, -, hr⟩ := rows_QM hG hF hP.Q hi
    have hpm : p % m < m := Nat.mod_lt _ (by have := hG.hm; omega)
    have hdg : dg (2 * Q + S1) p = dg (row (2 * Q + S1) m (p / m)) (p % m) := by
      rw [dg_row _ _ hpm, Nat.div_add_mod]
    rw [hdg, hr] at hp
    by_cases hs : dg S1 (m * (p / m)) = 1
    · rw [if_pos hs, dg_pow] at hp
      by_cases hk : p % m = ℓ
      · -- `a + β + 1 < γ`
        have hγ : TS.u.length + TS.β + 1 < γ' := by
          have h1 := hT.C_gt_KB
          rw [hM.β_eq, hM.B_eq, hG.hC] at h1
          have h2 : 3 * 3 ^ TS.β * 3 ^ TS.u.length = 3 ^ (TS.u.length + TS.β + 1) := by
            rw [pow_add, pow_add, pow_one]; ring
          rw [h2] at h1
          exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h1
        have := hG.hγm
        omega
      · rw [if_neg hk] at hp; omega
    · rw [if_neg hs, dg_zero] at hp; omega
  -- the length equation
  have heq : (L - (2 * Q + S1)) + (2 * Q + S1) + 3 ^ (m * t + 1) =
      3 ^ W₀.length + 3 ^ (m - (TS.β - 1)) * (L - (2 * Q + S1)) +
        3 ^ (m - (TS.β - 1) + (TS.u.length - 1)) * (2 * Q + S1) := by
    have h := length_eq91 hT hI hP hS hG hF
    rw [hL, ← hG.he, pow_succ, ← hG.hq, mul_comm q 3]
    exact h
  -- the content transport
  have htrans : ((3 ^ m : ℕ) : ℤ) * (((GN : ℤ) - rep TS.β * 3 ^ (m - TS.β) * heads m t) -
      (3 * E + S1) + content TS.u * (2 * Q + S1)) =
    (3 ^ TS.β : ℕ) * (((GN : ℤ) - rep TS.β * 3 ^ (m - TS.β) * heads m t) - content W₀) := by
    have hid := content_identity91 hT hP hS
    have hjZ := jZ_eq hT hG hF
    have hN : T.N Q S1 Tc = (GN : ℤ) - rep TS.β * 3 ^ (m - TS.β) * heads m t := by
      rw [hGN]
      have : ((T.jg * Z : ℕ) : ℤ) = rep TS.β * 3 ^ (m - TS.β) * heads m t := by
        rw [hjZ, hG.hH]; push_cast; ring
      push_cast at this ⊢
      linarith
    have hR : ((3 ^ m : ℕ) : ℤ) = R := by rw [hG.hR]
    have hK : ((3 ^ TS.β : ℕ) : ℤ) = 3 * T.Khalf := by rw [← hM.β_eq]; push_cast; ring
    have hUe : (content TS.u : ℤ) = 3 * T.Uthird + T.ε := by exact_mod_cast hM.U_eq
    rw [hR, hK, hUe, ← hN, hW]
    push_cast at hid ⊢
    linear_combination -hid
  -- assemble the context
  have C : Ctx TS W₀ m t (L - (2 * Q + S1)) (2 * Q + S1) S1 E GN :=
    { hm := hG.hm
      ht := hG.ht
      hβ := hG.hβ
      ha := hG.ha
      hβm := hG.hβm
      hℓ₀ := hℓ₀
      hℓ₀m := hℓ₀m
      hM0 := hF.bM0
      hM1 := hF.bM1
      hM0lt := by
        have := hF.L_lt
        rw [hG.he] at this
        have : 0 < 3 ^ (m * t) := by positivity
        omega
      hM1lt := M1_lt hG hF
      hS1 := hF.bS1
      hS1lt := S1_lt hG hF
      hS1H := S1_heads hG hF
      hE := hF.bE
      hElt := by
        have := hF.E_lt
        rw [hG.he] at this
        have : 0 < 3 ^ (m * t) := by positivity
        omega
      hEsupp := E_support hT hG hF
      hGN := hGNb
      hGNlt := hGNlt
      hM1row := hM1row
      hM1α := hM1α
      heq := heq
      htrans := htrans }
  exact halts_of_ctx C

end Jones1980
