import Diophantine.Paper1980.PellRelaxed

/-!
# The relaxed auxiliary norm forces an integral Pell solution

Main result of `Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md`: for natural
parameters with `1 < A`, `0 < p`, `0 < i`, and `0 < f`, assume `c = ψ_A(p)`
and `c > A (A² − 1)²`. Then the relaxed norm
`(i c²)² = (A² − 1)(f² − 1)` gives an index `m` with `f = χ_A(m)`,
`i c² = (A² − 1) ψ_A(m)`, `p ∣ m`, and `c ∣ m` (`relaxed_aux`).
These conclusions supply the auxiliary Pell data used by `doubled_index_core`;
the main pair, odd target index, size conditions, divisibility condition,
and equation `E17` are supplied separately.
-/

namespace Jones1980

open Pell

/-- `A² − 1` is not a square for `A ≥ 2`. -/
theorem sq_sub_one_not_square {A s : ℕ} (hA : 1 < A) (h : s ^ 2 = A ^ 2 - 1) : False := by
  have h1 : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hA2eq : A ^ 2 = s ^ 2 + 1 := by omega
  have hsA : s < A := by
    by_contra hle; push Not at hle
    have : A ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hle 2
    omega
  have h2 : (s + 1) ^ 2 ≤ A ^ 2 := Nat.pow_le_pow_left hsA 2
  have h4 : 2 ^ 2 ≤ A ^ 2 := Nat.pow_le_pow_left hA 2
  nlinarith

/-- `χ_A(g) > ψ_A(g)`. -/
theorem yn_lt_xn {A : ℕ} (hA : 1 < A) (g : ℕ) : yn hA g < xn hA g := by
  have h := pell_eq hA g
  change xn hA g * xn hA g - (A * A - 1) * yn hA g * yn hA g = 1 at h
  have h3 : 3 ≤ A * A - 1 := by have := Nat.mul_le_mul hA hA; omega
  have this : (A * A - 1) * yn hA g * yn hA g ≥ 3 * (yn hA g * yn hA g) := by
    rw [mul_assoc]; exact Nat.mul_le_mul_right _ h3
  have e : xn hA g * xn hA g = (A * A - 1) * yn hA g * yn hA g + 1 := by omega
  by_contra hle; push Not at hle
  have h4 : xn hA g * xn hA g ≤ yn hA g * yn hA g := Nat.mul_le_mul hle hle
  omega

set_option maxHeartbeats 1000000 in
/-- The relaxed auxiliary norm with `c = ψ_A(p)` and `c > A (A² − 1)²` forces the
integral solution `f = χ_A(m)`, `i c² = (A² − 1) ψ_A(m)` with `p ∣ m` and `c ∣ m`. -/
theorem relaxed_aux {A c p f i : ℕ} (hA : 1 < A) (hp : 0 < p) (hcp : c = yn hA p)
    (hi : 0 < i) (hf0 : 0 < f)
    (E16 : (i * c ^ 2) ^ 2 = (A ^ 2 - 1) * (f ^ 2 - 1))
    (hbig : A * (A ^ 2 - 1) ^ 2 < c) :
    ∃ m, f = xn hA m ∧ p ∣ m ∧ c ∣ m ∧ i * c ^ 2 = (A ^ 2 - 1) * yn hA m := by
  -- notation
  have hA2 : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hD3 : 3 ≤ A ^ 2 - 1 := by have h := Nat.pow_le_pow_left hA 2; norm_num at h; omega
  have hc0 : 0 < c := by rw [hcp]; exact lt_of_lt_of_le hp (yn_ge_n hA p)
  set D := A ^ 2 - 1 with hDdef
  set R := i * c ^ 2 with hRdef
  have hR0 : 0 < R := by positivity
  -- Step 1: `D = s₀² d₀`, `d₀` squarefree, `d₀ ≥ 2`
  obtain ⟨d₀, s₀, hd₀, hs₀, hDs, hsqf⟩ := Nat.sq_mul_squarefree_of_pos (by omega : 0 < D)
  have hd₀1 : d₀ ≠ 1 := by
    intro h1; rw [h1, mul_one] at hDs
    exact sq_sub_one_not_square hA hDs
  have hd₀2 : 2 ≤ d₀ := by omega
  have hnsq : ¬IsSquare (d₀ : ℤ) := by
    rintro ⟨t, ht⟩
    have ht' : d₀ = t.natAbs * t.natAbs := by
      have := congrArg Int.natAbs ht
      simpa [Int.natAbs_mul] using this
    have hu : IsUnit t.natAbs := hsqf t.natAbs (by rw [← ht'])
    rw [Nat.isUnit_iff] at hu
    rw [hu] at ht'
    omega
  -- Step 2: the fundamental unit `ε = (F, y₀)` of `x² − d₀ y² = 1`
  obtain ⟨ε, hε⟩ := Pell.IsFundamental.exists_of_not_isSquare (by exact_mod_cast hd₀ : (0 : ℤ) < d₀) hnsq
  obtain ⟨F, hFx⟩ : ∃ F : ℕ, (F : ℤ) = ε.x := ⟨ε.x.toNat, Int.toNat_of_nonneg hε.x_pos.le⟩
  have hF : 1 < F := by have := hε.1; omega
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ℕ, (y₀ : ℤ) = ε.y := ⟨ε.y.toNat, Int.toNat_of_nonneg hε.2.1.le⟩
  have hy₀0 : 0 < y₀ := by have := hε.2.1; omega
  have hεprop : (F : ℤ) ^ 2 - d₀ * (y₀ : ℤ) ^ 2 = 1 := by
    have := ε.prop; rw [← hFx, ← hy₀] at this; exact this
  have hFF : F * F - 1 = d₀ * (y₀ * y₀) := by
    have h1 : (F : ℤ) * F = d₀ * (y₀ * y₀) + 1 := by linear_combination hεprop
    have h2 : F * F = d₀ * (y₀ * y₀) + 1 := by exact_mod_cast h1
    omega
  -- Step 3: `(A, s₀) = ε^e`, so `A = χ_F(e)` and `s₀ = y₀ ψ_F(e)`
  have hαprop : (A : ℤ) ^ 2 - d₀ * (s₀ : ℤ) ^ 2 = 1 := by
    have h1 : A ^ 2 = s₀ ^ 2 * d₀ + 1 := by omega
    have h2 : ((A ^ 2 : ℕ) : ℤ) = ((s₀ ^ 2 * d₀ + 1 : ℕ) : ℤ) := by rw [h1]
    push_cast at h2; linear_combination h2
  obtain ⟨e, he⟩ := hε.eq_pow_of_nonneg (a := Pell.Solution₁.mk (A : ℤ) s₀ hαprop)
    (by rw [Pell.Solution₁.x_mk]; exact_mod_cast (show 0 < A by omega))
    (by rw [Pell.Solution₁.y_mk]; positivity)
  obtain ⟨hex, hey⟩ := pow_x_y ε hF hFx.symm e
  rw [← he, Pell.Solution₁.x_mk] at hex
  rw [← he, Pell.Solution₁.y_mk, ← hy₀] at hey
  have hAe : A = xn hF e := by exact_mod_cast hex
  have hs₀e : s₀ = y₀ * yn hF e := by exact_mod_cast hey
  subst hAe
  set A := xn hF e with hAdef
  set S := yn hF e with hSdef
  have he0 : 0 < e := by
    by_contra h0; push Not at h0
    have h1 : e = 0 := by omega
    have h2 : A = 1 := by rw [hAdef, h1, xn_zero]
    omega
  have hS0 : 0 < S := by rw [hSdef]; exact lt_of_lt_of_le he0 (yn_ge_n hF e)
  have hSA : S < A := yn_lt_xn hF e
  -- the composition identities for the parameter `A = χ_F(e)`
  have hcomp := comp_xn_yn hF e hA
  have hSc : S * c = yn hF (e * p) := by rw [hcp, mul_comm]; exact (hcomp p).2
  -- `D = (F² − 1) S²`
  have hDT : D = (F * F - 1) * S * S := by
    rw [hFF, ← hDs, hs₀e]; ring
  -- Step 4: the relaxed solution `(f, y) = ε^n`
  have hRsq : R ^ 2 = D * (f ^ 2 - 1) := E16
  have hs₀R : s₀ ∣ R := by
    have : s₀ ^ 2 ∣ R ^ 2 := by rw [hRsq, ← hDs]; exact Dvd.intro (d₀ * (f ^ 2 - 1)) (by ring)
    exact (Nat.pow_dvd_pow_iff two_ne_zero).1 this
  obtain ⟨R₁, hR₁⟩ := hs₀R
  have hd₀R₁ : d₀ ∣ R₁ := by
    have h1 : d₀ * (f ^ 2 - 1) = R₁ ^ 2 := by
      have : s₀ ^ 2 * (d₀ * (f ^ 2 - 1)) = s₀ ^ 2 * R₁ ^ 2 := by
        rw [← mul_assoc, hDs, ← hRsq, hR₁]; ring
      exact Nat.eq_of_mul_eq_mul_left (by positivity) this
    exact (hsqf.dvd_pow_iff_dvd two_ne_zero).1 ⟨_, h1.symm⟩
  obtain ⟨y, hy⟩ := hd₀R₁
  have hfy : f ^ 2 - 1 = d₀ * y ^ 2 := by
    have : s₀ ^ 2 * (d₀ * (f ^ 2 - 1)) = s₀ ^ 2 * (d₀ * (d₀ * y ^ 2)) := by
      rw [← mul_assoc, hDs, ← hRsq, hR₁, hy]; ring
    have := Nat.eq_of_mul_eq_mul_left (by positivity) this
    exact Nat.eq_of_mul_eq_mul_left hd₀ this
  have hβprop : (f : ℤ) ^ 2 - d₀ * (y : ℤ) ^ 2 = 1 := by
    have hf1 : 1 ≤ f ^ 2 := Nat.one_le_pow _ _ hf0
    have h2 : ((f ^ 2 - 1 : ℕ) : ℤ) = ((d₀ * y ^ 2 : ℕ) : ℤ) := by rw [hfy]
    push_cast [Nat.cast_sub hf1] at h2; linear_combination h2
  obtain ⟨n, hn⟩ := hε.eq_pow_of_nonneg (a := Pell.Solution₁.mk (f : ℤ) y hβprop)
    (by rw [Pell.Solution₁.x_mk]; exact_mod_cast hf0)
    (by rw [Pell.Solution₁.y_mk]; positivity)
  obtain ⟨hnx, hny⟩ := pow_x_y ε hF hFx.symm n
  rw [← hn, Pell.Solution₁.x_mk] at hnx
  rw [← hn, Pell.Solution₁.y_mk, ← hy₀] at hny
  have hfn : f = xn hF n := by exact_mod_cast hnx
  have hyn : y = y₀ * yn hF n := by exact_mod_cast hny
  -- `R = T ψ_F(n)` with `T = (F² − 1) S`
  set T := (F * F - 1) * S with hTdef
  have hRT : R = T * yn hF n := by
    rw [hR₁, hy, hyn, hs₀e, hTdef, hFF]; ring
  have hDTS : D = T * S := by rw [hDT]
  -- Step 5: `c ≤ T · gcd(ψ_F(n), ψ_F(ep))`
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, xn_zero] at hfn
      have : f ^ 2 - 1 = 0 := by rw [hfn]; norm_num
      rw [this] at hRsq
      simp at hRsq; omega
    · exact h
  have hcR : c ∣ T * yn hF n := by
    rw [← hRT, hRdef]; exact Dvd.intro (i * c) (by ring)
  have hcDc : c ∣ T * yn hF (e * p) := by
    rw [← hSc]; exact Dvd.intro (T * S) (by ring)
  have hgcd : c ∣ T * Nat.gcd (yn hF n) (yn hF (e * p)) := by
    rw [← Nat.gcd_mul_left]; exact Nat.dvd_gcd hcR hcDc
  rw [yn_gcd] at hgcd
  set g := Nat.gcd n (e * p) with hgdef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hn0
  have hT0 : 0 < T := Nat.mul_pos (by nlinarith) hS0
  have hyg0 : 0 < yn hF g := lt_of_lt_of_le hg0 (yn_ge_n hF g)
  have hcle : c ≤ T * yn hF g := Nat.le_of_dvd (Nat.mul_pos hT0 hyg0) hgcd
  -- Step 6: `ep ∣ n`
  have hep : e * p ∣ n := by
    by_contra hnd
    have hg_dvd : g ∣ e * p := Nat.gcd_dvd_right n (e * p)
    have hg_ne : g ≠ e * p := by
      intro h; apply hnd; rw [← h]; exact Nat.gcd_dvd_left n (e * p)
    have h2g : 2 * g ≤ e * p := by
      obtain ⟨k, hk⟩ := hg_dvd
      have hk1 : k ≠ 1 := by intro h; rw [h, mul_one] at hk; exact hg_ne hk.symm
      have hk0 : k ≠ 0 := by
        intro h; rw [h, mul_zero] at hk
        have : 0 < e * p := Nat.mul_pos he0 hp
        omega
      have hk2 : 2 ≤ k := by omega
      rw [hk]
      calc 2 * g = g * 2 := by ring
        _ ≤ g * k := Nat.mul_le_mul_left g hk2
    -- `2 ψ_F(g)² < ψ_F(2g) ≤ ψ_F(ep) = S c`
    have h2y : 2 * yn hF g ^ 2 < yn hF (2 * g) := by
      have h := yn_add hF g g
      rw [show g + g = 2 * g by ring] at h
      rw [h]
      have hlt := yn_lt_xn hF g
      have hyg : 0 < yn hF g := lt_of_lt_of_le hg0 (yn_ge_n hF g)
      have h1 : yn hF g * yn hF g < xn hF g * yn hF g := Nat.mul_lt_mul_of_pos_right hlt hyg
      have e1 : xn hF g * yn hF g + yn hF g * xn hF g = 2 * (xn hF g * yn hF g) := by ring
      have e2 : 2 * yn hF g ^ 2 = 2 * (yn hF g * yn hF g) := by ring
      omega
    have h3 : yn hF (2 * g) ≤ S * c := by
      rw [hSc]; exact (strictMono_y hF).monotone h2g
    -- combine with `c ≤ T ψ_F(g) ≤ D ψ_F(g)` and `S < A`
    have hTD : T ≤ D := by rw [hDTS]; exact Nat.le_mul_of_pos_right _ hS0
    have hcD : c ≤ D * yn hF g := le_trans hcle (Nat.mul_le_mul_right _ hTD)
    have hc2 : c * c ≤ (D * yn hF g) * (D * yn hF g) := Nat.mul_le_mul hcD hcD
    have hA' : S < A := hSA
    -- `2 c² ≤ 2 D² ψ_F(g)² < D² S c < D² A c`, so `2 c < A D²`, contradicting `A D² < c`
    have key : 2 * (c * c) < A * D ^ 2 * c := by
      calc 2 * (c * c) ≤ 2 * ((D * yn hF g) * (D * yn hF g)) := by omega
        _ = D ^ 2 * (2 * yn hF g ^ 2) := by ring
        _ < D ^ 2 * (S * c) := by
            apply Nat.mul_lt_mul_of_pos_left (lt_of_lt_of_le h2y h3) (by positivity)
        _ ≤ D ^ 2 * (A * c) := by
            apply Nat.mul_le_mul_left; exact Nat.mul_le_mul_right _ hA'.le
        _ = A * D ^ 2 * c := by ring
    have key' : 2 * c * c < A * D ^ 2 * c := by rw [mul_assoc]; exact key
    have : 2 * c < A * D ^ 2 := Nat.lt_of_mul_lt_mul_right key'
    omega
  -- `n = e m` with `p ∣ m`
  obtain ⟨k, hk⟩ := hep
  set m := p * k with hmdef
  have hnm : n = e * m := by rw [hk, hmdef]; ring
  have hfm : f = xn hA m := by rw [hfn, hnm, (hcomp m).1]
  have hRm : R = D * yn hA m := by
    rw [hRT, hnm, ← (hcomp m).2, hDTS]; ring
  refine ⟨m, hfm, ⟨k, hmdef⟩, ?_, hRm⟩
  -- Step 7: `c ∣ m`
  -- `ψ_A(pk) ≡ k χ_A(p)^(k−1) ψ_A(p) (mod ψ_A(p)³)`
  have hmod := (xy_modEq_yn hA p k).2
  rw [← hcp] at hmod
  have hd0 : Nat.Coprime c (xn hA p) := by rw [hcp]; exact (xy_coprime hA p).symm
  obtain ⟨t, ht⟩ := Nat.modEq_iff_dvd.1 hmod
  -- `c² ∣ D ψ_A(m)` gives `c ∣ D k χ_A(p)^(k−1)`, hence `c ∣ D k`
  have hc2R : (c : ℤ) ^ 2 ∣ (D : ℤ) * yn hA m := by
    have : c ^ 2 ∣ D * yn hA m := by rw [← hRm, hRdef]; exact Dvd.intro_left i rfl
    exact_mod_cast this
  have hcDk' : (c : ℤ) ∣ (D : ℤ) * (k * xn hA p ^ (k - 1)) := by
    have hyn : (yn hA m : ℤ) = k * xn hA p ^ (k - 1) * c - c ^ 3 * t := by
      push_cast at ht; rw [hmdef]; linarith
    have h1 : (c : ℤ) * c ∣ (c : ℤ) * (D * (k * xn hA p ^ (k - 1)) - D * c ^ 2 * t) := by
      have e : (c : ℤ) * (D * (k * xn hA p ^ (k - 1)) - D * c ^ 2 * t) = D * yn hA m := by
        rw [hyn]; ring
      rw [e, ← sq]; exact hc2R
    have h2 : (c : ℤ) ∣ D * (k * xn hA p ^ (k - 1)) - D * c ^ 2 * t :=
      (mul_dvd_mul_iff_left (by exact_mod_cast hc0.ne')).1 h1
    have h3 : (c : ℤ) ∣ D * c ^ 2 * t := Dvd.intro (D * c * t) (by ring)
    have := dvd_add h2 h3
    rwa [sub_add_cancel] at this
  have hcDk : c ∣ D * k := by
    have h1 : c ∣ D * k * xn hA p ^ (k - 1) := by
      have : (c : ℤ) ∣ ((D * k * xn hA p ^ (k - 1) : ℕ) : ℤ) := by
        push_cast
        rw [show (D : ℤ) * k * xn hA p ^ (k - 1) = D * (k * xn hA p ^ (k - 1)) by ring]
        exact hcDk'
      exact_mod_cast this
    exact (Nat.Coprime.pow_right (k - 1) hd0).dvd_of_dvd_mul_right h1
  -- `c ≡ p A^(p−1) (mod D)`, so `g₀ = gcd c D` divides `p`
  have hcmod : c ≡ p * A ^ (p - 1) [MOD D] := by
    have := (xn_yn_modEq_pow hA (p - 1)).2
    rw [Nat.sub_add_cancel hp, ← hcp] at this
    rw [hDdef, sq]; exact this
  have hAD : Nat.Coprime A D := by
    show Nat.gcd A D = 1
    have h1 : Nat.gcd A D ∣ A * A := dvd_mul_of_dvd_left (Nat.gcd_dvd_left A D) A
    have h2 : Nat.gcd A D ∣ D := Nat.gcd_dvd_right A D
    have h3 : Nat.gcd A D ∣ A * A - D := Nat.dvd_sub h1 h2
    have h4 : A * A - D = 1 := by
      have : 1 ≤ A * A := Nat.one_le_iff_ne_zero.2 (by positivity)
      rw [hDdef, sq]; omega
    rw [h4] at h3
    exact Nat.dvd_one.1 h3
  set g₀ := Nat.gcd c D with hg₀
  have hg₀c : g₀ ∣ c := Nat.gcd_dvd_left c D
  have hg₀D : g₀ ∣ D := Nat.gcd_dvd_right c D
  have hg₀0 : 0 < g₀ := Nat.gcd_pos_of_pos_left _ hc0
  have hg₀p : g₀ ∣ p := by
    have h1 : (D : ℤ) ∣ ((p * A ^ (p - 1) : ℕ) : ℤ) - (c : ℤ) := Nat.modEq_iff_dvd.1 hcmod
    have h2 : (g₀ : ℤ) ∣ ((p * A ^ (p - 1) : ℕ) : ℤ) - (c : ℤ) :=
      dvd_trans (by exact_mod_cast hg₀D) h1
    have h3 : (g₀ : ℤ) ∣ (c : ℤ) := by exact_mod_cast hg₀c
    have h4 : (g₀ : ℤ) ∣ ((p * A ^ (p - 1) : ℕ) : ℤ) := by
      have := dvd_add h2 h3; rwa [sub_add_cancel] at this
    have h5 : g₀ ∣ p * A ^ (p - 1) := by exact_mod_cast h4
    have hcop : Nat.Coprime g₀ (A ^ (p - 1)) :=
      Nat.Coprime.pow_right _ (Nat.Coprime.coprime_dvd_left hg₀D hAD.symm)
    exact hcop.dvd_of_dvd_mul_right h5
  have hcop' : Nat.Coprime (c / g₀) (D / g₀) := Nat.coprime_div_gcd_div_gcd hg₀0
  have hc'k : c / g₀ ∣ k := by
    have h1 : g₀ * (c / g₀) ∣ g₀ * (D / g₀ * k) := by
      rw [Nat.mul_div_cancel' hg₀c, ← mul_assoc, Nat.mul_div_cancel' hg₀D]; exact hcDk
    have h2 : c / g₀ ∣ D / g₀ * k := Nat.dvd_of_mul_dvd_mul_left hg₀0 h1
    exact hcop'.dvd_of_dvd_mul_left h2
  rw [hmdef]
  calc c = g₀ * (c / g₀) := (Nat.mul_div_cancel' hg₀c).symm
    _ ∣ p * k := mul_dvd_mul hg₀p hc'k

end Jones1980
