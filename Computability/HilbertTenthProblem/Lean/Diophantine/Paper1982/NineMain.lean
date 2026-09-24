import Diophantine.Paper1982.NinePoly

/-!
# Jones 1982, §3: the nine unknowns

At a natural point the polynomial quantities of `NinePoly` are those of `NineReduce` and
`NineRatio`; combining the three steps gives Matijasevič's reduction to nine unknowns.
-/

namespace Jones1982.Nine

open Diophantine MvPolynomial

variable {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ} {z y : ℕ}


/-- At a natural point, the quantities are those of `NineReduce` and `NineRatio`, except that
the code `R` is still the integer polynomial. -/
theorem varsOf_nat' {u : ℕ} (hI : Index ν P z u y) {x : ℕ} (hx : 0 < x) (a : Fin 9 → ℕ) :
    varsOf ν P z y (fun k => ((Fin.cons x a : Fin 10 → ℕ) k : ℤ)) =
      { Vars.ofNat 0 (qN ν (bN x y (a 0)) ^ 16) (bN x y (a 0)) (a 1 + 1)
          (32 * bN x y (a 0) * (bN x y (a 0) ^ 5) ^ (5 ^ ν)) (a 2 + 1) (a 3 + 1) (a 4 + 1) (a 5)
          (a 6 + 1) (a 7 + 1) with
        R := rPolynomial x z (bN x y (a 0)) (eN ν P z (bN x y (a 0))) (a 1 + 1)
          (lN ν (bN x y (a 0))) (qN ν (bN x y (a 0)) ^ 16) (qN ν (bN x y (a 0)))
          (θN z (bN x y (a 0))) (lamN ν (bN x y (a 0))) } := by
  set v : Fin 10 → ℤ := fun k => ((Fin.cons x a : Fin 10 → ℕ) k : ℤ) with hv
  have h0 : v 0 = x := rfl
  have h1 : v 1 = a 0 := rfl
  have h2 : v 2 = a 1 := rfl
  have h3 : v 3 = a 2 := rfl
  have h4 : v 4 = a 3 := rfl
  have h5 : v 5 = a 4 := rfl
  have h6 : v 6 = a 5 := rfl
  have h7 : v 7 = a 6 := rfl
  have h8 : v 8 = a 7 := rfl
  have hb : (x : ℤ) * y + 1 + (a 0 : ℤ) = (bN x y (a 0) : ℤ) := by simp [bN]
  have h2z := two_z_lt hI hx (a 0)
  have hθ : ((bN x y (a 0) : ℤ)) ^ 5 - 2 * z = (θN z (bN x y (a 0)) : ℤ) := by
    rw [θN]; push_cast [h2z.le]; ring
  simp only [varsOf, Vars.ofNat, h0, h1, h2, h3, h4, h5, h6, h7, h8, hb, hθ, ← eN_eq hI,
    ← lN_eq, ← lamN_eq, rPolynomial_eq_rZ, qN, Vars.mk.injEq]
  push_cast
  repeat' constructor

theorem wset_iff_nine (hν : 1 ≤ ν) (hP : P.totalDegree ≤ 4) (hnorm : Normalized P) {u : ℕ}
    (hI : Index ν P z u y) {x : ℕ} (hx : 0 < x) :
    Wset P x ↔ ∃ a : Fin 9 → ℕ,
      nineValue ν P z y (fun k => ((Fin.cons x a : Fin 10 → ℕ) k : ℤ)) = 0 := by
  constructor
  · intro hW
    obtain ⟨ε, g, k, hg, hb, hgb, hdvd⟩ := reduced_of_mem hν hP hnorm hI hx hW
    have hb0 : 0 < bN x y ε := by rw [bN]; omega
    have hBpos : 0 < bN x y ε * (bN x y ε ^ 5) ^ (5 ^ ν) := by positivity
    have e4 : 4 * bN x y ε * (bN x y ε ^ 5) ^ (5 ^ ν) =
        4 * (bN x y ε * (bN x y ε ^ 5) ^ (5 ^ ν)) := by ring
    have hgb4 : g < 4 * bN x y ε * (bN x y ε ^ 5) ^ (5 ^ ν) := by rw [e4]; omega
    obtain ⟨hN8, hR8, hbN, hbR, hReq⟩ := sizes_of_reduced hν hI hx hg hgb4
    obtain ⟨h, s, w, φ, i, j, hh, hs, hw, hi, hj, hc⟩ := ratio_complete hR8 hN8 hbR hb0 hbN
      (g := g) (G := 32 * bN x y ε * (bN x y ε ^ 5) ^ (5 ^ ν))
      (by have e32 : 32 * bN x y ε * (bN x y ε ^ 5) ^ (5 ^ ν) =
            32 * (bN x y ε * (bN x y ε ^ 5) ^ (5 ^ ν)) := by ring
          rw [e32]; omega) hdvd ⟨k, hb⟩
    obtain ⟨n, hn⟩ := (conds_iff_value _).1 hc
    refine ⟨![ε, g - 1, h - 1, s - 1, w - 1, φ, i - 1, j - 1, n], ?_⟩
    rw [nineValue, varsOf_nat' hI hx]
    have e1 : g - 1 + 1 = g := by omega
    have e2 : h - 1 + 1 = h := by omega
    have e3 : s - 1 + 1 = s := by omega
    have e4 : w - 1 + 1 = w := by omega
    have e6 : i - 1 + 1 = i := by omega
    have e7 : j - 1 + 1 = j := by omega
    have hV : { Vars.ofNat 0 (qN ν (bN x y ε) ^ 16) (bN x y ε) g
          (32 * bN x y ε * (bN x y ε ^ 5) ^ (5 ^ ν)) h s w φ i j with
        R := rPolynomial x z (bN x y ε) (eN ν P z (bN x y ε)) g (lN ν (bN x y ε))
          (qN ν (bN x y ε) ^ 16) (qN ν (bN x y ε)) (θN z (bN x y ε)) (lamN ν (bN x y ε)) } =
        Vars.ofNat (RN ν P x z (bN x y ε) g) (qN ν (bN x y ε) ^ 16) (bN x y ε) g
          (32 * bN x y ε * (bN x y ε ^ 5) ^ (5 ^ ν)) h s w φ i j := by
      simp only [Vars.ofNat, hReq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      e1, e2, e3, e4, e6, e7]
    have h9 : ((Fin.cons x ![ε, g - 1, h - 1, s - 1, w - 1, φ, i - 1, j - 1, n] :
        Fin 10 → ℕ) 9 : ℤ) = (n : ℤ) := rfl
    rw [hV, h9]
    exact hn
  · rintro ⟨a, ha⟩
    rw [nineValue, varsOf_nat' hI hx] at ha
    have hc := (conds_iff_value _).2 ⟨a 8, ha⟩
    have hb0 : 0 < bN x y (a 0) := by rw [bN]; omega
    have hG0 : 0 < 32 * bN x y (a 0) * (bN x y (a 0) ^ 5) ^ (5 ^ ν) := by positivity
    have hg8 := g_lt_of_marg _ (by simp only [Vars.ofNat]; exact_mod_cast hG0)
      (by simp only [Vars.ofNat]; positivity) hc.2.2.2
    simp only [Vars.ofNat] at hg8
    have hgb4 : a 1 + 1 < 4 * bN x y (a 0) * (bN x y (a 0) ^ 5) ^ (5 ^ ν) := by
      have : 8 * (a 1 + 1) < 32 * bN x y (a 0) * (bN x y (a 0) ^ 5) ^ (5 ^ ν) := by
        exact_mod_cast hg8
      have e32 : 32 * bN x y (a 0) * (bN x y (a 0) ^ 5) ^ (5 ^ ν) =
          32 * (bN x y (a 0) * (bN x y (a 0) ^ 5) ^ (5 ^ ν)) := by ring
      have e4 : 4 * bN x y (a 0) * (bN x y (a 0) ^ 5) ^ (5 ^ ν) =
          4 * (bN x y (a 0) * (bN x y (a 0) ^ 5) ^ (5 ^ ν)) := by ring
      rw [e32] at this; rw [e4]; omega
    obtain ⟨hN8, hR8, hbN, hbR, hReq⟩ := sizes_of_reduced hν hI hx (Nat.succ_pos _) hgb4
    have hV : { Vars.ofNat 0 (qN ν (bN x y (a 0)) ^ 16) (bN x y (a 0)) (a 1 + 1)
          (32 * bN x y (a 0) * (bN x y (a 0) ^ 5) ^ (5 ^ ν)) (a 2 + 1) (a 3 + 1) (a 4 + 1) (a 5)
          (a 6 + 1) (a 7 + 1) with
        R := rPolynomial x z (bN x y (a 0)) (eN ν P z (bN x y (a 0))) (a 1 + 1)
          (lN ν (bN x y (a 0))) (qN ν (bN x y (a 0)) ^ 16) (qN ν (bN x y (a 0)))
          (θN z (bN x y (a 0))) (lamN ν (bN x y (a 0))) } =
        Vars.ofNat (RN ν P x z (bN x y (a 0)) (a 1 + 1)) (qN ν (bN x y (a 0)) ^ 16) (bN x y (a 0))
          (a 1 + 1) (32 * bN x y (a 0) * (bN x y (a 0) ^ 5) ^ (5 ^ ν)) (a 2 + 1) (a 3 + 1)
          (a 4 + 1) (a 5) (a 6 + 1) (a 7 + 1) := by
      simp only [Vars.ofNat, hReq]
    rw [hV] at hc
    obtain ⟨hdvd, ⟨k, hk⟩, -⟩ := ratio_sound hR8 hN8 hbR hb0 hbN hG0 (Nat.succ_pos _)
      (Nat.succ_pos _) (Nat.succ_pos _) (Nat.succ_pos _) (Nat.succ_pos _) hc
    exact mem_of_reduced hν hP hI hx (Nat.succ_pos _) hk hgb4 hdvd

end Jones1982.Nine

namespace Jones1982

open Nine

/-- **§3: Matijasevič's reduction to nine unknowns**, for a Diophantine set given in Mathlib's
form. -/
theorem nine_unknowns_dioph {S : Set ℕ} (hS : Dioph {v : Unit → ℕ | v () ∈ S}) :
    ∃ M : MvPolynomial (Fin 10) ℤ, ∀ x : ℕ, 0 < x →
      (x ∈ S ↔ ∃ a : Fin 9 → ℕ,
        MvPolynomial.eval (fun k => ((Fin.cons x a : Fin 10 → ℕ) k : ℤ)) M = 0) := by
  obtain ⟨Q, hQ, hnorm, hrep⟩ := mathlib_dioph_quartic58 hS
  obtain ⟨z, u, y, -, -, -, hI⟩ := exists_index Q (by norm_num : 1 ≤ 58)
  obtain ⟨M, hM⟩ := polyFn_nineValue 58 Q z y
  refine ⟨M, fun x hx => ?_⟩
  rw [hrep x hx, wset_iff_nine (by norm_num) hQ hnorm hI hx]
  simp only [hM]

/-- **§3: Matijasevič's reduction to nine unknowns.** For every recursively enumerable set `S`
there is an integer polynomial `M` in `x` and nine unknowns such that, for every positive `x`,
`x ∈ S` iff `M(x, z₁, …, z₉) = 0` for some natural numbers `z₁, …, z₉`. -/
theorem nine_unknowns {S : Set ℕ} (hS : REPred S) :
    ∃ M : MvPolynomial (Fin 10) ℤ, ∀ x : ℕ, 0 < x →
      (x ∈ S ↔ ∃ a : Fin 9 → ℕ,
        MvPolynomial.eval (fun k => ((Fin.cons x a : Fin 10 → ℕ) k : ℤ)) M = 0) :=
  nine_unknowns_dioph (Diophantine.rePred_dioph hS)

end Jones1982
