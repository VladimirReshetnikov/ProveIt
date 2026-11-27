import IPRADerivations.DiophantineNumberTheory.Coprime

/-!
# Primitive Pythagorean triples

Packet: `diophantine-number-theory/flt_ipra`, Lemma `lem:pythagoras`.

Let `A, H ≥ 1`, `B = 2H`, `A² + B² = C²` and `gcd(A, B) = 1`. Then `A = 2a + 1` and
`C = 2c + 1` are odd, `a < c`, and with `U = c + a + 1 = (C + A)/2`,
`V = c - a = (C - A)/2`:

* `U V = H²`, `gcd(U, V) = 1`, so `U = m²` and `V = n²` with the explicit parameters
  `m = gcd(U, H)`, `n = gcd(V, H)` (`square_of_coprime`; no search is needed);
* `A + n² = m²`, `H = m n` (so `B = 2mn`), `C = m² + n²`, `gcd(m, n) = 1`, `n ≥ 1`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.Pythagoras

open_ipra exports
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `U = (C + A)/2`. -/
abbrev pU (A C : PTm n) : PTm n := half C + half A + one
/-- `V = (C - A)/2`. -/
abbrev pV (A C : PTm n) : PTm n := succ (monus (half C) (succ (half A)))
/-- `m = gcd(U, H)`. -/
abbrev pm (A H C : PTm n) : PTm n := gcd (pU A C) H
/-- `n = gcd(V, H)`. -/
abbrev pn (A H C : PTm n) : PTm n := gcd (pV A C) H

theorem two_pos : Γ ⊢[PRAAx] (two : PTm n) ≐ succ (pred two) := congrSucc (pred_succ _).eqSymm

/-! ## The algebra -/

theorem alg_odd {A C H a k : PTm n} (hE : Γ ⊢[PRAAx] A * A + (two * H) * (two * H) ≐ C * C)
    (eA : Γ ⊢[PRAAx] A ≐ two * a + one) (eC : Γ ⊢[PRAAx] C ≐ two * k) :
    Γ ⊢[PRAAx] two * (two * (k * k)) ≐ two * (two * (a * a) + two * a + two * (H * H)) + one := by
  ipra_lc -natEq hE + (Groth.ι (IPRA.Q.mk Γ A) + 2 * Groth.ι (IPRA.Q.mk Γ a) + 1) * natEq eA -
    (Groth.ι (IPRA.Q.mk Γ C) + 2 * Groth.ι (IPRA.Q.mk Γ k)) * natEq eC

theorem alg_UV {A C H a c V : PTm n} (hE : Γ ⊢[PRAAx] A * A + (two * H) * (two * H) ≐ C * C)
    (eA : Γ ⊢[PRAAx] A ≐ two * a + one) (eC : Γ ⊢[PRAAx] C ≐ two * c + one) (ec : Γ ⊢[PRAAx] c ≐ a + V) :
    Γ ⊢[PRAAx] (two * two) * ((c + a + one) * V) ≐ (two * two) * (H * H) := by
  ipra_lc -natEq hE + (Groth.ι (IPRA.Q.mk Γ A) + 2 * Groth.ι (IPRA.Q.mk Γ a) + 1) * natEq eA -
    (Groth.ι (IPRA.Q.mk Γ C) + 2 * Groth.ι (IPRA.Q.mk Γ c) + 1) * natEq eC -
    4 * (Groth.ι (IPRA.Q.mk Γ c) + Groth.ι (IPRA.Q.mk Γ a) + 1) * natEq ec

/-! ## The parametrization -/

theorem pyth_at {A H C : PTm n} (hA : Γ ⊢[PRAAx] A ≐ succ (pred A)) (hH : Γ ⊢[PRAAx] H ≐ succ (pred H))
    (hE : Γ ⊢[PRAAx] A * A + (two * H) * (two * H) ≐ C * C) (hg : Γ ⊢[PRAAx] gcd A (two * H) ≐ one) :
    Γ ⊢[PRAAx] (A + pn A H C * pn A H C ≐ pm A H C * pm A H C) ⋏ (H ≐ pm A H C * pn A H C) ⋏
      (C ≐ pm A H C * pm A H C + pn A H C * pn A H C) ⋏ (gcd (pm A H C) (pn A H C) ≐ one) ⋏
      (pn A H C ≐ succ (pred (pn A H C))) := by
  have hB := pos_mul two_pos hH
  -- `A` is odd: otherwise `2` divides `gcd(A, B) = 1`.
  have oddA : Γ ⊢[PRAAx] A ≐ two * half A + one := by
    refine .orE (even_or_odd A) ?_ Prf.hyp0
    have d := gcd_greatest' (Γ := (A ≐ two * half A) :: Γ) (a := A) (b := two * H) two_pos.wk
      (dvd_of_eq' two_pos.wk Prf.hyp0) (dvd_of_eq' (w := H) two_pos.wk (.eqRefl _))
    have e := succ_inj (eq_one_of_dvd_one two_pos.wk (dvd_congr hg.wk d))
    exact succ_ne_zero' _ e
  -- `C` is odd: `C²` is odd.
  have oddC : Γ ⊢[PRAAx] C ≐ two * half C + one := by
    refine .orE (even_or_odd C) ?_ Prf.hyp0
    exact even_ne_odd _ (alg_odd hE.wk oddA.wk Prf.hyp0)
  -- `a < c`, since `A < C`.
  have hlt : Γ ⊢[PRAAx] lt (half A) (half C) := by
    refine .orE (lt_or_le (half A) (half C)) Prf.hyp0 ?_
    have w := eq_add_of_le (Prf.hyp0 : (le (half C) (half A) :: Γ) ⊢[PRAAx] _)
    have hCA : (le (half C) (half A) :: Γ) ⊢[PRAAx] le C A := by
      refine le_of_eq_add (d := two * monus (half A) (half C)) ?_
      refine withEq oddA.wk fun e₁ => withEq oddC.wk fun e₂ => withEq w fun e₃ => ?_
      apply deriveNat; ipra_simps; rw [e₁, e₂, e₃]; ring
    have hAC : (le (half C) (half A) :: Γ) ⊢[PRAAx] lt (A * A) (C * C) := by
      refine le_of_eq_add (d := pred ((two * H) * (two * H))) ?_
      refine withEq hE.wk fun e₁ => withEq hB.wk fun e₂ => ?_
      ipra_lc -e₁ + natEq (pos_mul hB.wk hB.wk)
    exact le_lt_absurd _ (sq_le_sq hCA) hAC
  have ec : Γ ⊢[PRAAx] half C ≐ half A + pV A C :=
    (eq_add_of_le hlt).eqTrans (by ipra_ring)
  have hV : Γ ⊢[PRAAx] pV A C ≐ succ (pred (pV A C)) := congrSucc (pred_succ _).eqSymm
  have hU : Γ ⊢[PRAAx] pU A C ≐ succ (pred (pU A C)) :=
    eq_succ_pred (y := half C + half A) (by ipra_ring)
  have eUV := mul_cancel (pos_mul two_pos two_pos) (alg_UV hE oddA oddC ec)
  have AUV : Γ ⊢[PRAAx] A + pV A C ≐ pU A C := by
    refine withEq oddA fun e₁ => withEq ec fun e₂ => ?_
    apply deriveNat; ipra_simps; rw [e₁, e₂]; ring
  have CUV : Γ ⊢[PRAAx] C ≐ pU A C + pV A C := by
    refine withEq oddC fun e₁ => withEq ec fun e₂ => ?_
    apply deriveNat; ipra_simps; rw [e₁, e₂]; ring
  -- `gcd(U, V) = 1`: a common divisor divides `A`, `C`, hence `B²`, and `gcd(A, B²) = 1`.
  have hUV : Γ ⊢[PRAAx] gcd (pU A C) (pV A C) ≐ one := by
    have hd := gcd_pos (B := pV A C) hU
    have hdd := gcd_dvd' (b := pV A C) hU
    have dA := dvd_sub' hd (dvd_congr AUV.eqSymm (Prf.andE₁ hdd)) (Prf.andE₂ hdd)
    have dC := dvd_congr CUV.eqSymm (dvd_add' hd (Prf.andE₁ hdd) (Prf.andE₂ hdd))
    have dBB := dvd_sub' hd (dvd_congr ((add_comm _ _).eqTrans hE).eqSymm (dvd_mul' hd C dC))
      (dvd_mul' hd A dA)
    exact eq_one_of_coprime_dvd hd (coprime_dvd_left hd dA (coprime_mul hA hg hg)) dBB
  -- `U = m²`, `V = n²`.
  have eU := square_of_coprime hU hUV eUV
  have eV := square_of_coprime hV (gcd_comm_one hV hUV) ((mul_comm _ _).eqTrans eUV)
  have hm := gcd_pos (B := H) hU
  have hn := gcd_pos (B := H) hV
  have eH : Γ ⊢[PRAAx] H ≐ pm A H C * pn A H C := by
    refine sq_inj ?_
    refine withEq eUV fun e₁ => withEq eU fun e₂ => withEq eV fun e₃ => ?_
    apply deriveNat; ipra_simps; rw [← e₁, e₂, e₃]; ring
  have hmn : Γ ⊢[PRAAx] gcd (pm A H C) (pn A H C) ≐ one := by
    have hd := gcd_pos (B := pn A H C) hm
    have hdd := gcd_dvd' (b := pn A H C) hm
    have dU := dvd_congr eU.eqSymm (dvd_mul' hd _ (Prf.andE₁ hdd))
    have dV := dvd_congr eV.eqSymm (dvd_mul' hd _ (Prf.andE₂ hdd))
    exact eq_one_of_dvd_one hd (dvd_congr hUV (gcd_greatest' hd dU dV))
  refine .andI ((congrAdd (.eqRefl _) eV.eqSymm).eqTrans (AUV.eqTrans eU)) (.andI eH (.andI ?_ (.andI hmn hn)))
  exact CUV.eqTrans (congrAdd eU eV)

/-- Variables `0 = A - 1`, `1 = H - 1`, `2 = C`, with `B = 2H`. -/
abbrev pythFormula : Fm PTm 3 :=
  gcd (succ (var 0)) (two * succ (var 1)) ≐ one ⟶
    succ (var 0) * succ (var 0) + (two * succ (var 1)) * (two * succ (var 1)) ≐ var 2 * var 2 ⟶
    (succ (var 0) + pn (succ (var 0)) (succ (var 1)) (var 2) * pn (succ (var 0)) (succ (var 1)) (var 2) ≐
        pm (succ (var 0)) (succ (var 1)) (var 2) * pm (succ (var 0)) (succ (var 1)) (var 2)) ⋏
      (succ (var 1) ≐ pm (succ (var 0)) (succ (var 1)) (var 2) * pn (succ (var 0)) (succ (var 1)) (var 2)) ⋏
      (var 2 ≐ pm (succ (var 0)) (succ (var 1)) (var 2) * pm (succ (var 0)) (succ (var 1)) (var 2) +
        pn (succ (var 0)) (succ (var 1)) (var 2) * pn (succ (var 0)) (succ (var 1)) (var 2)) ⋏
      (gcd (pm (succ (var 0)) (succ (var 1)) (var 2)) (pn (succ (var 0)) (succ (var 1)) (var 2)) ≐ one) ⋏
      (pn (succ (var 0)) (succ (var 1)) (var 2) ≐ succ (pred (pn (succ (var 0)) (succ (var 1)) (var 2))))

theorem pythagoras : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 pythFormula :=
  closeUniv 3 (.impI (.impI (pyth_at (congrSucc (pred_succ _).eqSymm) (congrSucc (pred_succ _).eqSymm)
    Prf.hyp0 Prf.hyp1)))

end LeanProofs.IPRA.DiophantineNumberTheory.Pythagoras
