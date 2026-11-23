import IPRADerivations.Core.OrderCertificates
import IPRADerivations.AnalyticNumberTheory.Mobius
import IPRADerivations.AnalyticNumberTheory.FactorialLambda
import IPRADerivations.AnalyticNumberTheory.ValuationAdd

/-!
# The Möbius function is multiplicative

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/elementary.tex`, Theorem
`el:mobiuscancel`, first assertion: "The function `μ` is multiplicative … For coprime inputs, their prime supports
are disjoint. If either has a repeated prime factor, the product does too and both sides of multiplicativity are
zero. Otherwise the numbers of prime factors add and their parity signs multiply."

`μ` is the signed pair `μ = μ⁺ − μ⁻` of `Mobius` (`μ⁺ = [s = 0][ω even]`, `μ⁻ = [s = 0][ω odd]`, with `ω_N` the
number of prime divisors and `s_N` the number of primes whose square divides, both below a prime bound `N`).
For `a, b ≥ 1` with `gcd(a, b) = 1` and every `N`:

* `cop_val`: for a prime `q`, `v_q(a) = 0` or `v_q(b) = 0`;
* **`om_cop`**, **`sq_cop`**: `ω_N(ab) = ω_N(a) + ω_N(b)` and `s_N(ab) = s_N(a) + s_N(b)`;
* `par_add`: the parity bits of a sum (`[x + y even] = [x even][y even] + [x odd][y odd]`, …);
* `eqb_add_zero`: `[x + y = 0] = [x = 0][y = 0]`;
* **`mu_mul`**: `μ⁺(ab) = μ⁺(a)μ⁺(b) + μ⁻(a)μ⁻(b)` and `μ⁻(ab) = μ⁺(a)μ⁻(b) + μ⁻(a)μ⁺(b)`, that is
  `μ(ab) = μ(a) μ(b)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.MobiusMult

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val isP isP_01 prime_of_isP)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (val_mul val_one)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationAdd (val_gcd_ge)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (om sq muP muN omB sqB inst2_om inst2_sq zero_mul_l congrSg
  congrEqb' congrVal par_succ shift_mul' one_ne_zero' zero_ne_one')
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (sum_add2)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_eq' zero_lt')
open LeanProofs.IPRA.AnalyticNumberTheory.PhiDouble (two_pos')
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Pointwise -/

/-- For `x = 0`: `sg(x + y) = sg x + sg y` and `sg(x + y ∸ 1) = sg(x ∸ 1) + sg(y ∸ 1)`. -/
theorem sg_add_l {x y : PTm n} (h : Γ ⊢[PRAAx] x ≐ zero) :
    Γ ⊢[PRAAx] (sg (x + y) ≐ sg x + sg y) ⋏ (sg (monus (x + y) one) ≐ sg (monus x one) + sg (monus y one)) := by
  have e : Γ ⊢[PRAAx] x + y ≐ y := (congrAdd h (.eqRefl _)).eqTrans (zero_add y)
  have s0 : Γ ⊢[PRAAx] sg x ≐ zero := (congrSg h).eqTrans sg_zero
  have m0 : Γ ⊢[PRAAx] sg (monus x one) ≐ zero := (congrSg ((congrMonus h (.eqRefl _)).eqTrans (zero_monus _))).eqTrans sg_zero
  exact .andI ((congrSg e).eqTrans ((zero_add _).eqSymm.eqTrans (congrAdd s0.eqSymm (.eqRefl _))))
    ((congrSg (congrMonus e (.eqRefl _))).eqTrans ((zero_add _).eqSymm.eqTrans (congrAdd m0.eqSymm (.eqRefl _))))

/-- For `y = 0`, the same. -/
theorem sg_add_r {x y : PTm n} (h : Γ ⊢[PRAAx] y ≐ zero) :
    Γ ⊢[PRAAx] (sg (x + y) ≐ sg x + sg y) ⋏ (sg (monus (x + y) one) ≐ sg (monus x one) + sg (monus y one)) := by
  have e : Γ ⊢[PRAAx] x + y ≐ x := (congrAdd (.eqRefl _) h).eqTrans (add_zero x)
  have s0 : Γ ⊢[PRAAx] sg y ≐ zero := (congrSg h).eqTrans sg_zero
  have m0 : Γ ⊢[PRAAx] sg (monus y one) ≐ zero := (congrSg ((congrMonus h (.eqRefl _)).eqTrans (zero_monus _))).eqTrans sg_zero
  exact .andI ((congrSg e).eqTrans ((add_zero _).eqSymm.eqTrans (congrAdd (.eqRefl _) s0.eqSymm)))
    ((congrSg (congrMonus e (.eqRefl _))).eqTrans ((add_zero _).eqSymm.eqTrans (congrAdd (.eqRefl _) m0.eqSymm)))

/-- Coprime numbers share no prime: `v_q(a) = 0` or `v_q(b) = 0`. -/
theorem cop_val {q a b : PTm n} (hq : Γ ⊢[PRAAx] prime q) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (hab : Γ ⊢[PRAAx] gcd a b ≐ one) : Γ ⊢[PRAAx] (val q a ≐ zero) ⋎ (val q b ≐ zero) := by
  refine .orE (zero_or_succ (val q a)) (.orI₁ Prf.hyp0) ?_
  refine .orI₂ ?_
  refine .orE (zero_or_succ (val q b)) Prf.hyp0 ?_
  let C : List (Fm PTm n) := (val q b ≐ succ (pred (val q b))) :: (val q a ≐ succ (pred (val q a))) :: Γ
  have xa := natEq (Prf.hyp1 : C ⊢[PRAAx] val q a ≐ succ (pred (val q a)))
  have xb := natEq (Prf.hyp0 : C ⊢[PRAAx] val q b ≐ succ (pred (val q b)))
  have h1 : C ⊢[PRAAx] le one (val q a) := by ipra_le 𝔞 (pred (val q a)) with xa
  have h2 : C ⊢[PRAAx] le one (val q b) := by ipra_le 𝔞 (pred (val q b)) with xb
  have h2q : C ⊢[PRAAx] le two q := Prf.andE₁ hq.wk.wk
  have g := val_gcd_ge h2q ha.wk.wk h1 h2
  have v1 : C ⊢[PRAAx] val q (gcd a b) ≐ zero := (congrVal (.eqRefl q) hab.wk.wk).eqTrans (val_one h2q)
  exact not_succ_le_self zero _ (le_congr (.eqRefl _) v1 g)

theorem distrib (i s t : PTm n) : Γ ⊢[PRAAx] i * (s + t) ≐ i * s + i * t := by
  apply deriveNat; ipra_simps; ring

theorem om_pt_cop {q a b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (hab : Γ ⊢[PRAAx] gcd a b ≐ one) : Γ ⊢[PRAAx] inst2 omB q (a * b) ≐ inst2 omB q a + inst2 omB q b := by
  rw [inst2_om, inst2_om, inst2_om]
  refine .orE (isP_01 q) ?_ ?_
  · have h0 : ((isP q ≐ zero) :: Γ) ⊢[PRAAx] isP q ≐ zero := Prf.hyp0
    exact (zero_mul_l h0 _).eqTrans ((congrAdd (zero_mul_l h0 _) (zero_mul_l h0 _)).eqTrans (add_zero _)).eqSymm
  · let C : List (Fm PTm n) := (isP q ≐ one) :: Γ
    have hq : C ⊢[PRAAx] prime q := prime_of_isP Prf.hyp0
    have hv := val_mul hq ha.wk hb.wk
    refine .orE (cop_val hq ha.wk hab.wk) ?_ ?_
    · have s := Prf.andE₁ (sg_add_l (y := val q b) (Prf.hyp0 : ((val q a ≐ zero) :: C) ⊢[PRAAx] val q a ≐ zero))
      exact (congrMul (.eqRefl _) ((congrSg hv.wk).eqTrans s)).eqTrans (distrib _ _ _)
    · have s := Prf.andE₁ (sg_add_r (x := val q a) (Prf.hyp0 : ((val q b ≐ zero) :: C) ⊢[PRAAx] val q b ≐ zero))
      exact (congrMul (.eqRefl _) ((congrSg hv.wk).eqTrans s)).eqTrans (distrib _ _ _)

theorem sq_pt_cop {q a b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (hab : Γ ⊢[PRAAx] gcd a b ≐ one) : Γ ⊢[PRAAx] inst2 sqB q (a * b) ≐ inst2 sqB q a + inst2 sqB q b := by
  rw [inst2_sq, inst2_sq, inst2_sq]
  refine .orE (isP_01 q) ?_ ?_
  · have h0 : ((isP q ≐ zero) :: Γ) ⊢[PRAAx] isP q ≐ zero := Prf.hyp0
    exact (zero_mul_l h0 _).eqTrans ((congrAdd (zero_mul_l h0 _) (zero_mul_l h0 _)).eqTrans (add_zero _)).eqSymm
  · let C : List (Fm PTm n) := (isP q ≐ one) :: Γ
    have hq : C ⊢[PRAAx] prime q := prime_of_isP Prf.hyp0
    have hv := val_mul hq ha.wk hb.wk
    refine .orE (cop_val hq ha.wk hab.wk) ?_ ?_
    · have s := Prf.andE₂ (sg_add_l (y := val q b) (Prf.hyp0 : ((val q a ≐ zero) :: C) ⊢[PRAAx] val q a ≐ zero))
      exact (congrMul (.eqRefl _) ((congrSg (congrMonus hv.wk (.eqRefl _))).eqTrans s)).eqTrans (distrib _ _ _)
    · have s := Prf.andE₂ (sg_add_r (x := val q a) (Prf.hyp0 : ((val q b ≐ zero) :: C) ⊢[PRAAx] val q b ≐ zero))
      exact (congrMul (.eqRefl _) ((congrSg (congrMonus hv.wk (.eqRefl _))).eqTrans s)).eqTrans (distrib _ _ _)

/-! ## The counts -/

section Counts

variable {a b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
  (hab : Γ ⊢[PRAAx] gcd a b ≐ one)
include ha hb hab

theorem shifted :
    ((Γ.map Fm.shift) ⊢[PRAAx] Syn.shift a ≐ succ (pred (Syn.shift a))) ∧
      ((Γ.map Fm.shift) ⊢[PRAAx] Syn.shift b ≐ succ (pred (Syn.shift b))) ∧
      ((Γ.map Fm.shift) ⊢[PRAAx] gcd (Syn.shift a) (Syn.shift b) ≐ one) :=
  ⟨by simpa [Fm.shift, Syn.shift] using ha.shift, by simpa [Fm.shift, Syn.shift] using hb.shift, by
    have e := hab.shift
    simp only [Fm.shift, Fm.subst_eq, subst_ex2, subst_ap2, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] at e
    exact e⟩

/-- **`ω_N(ab) = ω_N(a) + ω_N(b)`** for coprime `a, b ≥ 1`. -/
theorem om_cop (N : PTm n) : Γ ⊢[PRAAx] om N (a * b) ≐ om N a + om N b := by
  obtain ⟨ha', hb', hab'⟩ := shifted ha hb hab
  refine sum_add2 omB omB omB (.allI (.impI ?_))
  rw [shift_mul']
  exact om_pt_cop ha'.wk hb'.wk hab'.wk

/-- **`s_N(ab) = s_N(a) + s_N(b)`** for coprime `a, b ≥ 1`. -/
theorem sq_cop (N : PTm n) : Γ ⊢[PRAAx] sq N (a * b) ≐ sq N a + sq N b := by
  obtain ⟨ha', hb', hab'⟩ := shifted ha hb hab
  refine sum_add2 sqB sqB sqB (.allI (.impI ?_))
  rw [shift_mul']
  exact sq_pt_cop ha'.wk hb'.wk hab'.wk

end Counts

/-! ## Parity and zero tests of sums -/

/-- `[x even]`. -/
abbrev ev (x : PTm n) : PTm n := eqb (rem x two) zero
/-- `[x odd]`. -/
abbrev od (x : PTm n) : PTm n := eqb (rem x two) one

theorem par_base_alg {E O Ex Ox E0 O0 : PTm n} (h : Γ ⊢[PRAAx] E ≐ Ex) (h' : Γ ⊢[PRAAx] O ≐ Ox)
    (e0 : Γ ⊢[PRAAx] E0 ≐ one) (o0 : Γ ⊢[PRAAx] O0 ≐ zero) :
    Γ ⊢[PRAAx] (E ≐ Ex * E0 + Ox * O0) ⋏ (O ≐ Ex * O0 + Ox * E0) := by
  have x := natEq h; have y := natEq h'; have z := natEq e0; have w := natEq o0
  refine .andI ?_ ?_
  · apply deriveNat; ipra_simps; linear_combination x - 𝔞 Ex * z - 𝔞 Ox * w
  · apply deriveNat; ipra_simps; linear_combination y - 𝔞 Ex * w - 𝔞 Ox * z

theorem par_step_alg {E O Ex Ox Ey Oy E1 O1 Ey1 Oy1 : PTm n} (pe : Γ ⊢[PRAAx] E1 ≐ O) (po : Γ ⊢[PRAAx] O1 ≐ E)
    (ihE : Γ ⊢[PRAAx] E ≐ Ex * Ey + Ox * Oy) (ihO : Γ ⊢[PRAAx] O ≐ Ex * Oy + Ox * Ey)
    (se : Γ ⊢[PRAAx] Ey1 ≐ Oy) (so : Γ ⊢[PRAAx] Oy1 ≐ Ey) :
    Γ ⊢[PRAAx] (E1 ≐ Ex * Ey1 + Ox * Oy1) ⋏ (O1 ≐ Ex * Oy1 + Ox * Ey1) := by
  have a := natEq pe; have b := natEq po; have c := natEq ihE; have d := natEq ihO
  have f := natEq se; have g := natEq so
  refine .andI ?_ ?_
  · apply deriveNat; ipra_simps; linear_combination a + d - 𝔞 Ex * f - 𝔞 Ox * g
  · apply deriveNat; ipra_simps; linear_combination b + c - 𝔞 Ex * g - 𝔞 Ox * f

theorem rem_zero_two : Γ ⊢[PRAAx] rem (zero : PTm n) two ≐ zero :=
  rem_eq' two_pos' (q := zero) (by apply deriveNat; ipra_simps; try ring) (zero_lt' two_pos')

/-- The parity bits of a sum. -/
abbrev ParF (x y : PTm n) : Fm PTm n :=
  (ev (x + y) ≐ ev x * ev y + od x * od y) ⋏ (od (x + y) ≐ ev x * od y + od x * ev y)

theorem par_add (x y : PTm n) : Γ ⊢[PRAAx] ParF x y := by
  have hall : Γ ⊢[PRAAx] Fm.all (ParF (Syn.shift x) (var 0)) := by
    refine PRA.qfInd _ ⟨trivial, trivial⟩ ?_ ?_
    · simp only [ParF, Fm.subst_and, Fm.subst_eq, subst_eqb, subst_ap2, PTm.subst_add, PTm.subst_mul,
        PTm.subst_monus, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero]
      have r0 := rem_zero_two (Γ := Γ) (n := n)
      have e0 : Γ ⊢[PRAAx] ev (zero : PTm n) ≐ one := (congrEqb' r0 (.eqRefl _)).eqTrans (eqb_of_eq (.eqRefl _))
      have o0 : Γ ⊢[PRAAx] od (zero : PTm n) ≐ zero := (congrEqb' r0 (.eqRefl _)).eqTrans (eqb_of_ne zero_ne_one')
      have ex : Γ ⊢[PRAAx] ev (x + zero) ≐ ev x := congrEqb' (congrAp2 remF (add_zero x) (.eqRefl _)) (.eqRefl _)
      have ox : Γ ⊢[PRAAx] od (x + zero) ≐ od x := congrEqb' (congrAp2 remF (add_zero x) (.eqRefl _)) (.eqRefl _)
      exact par_base_alg ex ox e0 o0
    · simp only [ParF, Fm.subst_and, Fm.subst_eq, subst_eqb, subst_ap2, PTm.subst_add, PTm.subst_mul,
        PTm.subst_monus, Syn.subst_var, Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero]
      let C : List (Fm PTm (n + 1)) := ParF (Syn.shift x) (var 0) :: Γ.map Fm.shift
      have ih : C ⊢[PRAAx] ParF (Syn.shift x) (var 0) := Prf.hyp0
      have es : C ⊢[PRAAx] Syn.shift x + succ (var 0) ≐ succ (Syn.shift x + var 0) := add_succ _ _
      have ps := Mobius.par_succ (Γ := C) (Syn.shift x + var 0)
      have py := Mobius.par_succ (Γ := C) (var 0 : PTm (n + 1))
      have pe : C ⊢[PRAAx] ev (Syn.shift x + succ (var 0)) ≐ od (Syn.shift x + var 0) :=
        (congrEqb' (congrAp2 remF es (.eqRefl _)) (.eqRefl _)).eqTrans (Prf.andE₁ ps)
      have po : C ⊢[PRAAx] od (Syn.shift x + succ (var 0)) ≐ ev (Syn.shift x + var 0) :=
        (congrEqb' (congrAp2 remF es (.eqRefl _)) (.eqRefl _)).eqTrans (Prf.andE₂ ps)
      exact par_step_alg pe po (Prf.andE₁ ih) (Prf.andE₂ ih) (Prf.andE₁ py) (Prf.andE₂ py)
  have h2 := Prf.allE y hall
  simp only [ParF, Fm.subst_and, Fm.subst_eq, subst_eqb, subst_ap2, PTm.subst_add, PTm.subst_mul,
    PTm.subst_monus, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] at h2
  exact h2

/-- `[x + y = 0] = [x = 0][y = 0]`. -/
theorem eqb_add_zero (x y : PTm n) : Γ ⊢[PRAAx] eqb (x + y) zero ≐ eqb x zero * eqb y zero := by
  refine .orE (zero_or_succ x) ?_ ?_
  · have h0 : ((x ≐ zero) :: Γ) ⊢[PRAAx] x ≐ zero := Prf.hyp0
    have e : ((x ≐ zero) :: Γ) ⊢[PRAAx] x + y ≐ y := (congrAdd h0 (.eqRefl _)).eqTrans (zero_add y)
    exact (congrEqb' e (.eqRefl _)).eqTrans ((one_mul _).eqSymm.eqTrans (congrMul (eqb_of_eq h0).eqSymm (.eqRefl _)))
  · let C : List (Fm PTm n) := (x ≐ succ (pred x)) :: Γ
    have hs : C ⊢[PRAAx] x ≐ succ (pred x) := Prf.hyp0
    have E : C ⊢[PRAAx] x + y ≐ succ (pred x + y) := by
      have z := natEq hs
      apply deriveNat; ipra_simps; linear_combination z
    have ne1 : C ⊢[PRAAx] neg (x + y ≐ zero) := .impI (succ_ne_zero' _ (E.wk.eqSymm.eqTrans Prf.hyp0))
    have ne2 : C ⊢[PRAAx] neg (x ≐ zero) := .impI (succ_ne_zero' _ (hs.wk.eqSymm.eqTrans Prf.hyp0))
    exact (eqb_of_ne ne1).eqTrans (zero_mul_l (eqb_of_ne ne2) _).eqSymm

theorem mu_alg {S Sa Sb E O Ea Oa Eb Ob : PTm n} (hs : Γ ⊢[PRAAx] S ≐ Sa * Sb)
    (he : Γ ⊢[PRAAx] E ≐ Ea * Eb + Oa * Ob) (ho : Γ ⊢[PRAAx] O ≐ Ea * Ob + Oa * Eb) :
    Γ ⊢[PRAAx] (S * E ≐ Sa * Ea * (Sb * Eb) + Sa * Oa * (Sb * Ob)) ⋏
      (S * O ≐ Sa * Ea * (Sb * Ob) + Sa * Oa * (Sb * Eb)) := by
  have x := natEq hs; have y := natEq he; have z := natEq ho
  refine .andI ?_ ?_
  · apply deriveNat; ipra_simps; linear_combination 𝔞 E * x + 𝔞 Sa * 𝔞 Sb * y
  · apply deriveNat; ipra_simps; linear_combination 𝔞 O * x + 𝔞 Sa * 𝔞 Sb * z

/-- **`el:mobiuscancel`, multiplicativity**: for coprime `a, b ≥ 1` and every bound `N`,
`μ⁺(ab) = μ⁺(a)μ⁺(b) + μ⁻(a)μ⁻(b)` and `μ⁻(ab) = μ⁺(a)μ⁻(b) + μ⁻(a)μ⁺(b)`, i.e. `μ(ab) = μ(a)μ(b)`. -/
theorem mu_mul {a b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (hab : Γ ⊢[PRAAx] gcd a b ≐ one) (N : PTm n) :
    Γ ⊢[PRAAx] (muP N (a * b) ≐ muP N a * muP N b + muN N a * muN N b) ⋏
      (muN N (a * b) ≐ muP N a * muN N b + muN N a * muP N b) := by
  have s := (congrEqb' (sq_cop ha hb hab N) (.eqRefl zero)).eqTrans (eqb_add_zero _ _)
  have o := om_cop ha hb hab N
  have pa := par_add (Γ := Γ) (om N a) (om N b)
  have he : Γ ⊢[PRAAx] ev (om N (a * b)) ≐ ev (om N a) * ev (om N b) + od (om N a) * od (om N b) :=
    (congrEqb' (congrAp2 remF o (.eqRefl _)) (.eqRefl _)).eqTrans (Prf.andE₁ pa)
  have ho : Γ ⊢[PRAAx] od (om N (a * b)) ≐ ev (om N a) * od (om N b) + od (om N a) * ev (om N b) :=
    (congrEqb' (congrAp2 remF o (.eqRefl _)) (.eqRefl _)).eqTrans (Prf.andE₂ pa)
  exact mu_alg s he ho

end LeanProofs.IPRA.AnalyticNumberTheory.MobiusMult
