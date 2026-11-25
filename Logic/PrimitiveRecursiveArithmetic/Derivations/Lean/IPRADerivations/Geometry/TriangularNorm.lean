import IPRADerivations.Core.Tactic
import IPRADerivations.Core.ProdLemmas
import IPRADerivations.Core.ParityArith
import IPRADerivations.Combinatorics.BinomialIdentities
import IPRADerivations.Analysis.RationalClosure
import IPRADerivations.Core.CertificateTactics

/-!
# The triangular norm and its 2-adic descent

Packet: `geometry/aperiodic_monotile_ipra_2026-11-16` (Section "The triangular-norm descent":
`lem:qparity`, `lem:nosqrt2`). The triangular-lattice norm is `Q(m, n) = m² + m n + n²`.

* `q_ee`, `q_oe`, `q_eo`, `q_oo`: the four residue classes modulo `2`, as explicit identities;
  in particular `Q(2a, 2b) = 4 Q(a, b)`;
* `q_parity`: `Q(m, n)` is even iff `m` and `n` are even;
* `halve_step`: from `Q(C, D) = 2 Q(A, B)` all four numbers are even, and the halves satisfy the
  same equation;
* `halving_invariant`: with `hf k x` the `k`-fold half of `x`, the equation holds for the
  `k`-fold halves and `a = 2^k · hf k a`, `b = 2^k · hf k b`, by quantifier-free induction on the
  fuel `k`;
* `no_sqrt2`, `no_sqrt2_all`: `Q(c, d) = 2 Q(a, b)` gives `a = b = 0` and `Q(a, b) = 0`;
* `norm_reflect`: over the integers `Q(x + y, −y) = Q(x, y)`, so a value of `Q` at a pair of
  opposite signs is a value at natural numbers, and the statements above cover all integers;
* `norm_mul`: `Q(a, b) Q(c, d) = Q(a c − b d, a d + b c + b d)`.

The descent is carried by the fuel `k` instead of the generic descent principle: at `k = a` the
equation `a = 2^a · hf a a` contradicts `a < 2^a` unless `a = 0`. The torus argument
(`thm:notorus`) and the substitution system are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.TriangularNorm

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Analysis.RationalClosure (succ_le_two_pow)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {N : ℕ} {Γ : List (Fm PTm N)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `Q(m, n) = m² + m n + n²`. -/
abbrev qn {N : ℕ} (m n : PTm N) : PTm N := m * m + m * n + n * n

theorem q_congr {m n m' n' : PTm N} (hm : Γ ⊢[PRAAx] m ≐ m') (hn : Γ ⊢[PRAAx] n ≐ n') :
    Γ ⊢[PRAAx] qn m n ≐ qn m' n' := by
  ipra_lc (𝔞(m) + 𝔞(m') + 𝔞(n)) * natEq hm + (𝔞(m') + 𝔞(n) + 𝔞(n')) * natEq hn

theorem two_congr {X Y : PTm N} (h : Γ ⊢[PRAAx] X ≐ Y) : Γ ⊢[PRAAx] two * X ≐ two * Y :=
  congrMul (.eqRefl _) h

/-! ## The four residue classes -/

/-- `Q(2a, 2b) = 4 Q(a, b)`. -/
theorem q_ee (a b : PTm N) : Γ ⊢[PRAAx] qn (two * a) (two * b) ≐ two * (two * qn a b) := by
  ipra_ring

theorem q_oe (a b : PTm N) : Γ ⊢[PRAAx] qn (two * a + one) (two * b) ≐
    two * (two * (a * a) + two * a + two * (a * b) + b + two * (b * b)) + one := by
  ipra_ring

theorem q_eo (a b : PTm N) : Γ ⊢[PRAAx] qn (two * a) (two * b + one) ≐
    two * (two * (a * a) + two * (a * b) + a + two * (b * b) + two * b) + one := by
  ipra_ring

theorem q_oo (a b : PTm N) : Γ ⊢[PRAAx] qn (two * a + one) (two * b + one) ≐
    two * (two * (a * a) + (two + one) * a + two * (a * b) + (two + one) * b + two * (b * b) + one) +
      one := by
  ipra_ring

/-! ## Parity -/

/-- `Q(0, 0) ≡ 0`. -/
theorem q_par_ee {m n : PTm N} (hm : Γ ⊢[PRAAx] par m ≐ zero) (hn : Γ ⊢[PRAAx] par n ≐ zero) :
    Γ ⊢[PRAAx] par (qn m n) ≐ zero :=
  (congrAp1 parF ((q_congr (even_of hm) (even_of hn)).eqTrans (q_ee _ _))).eqTrans (par_double _)

/-- `Q(1, 0) ≡ Q(1, 1) ≡ 1`. -/
theorem q_par_odd_left {m : PTm N} (n : PTm N) (hm : Γ ⊢[PRAAx] par m ≐ one) :
    Γ ⊢[PRAAx] par (qn m n) ≐ one := by
  refine .orE (par_cases n) ?_ ?_
  · have hm' : ((par n ≐ zero) :: Γ) ⊢[PRAAx] par m ≐ one := hm.wk
    exact (congrAp1 parF ((q_congr (odd_of hm') (even_of Prf.hyp0)).eqTrans (q_oe _ _))).eqTrans
      (par_double_succ _)
  · have hm' : ((par n ≐ one) :: Γ) ⊢[PRAAx] par m ≐ one := hm.wk
    exact (congrAp1 parF ((q_congr (odd_of hm') (odd_of Prf.hyp0)).eqTrans (q_oo _ _))).eqTrans
      (par_double_succ _)

/-- `Q(0, 1) ≡ Q(1, 1) ≡ 1`. -/
theorem q_par_odd_right (m : PTm N) {n : PTm N} (hn : Γ ⊢[PRAAx] par n ≐ one) :
    Γ ⊢[PRAAx] par (qn m n) ≐ one := by
  refine .orE (par_cases m) ?_ ?_
  · have hn' : ((par m ≐ zero) :: Γ) ⊢[PRAAx] par n ≐ one := hn.wk
    exact (congrAp1 parF ((q_congr (even_of Prf.hyp0) (odd_of hn')).eqTrans (q_eo _ _))).eqTrans
      (par_double_succ _)
  · have hn' : ((par m ≐ one) :: Γ) ⊢[PRAAx] par n ≐ one := hn.wk
    exact (congrAp1 parF ((q_congr (odd_of Prf.hyp0) (odd_of hn')).eqTrans (q_oo _ _))).eqTrans
      (par_double_succ _)

/-- An even value of `Q` forces both arguments to be even. -/
theorem even_of_q_even {m n : PTm N} (h : Γ ⊢[PRAAx] par (qn m n) ≐ zero) :
    Γ ⊢[PRAAx] (par m ≐ zero) ⋏ (par n ≐ zero) := by
  refine .andI ?_ ?_
  · refine .orE (par_cases m) Prf.hyp0 ?_
    have h' : ((par m ≐ one) :: Γ) ⊢[PRAAx] par (qn m n) ≐ zero := h.wk
    exact succ_ne_zero' _ (a := zero) ((q_par_odd_left n Prf.hyp0).eqSymm.eqTrans h')
  · refine .orE (par_cases n) Prf.hyp0 ?_
    have h' : ((par n ≐ one) :: Γ) ⊢[PRAAx] par (qn m n) ≐ zero := h.wk
    exact succ_ne_zero' _ (a := zero) ((q_par_odd_right m Prf.hyp0).eqSymm.eqTrans h')

/-- `lem:qparity`: `Q(m, n) ≡ 0 (mod 2)` iff `m ≡ n ≡ 0 (mod 2)`. -/
theorem q_parity (m n : PTm N) :
    Γ ⊢[PRAAx] Fm.iff (par (qn m n) ≐ zero) ((par m ≐ zero) ⋏ (par n ≐ zero)) :=
  Prf.iffI (.impI (even_of_q_even Prf.hyp0))
    (.impI (q_par_ee (Prf.andE₁ Prf.hyp0) (Prf.andE₂ Prf.hyp0)))

/-! ## One step of the descent -/

theorem two_pos : Γ ⊢[PRAAx] (two : PTm N) ≐ succ (pred two) := pos_of_eq_succ (.eqRefl _)

/-- From `Q(C, D) = 2 Q(A, B)`: `A` and `B` are even and `Q(C/2, D/2) = 2 Q(A/2, B/2)`. -/
theorem halve_step {A B C D : PTm N} (h : Γ ⊢[PRAAx] qn C D ≐ two * qn A B) :
    Γ ⊢[PRAAx] ((A ≐ two * half A) ⋏ (B ≐ two * half B)) ⋏
      (qn (half C) (half D) ≐ two * qn (half A) (half B)) := by
  have pCD := even_of_q_even ((congrAp1 parF h).eqTrans (par_double _))
  have eC := even_of (Prf.andE₁ pCD); have eD := even_of (Prf.andE₂ pCD)
  -- `2 Q(A, B) = 4 Q(C/2, D/2)`.
  have h₁ : Γ ⊢[PRAAx] two * qn A B ≐ two * (two * qn (half C) (half D)) :=
    h.eqSymm.eqTrans ((q_congr eC eD).eqTrans (q_ee _ _))
  have h₂ : Γ ⊢[PRAAx] qn A B ≐ two * qn (half C) (half D) := mul_cancel two_pos h₁
  have pAB := even_of_q_even ((congrAp1 parF h₂).eqTrans (par_double _))
  have eA := even_of (Prf.andE₁ pAB); have eB := even_of (Prf.andE₂ pAB)
  -- `2 Q(C/2, D/2) = 4 Q(A/2, B/2)`.
  have h₃ : Γ ⊢[PRAAx] two * qn (half C) (half D) ≐ two * (two * qn (half A) (half B)) :=
    h₂.eqSymm.eqTrans ((q_congr eA eB).eqTrans (q_ee _ _))
  exact .andI (.andI eA eB) (mul_cancel two_pos h₃)

/-! ## Iterated halving -/

abbrev hfF : PR 2 := rec2 (var 0) (half (var 1))

/-- `hf k x`: `x` halved `k` times. -/
abbrev hf {N : ℕ} (k x : PTm N) : PTm N := ap2 hfF k x

theorem hf_zero (x : PTm N) : Γ ⊢[PRAAx] hf zero x ≐ x := by
  have h := rec2_zero (Γ := Γ) (var 0) (half (var 1)) x
  simpa using h

theorem hf_succ (k x : PTm N) : Γ ⊢[PRAAx] hf (succ k) x ≐ half (hf k x) := by
  have h := rec2_succ (Γ := Γ) (var 0) (half (var 1)) k x
  simpa using h

/-- `a = P H`, `H = 2 h`, `P' = P · 2`, `H' = h` give `a = P' H'`. -/
theorem scale_step {a P P' H H' h : PTm N} (ia : Γ ⊢[PRAAx] a ≐ P * H) (eH : Γ ⊢[PRAAx] H ≐ two * h)
    (eP : Γ ⊢[PRAAx] P' ≐ P * two) (eH' : Γ ⊢[PRAAx] H' ≐ h) : Γ ⊢[PRAAx] a ≐ P' * H' := by
  ipra_lc natEq ia + 𝔞(P) * natEq eH - 𝔞(h) * natEq eP - 𝔞(P') * natEq eH'

/-- The invariant after `k` halvings. -/
abbrev Inv {N : ℕ} (k a b c d : PTm N) : Fm PTm N :=
  ((a ≐ pw two k * hf k a) ⋏ (b ≐ pw two k * hf k b)) ⋏
    (qn (hf k c) (hf k d) ≐ two * qn (hf k a) (hf k b))

theorem inv_base {a b c d : PTm N} (h : Γ ⊢[PRAAx] qn c d ≐ two * qn a b) :
    Γ ⊢[PRAAx] Inv zero a b c d := by
  have unit : ∀ x : PTm N, Γ ⊢[PRAAx] x ≐ pw two zero * hf zero x := fun x =>
    (one_mul x).eqSymm.eqTrans (congrMul (pw_zero two).eqSymm (hf_zero x).eqSymm)
  exact .andI (.andI (unit a) (unit b))
    ((q_congr (hf_zero c) (hf_zero d)).eqTrans
      (h.eqTrans (two_congr (q_congr (hf_zero a) (hf_zero b)).eqSymm)))

theorem inv_step {k a b c d : PTm N} (ih : Γ ⊢[PRAAx] Inv k a b c d) :
    Γ ⊢[PRAAx] Inv (succ k) a b c d := by
  have s := halve_step (Prf.andE₂ ih)
  have ia := Prf.andE₁ (Prf.andE₁ ih); have ib := Prf.andE₂ (Prf.andE₁ ih)
  have eA := Prf.andE₁ (Prf.andE₁ s); have eB := Prf.andE₂ (Prf.andE₁ s)
  exact .andI
    (.andI (scale_step ia eA (pw_succ two k) (hf_succ k a)) (scale_step ib eB (pw_succ two k) (hf_succ k b)))
    ((q_congr (hf_succ k c) (hf_succ k d)).eqTrans
      ((Prf.andE₂ s).eqTrans (two_congr (q_congr (hf_succ k a) (hf_succ k b)).eqSymm)))

/-- Variables: `0 = k` (induction), `1 = a`, `2 = b`, `3 = c`, `4 = d`. -/
private abbrev invF : Fm PTm 5 :=
  (qn (var 3) (var 4) ≐ two * qn (var 1) (var 2)) ⟶ Inv (var 0) (var 1) (var 2) (var 3) (var 4)

private theorem inv₀ : ([] : List (Fm PTm 5)) ⊢[PRAAx] invF := by
  refine ind _ ⟨trivial, ⟨⟨trivial, trivial⟩, trivial⟩⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul,
      Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two, inst_three, inst_four,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (inv_base Prf.hyp0)
  · simp only [Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul,
      Syn.subst_var, Syn.repl_zero, repl_one, repl_two, repl_three, repl_four,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (inv_step (.impE Prf.hyp1 Prf.hyp0))

/-- The equation survives `k` halvings, and `a`, `b` are divisible by `2^k`. -/
theorem halving_invariant (k : PTm N) {a b c d : PTm N} (h : Γ ⊢[PRAAx] qn c d ≐ two * qn a b) :
    Γ ⊢[PRAAx] Inv k a b c d := by
  have i := inst (Γ := Γ) inv₀ (![k, a, b, c, d] : Fin 5 → PTm N)
  simp at i
  exact .impE i h

/-! ## The contradiction -/

/-- `a = 2^a · H` forces `a = 0`, since `a < 2^a`. -/
theorem zero_of_pow {a H : PTm N} (h : Γ ⊢[PRAAx] a ≐ pw two a * H) : Γ ⊢[PRAAx] a ≐ zero := by
  refine .orE (zero_or_succ H) ?_ ?_
  · have h' : ((H ≐ zero) :: Γ) ⊢[PRAAx] a ≐ pw two a * H := h.wk
    exact h'.eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _))
  · have h' : ((H ≐ succ (pred H)) :: Γ) ⊢[PRAAx] a ≐ pw two a * H := h.wk
    have e : ((H ≐ succ (pred H)) :: Γ) ⊢[PRAAx] a ≐ pw two a + pw two a * pred H := by
      ipra_lc natEq h' + 𝔞(pw two a) * natEq (Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := H ≐ succ (pred H)))
    exact not_succ_le_self a _ (le_trans (succ_le_two_pow a) (le_of_eq_add e))

/-- `lem:nosqrt2`: `Q(c, d) = 2 Q(a, b)` has only the solution `a = b = 0`. -/
theorem no_sqrt2 {a b c d : PTm N} (h : Γ ⊢[PRAAx] qn c d ≐ two * qn a b) :
    Γ ⊢[PRAAx] (a ≐ zero) ⋏ (b ≐ zero) :=
  .andI (zero_of_pow (Prf.andE₁ (Prf.andE₁ (halving_invariant a h))))
    (zero_of_pow (Prf.andE₂ (Prf.andE₁ (halving_invariant b h))))

/-- In particular `Q(a, b) = 0`: there is no solution with `Q(a, b) > 0`. -/
theorem no_sqrt2_norm {a b c d : PTm N} (h : Γ ⊢[PRAAx] qn c d ≐ two * qn a b) :
    Γ ⊢[PRAAx] qn a b ≐ zero := by
  have z := no_sqrt2 h
  ipra_lc (𝔞(a) + 𝔞(b)) * natEq (Prf.andE₁ z) + 𝔞(b) * natEq (Prf.andE₂ z)

/-- Variables: `0 = a`, `1 = b`, `2 = c`, `3 = d`. -/
def noSqrt2Formula : Fm PTm 4 :=
  (qn (var 2) (var 3) ≐ two * qn (var 0) (var 1)) ⟶
    (((var 0 ≐ zero) ⋏ (var 1 ≐ zero)) ⋏ (qn (var 0) (var 1) ≐ zero))

theorem no_sqrt2_all : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 4 noSqrt2Formula :=
  closeAll 4 (.impI (.andI (no_sqrt2 Prf.hyp0) (no_sqrt2_norm Prf.hyp0)))

/-! ## Integers -/

section Integers

abbrev x : ZT 8 := .var2 0 1
abbrev y : ZT 8 := .var2 2 3
abbrev z : ZT 8 := .var2 4 5
abbrev w : ZT 8 := .var2 6 7

/-- `Q` over the integers. -/
abbrev zq {k : ℕ} (u v : ZT k) : ZT k := u * u + u * v + v * v

/-- `Q(x + y, −y) = Q(x, y)`. -/
def reflectFormula : Fm PTm 8 := ZT.eq (zq (x + y) (-y)) (zq x y)

/-- `Q(x, y) Q(z, w) = Q(x z − y w, x w + y z + y w)`. -/
def mulFormula : Fm PTm 8 := ZT.eq (zq x y * zq z w) (zq (x * z - y * w) (x * w + y * z + y * w))

theorem reflect_open : ([] : List (Fm PTm 8)) ⊢[PRAAx] reflectFormula := by
  unfold reflectFormula; ipra_ring

theorem mul_open : ([] : List (Fm PTm 8)) ⊢[PRAAx] mulFormula := by
  unfold mulFormula; ipra_ring

/-- The form is invariant under `(x, y) ↦ (x + y, −y)`. -/
theorem norm_reflect : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 8 reflectFormula := closeAll 8 reflect_open

/-- The norm is multiplicative. -/
theorem norm_mul : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 8 mulFormula := closeAll 8 mul_open

end Integers

end LeanProofs.IPRA.Geometry.TriangularNorm
