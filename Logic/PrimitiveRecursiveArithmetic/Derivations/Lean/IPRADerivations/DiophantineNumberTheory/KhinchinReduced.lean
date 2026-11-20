import IPRADerivations.DiophantineNumberTheory.KhinchinBadBound
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.SumSplit

/-!
# Enough separated reduced fractions in every interval: (K3) (`hurwitz_khinchin_ipra`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, §"Enough separated reduced
fractions in every interval". For `J = (a, b)`, `L = b − a`, its middle half `J* = (a + L/4, b − L/4)`
of length `λ = L/2`, and `Q = 2^k`, the reduced fractions `p/q ∈ J*` with `Q/4 < q ≤ Q` number

  `LQ²/32 ≤ #𝓡_k(J) ≤ LQ²`                                                              (K3)

when `k ≥ K(J, N)` (K4), which gives `Lk ≥ 512`.

Here `J* = (α/β, γ/β)` with `α ≤ γ ≤ β = b₀ + 1`, so `λ = D/β` for `D = γ − α` and `L = 2D/β`; numerators
range over `p < M` for some `M ≥ Q` (every `p/q ∈ J* ⊆ (0, 1)` has `p < q ≤ Q`). The count
`redR Q y = Σ_{i < Q − ⌊Q/4⌋} #{p < M : p/q ∈ J*, gcd(p, q) = 1}` at `q = ⌊Q/4⌋ + 1 + i` runs over the
denominators `⌊Q/4⌋ < q ≤ Q`, i.e. `Q < 4q ≤ 4Q`. The hypothesis `Dk ≥ 256β` is `Lk ≥ 512`; it already
forces `k ≥ 256` (as `D ≤ β`), so `k ≥ 4` need not be assumed. `k3_bounds`:

  `DQ² ≤ 16β #𝓡`  (`LQ²/32 ≤ #𝓡`)   and   `β #𝓡 ≤ 2DQ²`  (`#𝓡 ≤ LQ²`).

The proof is the paper's (K7) computation:

* every pair counted by `A(Q)` (`KhinchinLattice.latticeA`) is coprime or bad (`total_split`), so
  `A(Q) ≤ #𝓡 + A(⌊Q/4⌋) + B(Q)` (`count_le`); (K5) bounds `A(Q)` below and `A(⌊Q/4⌋)` above, and
  `KhinchinBadBound.bad_bound` bounds `B(Q)`; together `3DQ² + 28DQ ≤ 32β#𝓡 + 40βQ + 16(D + 2β)(k + 1)Q`
  (`k7_lower_aux`);
* `2^k ≥ k²` for `k ≥ 4` (`sq_le_two_pow`) and (K4) give `DQ ≥ Dk·k ≥ 256βk`, which absorbs the error
  terms (`k4_aux`);
* the upper bound: `#𝓡 ≤ A(Q)` and (K5) give `2β#𝓡 ≤ DQ(Q + 1) + 2βQ ≤ 4DQ²` since `DQ ≥ β`
  (`upper_aux`). This replaces the paper's separation argument, which is not needed for the count.

All inequalities are derived from explicit slack certificates (`Core/OrderCertificates.ipra_le`).
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinReduced

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.Topology.StaggeredGrids (eqb01')
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBad (xq inJT cntB badB inst2_cntB inst2_badB)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBadSum (cB inst2_cB bqB inst2_bqB cnt_zero cnt_dS inst2_aK)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBadBound (bad_bound)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinLattice (aK latticeA lattice_core)
open LeanProofs.IPRA.AnalyticNumberTheory.SquareReciprocal (cancel_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Coprime and bad numerators -/

/-- `[p/q ∈ J*][gcd(p, q) = 1]` in `(p, x)`. -/
abbrev copB : PTm 2 := cntB * eqb (gcd (var 0) (xq (var 1))) one

/-- `cop(q) = #{p < M : p/q ∈ J*, gcd(p, q) = 1}` in `(q, ⟨M, t⟩)`. -/
abbrev cqB : PTm 2 := ap2 (sumF copB) (fstT (var 1)) (pairT (var 0) (sndT (var 1)))

/-- `#𝓡(Q) = Σ_{⌊Q/4⌋ < q ≤ Q} cop(q)`. -/
abbrev redR (Q y : PTm n) : PTm n :=
  ap2 (sumF (offB cqB)) (monus Q (quo Q (num 4))) (pairT (succ (quo Q (num 4))) y)

theorem inst2_copB (p x : PTm n) :
    inst2 copB p x = inJT p (xq x) (KhinchinBad.xα x) (KhinchinBad.xγ x) (KhinchinBad.xβ x) *
      eqb (gcd p (xq x)) one := by
  simp only [inst2, copB, cntB, inJT, Signum.sg, PTm.subst_mul, PTm.subst_monus, subst_ex2,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero, subst_eqb, subst_fstT, subst_sndT]

theorem inst2_cqB (q y : PTm n) : inst2 cqB q y = ap2 (sumF copB) (fstT y) (pairT q (sndT y)) := by
  simp [inst2, subst_ap2]

/-- `[p/q ∈ J*] = [p/q ∈ J*][gcd = 1] + [p/q ∈ J*][gcd ≠ 1]`. -/
theorem split_point (p x : PTm n) :
    Γ ⊢[PRAAx] inst2 cntB p x ≐ inst2 copB p x + inst2 badB p x := by
  rw [inst2_cntB, inst2_copB, inst2_badB]
  refine .orE (eqb01' (Γ := Γ) (gcd p (xq x)) one) ?_ ?_
  · have h : ((eqb (gcd p (xq x)) one ≐ zero) :: Γ) ⊢[PRAAx] eqb (gcd p (xq x)) one ≐ zero := Prf.hyp0
    refine .eqTrans ?_ (congrAdd (congrMul (.eqRefl _) h)
      (congrMul (.eqRefl _) ((congrMonus (.eqRefl _) h).eqTrans (monus_zero _)))).eqSymm
    apply deriveNat; ipra_simps; ring
  · have h : ((eqb (gcd p (xq x)) one ≐ one) :: Γ) ⊢[PRAAx] eqb (gcd p (xq x)) one ≐ one := Prf.hyp0
    refine .eqTrans ?_ (congrAdd (congrMul (.eqRefl _) h)
      (congrMul (.eqRefl _) ((congrMonus (.eqRefl _) h).eqTrans (monus_self _)))).eqSymm
    apply deriveNat; ipra_simps; ring

theorem count_split (M x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF cntB) M x ≐ ap2 (sumF copB) M x + ap2 (sumF badB) M x := by
  refine (sum_congr_bounded cntB (addBody copB badB) x x M (.allI (.impI ?_))).eqTrans (sum_add copB badB M x)
  rw [inst2_addBody]
  exact split_point _ _

/-- `Σ_{q<N} C(q) = Σ_{q<N} cop(q) + Σ_{q<N} bad(q)`. -/
theorem total_split (N y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF cB) N y ≐ ap2 (sumF cqB) N y + ap2 (sumF bqB) N y := by
  refine (sum_congr_bounded cB (addBody cqB bqB) y y N (.allI (.impI ?_))).eqTrans (sum_add cqB bqB N y)
  rw [inst2_addBody, inst2_cB, inst2_cqB, inst2_bqB]
  exact count_split _ _

/-- `Σ_{q ≤ X} C(q) = A(X)`: the denominator `0` counts nothing. -/
theorem cnt_total (X y : PTm n) : Γ ⊢[PRAAx] ap2 (sumF cB) (succ X) y ≐ ap2 (sumF aK) X y := by
  refine (sum_shift cB X y).eqTrans ?_
  rw [inst2_cB]
  refine (congrAdd (cnt_zero _ _ (.eqRefl _)) (.eqRefl _)).eqTrans ((zero_add _).eqTrans ?_)
  refine sum_congr_bounded (shiftBody cB) aK y y X (.allI (.impI ?_))
  rw [inst2_shiftBody, inst2_cB, inst2_aK]
  exact cnt_dS _ _ _

/-- `Σ_{q<N} cop(q) ≤ Σ_{q<N} C(q)`. -/
theorem cop_le (N y : PTm n) : Γ ⊢[PRAAx] le (ap2 (sumF cqB) N y) (ap2 (sumF cB) N y) :=
  le_congr (.eqRefl _) (total_split N y).eqSymm (le_add_right _ _)

/-! ## The count identity -/

/-- `A(Q) ≤ #𝓡 + A(⌊Q/4⌋) + B(Q)` and `#𝓡 ≤ A(Q)`, for `Q' = ⌊Q/4⌋ ≤ Q`. -/
theorem count_le {Q y : PTm n} (hQ' : Γ ⊢[PRAAx] le (quo Q (num 4)) Q) :
    Γ ⊢[PRAAx] le (ap2 (sumF aK) Q y) (redR Q y + ap2 (sumF aK) (quo Q (num 4)) y + ap2 (sumF bqB) (succ Q) y) ⋏
      le (redR Q y) (ap2 (sumF aK) Q y) := by
  have hs : Γ ⊢[PRAAx] succ Q ≐ succ (quo Q (num 4)) + monus Q (quo Q (num 4)) := by
    have e := natEq (eq_add_of_le hQ')
    apply deriveNat; ipra_simps; linear_combination e
  -- `cop(≤ Q) = cop(≤ Q') + #𝓡`
  have eC : Γ ⊢[PRAAx] ap2 (sumF cqB) (succ Q) y ≐ ap2 (sumF cqB) (succ (quo Q (num 4))) y + redR Q y :=
    (congrAp2 (sumF cqB) hs (.eqRefl _)).eqTrans (sum_split cqB _ _ y)
  have eA : Γ ⊢[PRAAx] ap2 (sumF aK) Q y ≐ ap2 (sumF cqB) (succ Q) y + ap2 (sumF bqB) (succ Q) y :=
    (cnt_total Q y).eqSymm.eqTrans (total_split _ y)
  have hc := le_congr (.eqRefl _) (cnt_total _ y) (cop_le (Γ := Γ) (succ (quo Q (num 4))) y)
  have hall := le_congr (.eqRefl _) (cnt_total _ y) (cop_le (Γ := Γ) (succ Q) y)
  refine .andI ?_ ?_
  · have e1 := natEq eA
    have e2 := natEq eC
    ipra_le sl hc with -e1 - e2
  · have e2 := natEq eC
    ipra_le sl hall + 𝔞 (ap2 (sumF cqB) (succ (quo Q (num 4))) y) with e2

/-! ## `2^k ≥ k²` -/

/-- `t + 4`. -/
abbrev f4 (t : PTm n) : PTm n := succ (succ (succ (succ t)))

/-- Variables: `0 = t`. -/
private abbrev sqF : Fm PTm 1 := le (f4 (var 0) * f4 (var 0)) (pw two (f4 (var 0)))

theorem sq4_base : Γ ⊢[PRAAx] le (f4 (zero : PTm n) * f4 zero) (pw two (f4 zero)) := by
  have p1 := natEq (pw_succ (Γ := Γ) (two : PTm n) (succ (succ (succ zero))))
  have p2 := natEq (pw_succ (Γ := Γ) (two : PTm n) (succ (succ zero)))
  have p3 := natEq (pw_succ (Γ := Γ) (two : PTm n) (succ zero))
  have p4 := natEq (pw_succ (Γ := Γ) (two : PTm n) zero)
  have p0 := natEq (pw_zero (Γ := Γ) (two : PTm n))
  ipra_le 0 using linear_combination p1 + 2 * p2 + 4 * p3 + 8 * p4 + 16 * p0

theorem sq4_step {t : PTm n} (ih : Γ ⊢[PRAAx] le (f4 t * f4 t) (pw two (f4 t))) :
    Γ ⊢[PRAAx] le (succ (f4 t) * succ (f4 t)) (pw two (succ (f4 t))) := by
  have p := natEq (pw_succ (Γ := Γ) (two : PTm n) (f4 t))
  ipra_le 2 * sl ih + 𝔞 t * 𝔞 t + 6 * 𝔞 t + 7 with p

private theorem sq4₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] sqF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · have e : sqF.subst (Syn.inst zero) = (le (f4 zero * f4 zero) (pw two (f4 zero)) : Fm PTm 0) := by simp
    rw [e]
    exact sq4_base
  · have e : sqF.subst (repl (succ (var 0))) =
        (le (succ (f4 (var 0)) * succ (f4 (var 0))) (pw two (succ (f4 (var 0)))) : Fm PTm 1) := by simp
    rw [e]
    exact sq4_step Prf.hyp0

/-- `k² ≤ 2^k` for `k ≥ 4`. -/
theorem sq_le_two_pow {k : PTm n} (h : Γ ⊢[PRAAx] le (num 4) k) : Γ ⊢[PRAAx] le (k * k) (pw two k) := by
  have i := inst (Γ := Γ) sq4₀ (![monus k (num 4)] : Fin 1 → PTm n)
  simp at i
  have ek : Γ ⊢[PRAAx] k ≐ f4 (monus k (num 4)) := by
    have e := natEq (eq_add_of_le h)
    apply deriveNat; ipra_simps; linear_combination e
  exact le_congr (congrMul ek ek).eqSymm (congrAp2 powF ek (.eqRefl _)).eqSymm i

/-! ## The arithmetic of (K7) -/

/-- `3DQ² + 28DQ ≤ 32β#𝓡 + 40βQ + 16C(K Q)` with `C = D + 2β`, `K = k + 1`. -/
theorem k7_lower_aux {R AQ AQ' Bad α γ D B C K Q Q' : PTm n}
    (hA : Γ ⊢[PRAAx] le AQ (R + AQ' + Bad))
    (lo : Γ ⊢[PRAAx] le (γ * (Q * succ Q)) (two * B * AQ + α * (Q * succ Q) + two * B * Q))
    (up : Γ ⊢[PRAAx] le (two * B * AQ' + α * (Q' * succ Q')) (γ * (Q' * succ Q') + two * B * Q'))
    (hq : Γ ⊢[PRAAx] le (num 4 * Q') Q)
    (bb : Γ ⊢[PRAAx] le (num 8 * B * Bad + num 4 * D * Q) (num 3 * D * (Q * Q) + num 4 * C * (K * Q)))
    (eγ : Γ ⊢[PRAAx] γ ≐ α + D) :
    Γ ⊢[PRAAx] le (num 3 * D * (Q * Q) + num 28 * D * Q) (num 32 * B * R + num 40 * B * Q + num 16 * C * (K * Q)) := by
  have e := natEq eγ
  ipra_le 16 * sl lo + 32 * 𝔞 B * sl hA + 16 * sl up + 4 * sl bb + 8 * 𝔞 B * sl hq +
    𝔞 D * (8 * 𝔞 Q' * sl hq + sl hq * sl hq + 4 * sl hq)
    with (16 * (𝔞 Q * (𝔞 Q + 1) - 𝔞 Q' * (𝔞 Q' + 1))) * e

/-- (K4) absorbs the error terms: `2 (DQ²) ≤ 2 (16β#𝓡)`. -/
theorem k4_aux {R D B C K Q k : PTm n}
    (h : Γ ⊢[PRAAx] le (num 3 * D * (Q * Q) + num 28 * D * Q) (num 32 * B * R + num 40 * B * Q + num 16 * C * (K * Q)))
    (f1 : Γ ⊢[PRAAx] le (k * k) Q) (f2 : Γ ⊢[PRAAx] le (num 256 * B) (D * k)) (f3 : Γ ⊢[PRAAx] le D B)
    (f4' : Γ ⊢[PRAAx] le one k) (eC : Γ ⊢[PRAAx] C ≐ D + two * B) (eK : Γ ⊢[PRAAx] K ≐ succ k) :
    Γ ⊢[PRAAx] le (two * (D * (Q * Q))) (two * (num 16 * B * R)) := by
  have e1 := natEq eC
  have e2 := natEq eK
  ipra_le 𝔞 Q * (148 * 𝔞 D + 208 * 𝔞 D * sl f4' + 152 * sl f3 + 224 * sl f3 * sl f4' + sl f2 * 𝔞 k +
      𝔞 D * sl f1) + sl h
    with (-16 * 𝔞 Q * 𝔞 K) * e1 + (-16 * 𝔞 Q * (𝔞 D + 2 * 𝔞 B)) * e2

/-- The upper bound: `2 (β#𝓡) ≤ 2 (2DQ²)`. -/
theorem upper_aux {R A D α γ B Q : PTm n} (h1 : Γ ⊢[PRAAx] le R A)
    (h2 : Γ ⊢[PRAAx] le (two * B * A + α * (Q * succ Q)) (γ * (Q * succ Q) + two * B * Q))
    (h3 : Γ ⊢[PRAAx] le B (D * Q)) (h4 : Γ ⊢[PRAAx] le one Q) (eγ : Γ ⊢[PRAAx] γ ≐ α + D) :
    Γ ⊢[PRAAx] le (two * (B * R)) (two * (num 2 * D * (Q * Q))) := by
  have e := natEq eγ
  ipra_le 𝔞 D * 𝔞 Q * sl h4 + 2 * sl h3 * 𝔞 Q + sl h2 + 2 * 𝔞 B * sl h1
    with (-(𝔞 Q * (𝔞 Q + 1))) * e

/-! ## (K3) -/

theorem two_pos : Γ ⊢[PRAAx] (two : PTm n) ≐ succ (pred two) := congrSucc (pred_succ _).eqSymm

/-- (K3): for `J* = (α/β, γ/β)`, `α ≤ γ ≤ β = b₀ + 1`, `D = γ − α`, `Q = 2^k ≤ M` and (K4) `Dk ≥ 256β`,
the reduced fractions `p/q ∈ J*` with `⌊Q/4⌋ < q ≤ Q` satisfy `DQ² ≤ 16β#𝓡` and `β#𝓡 ≤ 2DQ²`,
i.e. `LQ²/32 ≤ #𝓡 ≤ LQ²` for `L = 2D/β`. -/
theorem k3_bounds {α γ b0 M k : PTm n} (hαγ : Γ ⊢[PRAAx] le α γ) (hγ : Γ ⊢[PRAAx] le γ (succ b0))
    (hQM : Γ ⊢[PRAAx] le (pw two k) M) (hK : Γ ⊢[PRAAx] le (num 256 * succ b0) (monus γ α * k)) :
    Γ ⊢[PRAAx] le (monus γ α * (pw two k * pw two k))
        (num 16 * succ b0 * redR (pw two k) (pairT M (pairT α (pairT γ (succ b0))))) ⋏
      le (succ b0 * redR (pw two k) (pairT M (pairT α (pairT γ (succ b0)))))
        (num 2 * monus γ α * (pw two k * pw two k)) := by
  -- the elementary facts
  have eγ : Γ ⊢[PRAAx] γ ≐ α + monus γ α := eq_add_of_le hαγ
  have eγ' := natEq eγ
  have hDγ : Γ ⊢[PRAAx] le (monus γ α) γ := by ipra_le 𝔞 α with eγ'
  have hDB : Γ ⊢[PRAAx] le (monus γ α) (succ b0) := le_trans hDγ hγ
  have hB : Γ ⊢[PRAAx] succ b0 ≐ succ (pred (succ b0)) := congrSucc (pred_succ _).eqSymm
  have hk256 : Γ ⊢[PRAAx] le (num 256) k := by
    refine cancel_le hB ?_
    ipra_le sl hK + 𝔞 k * sl hDB
  have hk4 : Γ ⊢[PRAAx] le (num 4) k := by ipra_le sl hk256 + 252
  have hk1 : Γ ⊢[PRAAx] le one k := by ipra_le sl hk256 + 255
  have hsq := sq_le_two_pow hk4
  have hQ2 : Γ ⊢[PRAAx] le two (pw two k) := by
    ipra_le sl hsq + 65534 + 512 * sl hk256 + sl hk256 * sl hk256
  have hQ1 : Γ ⊢[PRAAx] le one (pw two k) := by ipra_le sl hQ2 + 1
  have hQs : Γ ⊢[PRAAx] pw two k ≐ succ (succ (monus (pw two k) two)) := by
    have e := natEq (eq_add_of_le hQ2)
    apply deriveNat; ipra_simps; linear_combination e
  have dm := div_mod_at (Γ := Γ) (x := pw two k) (y := num 4) (c := num 3) (.eqRefl _)
  have hq4 : Γ ⊢[PRAAx] le (num 4 * quo (pw two k) (num 4)) (pw two k) := le_of_eq_add (Prf.andE₁ dm)
  have hQ' : Γ ⊢[PRAAx] le (quo (pw two k) (num 4)) (pw two k) := by
    ipra_le sl hq4 + 3 * 𝔞 (quo (pw two k) (num 4))
  have hQ'M : Γ ⊢[PRAAx] le (quo (pw two k) (num 4)) M := le_trans hQ' hQM
  have hBDQ : Γ ⊢[PRAAx] le (succ b0) (monus γ α * pw two k) := by
    ipra_le 𝔞 (monus γ α) * sl hsq + 𝔞 k * sl hK + 𝔞 (succ b0) * (256 * sl hk1 + 255)
  -- the counts
  have cnt := count_le (y := pairT M (pairT α (pairT γ (succ b0)))) hQ'
  have k5Q := lattice_core (Γ := Γ) hαγ hγ hQM
  have k5Q' := lattice_core (Γ := Γ) hαγ hγ hQ'M
  have bb := bad_bound hαγ hγ hQM (.eqRefl _) hQs
  refine .andI ?_ ?_
  · have h7 := k7_lower_aux (Prf.andE₁ cnt) (Prf.andE₂ k5Q) (Prf.andE₁ k5Q') hq4 bb eγ
    exact cancel_le two_pos (k4_aux h7 hsq hK hDB hk1 (.eqRefl _) (.eqRefl _))
  · exact cancel_le two_pos (upper_aux (Prf.andE₂ cnt) (Prf.andE₁ k5Q) hBDQ hQ1 eγ)

/-! ## The closed sentence -/

private theorem hyp3' {Δ : List (Fm PTm 5)} {a b c φ : Fm PTm 5} : (a :: b :: c :: φ :: Δ) ⊢[PRAAx] φ :=
  Prf.hyp (by simp)

/-- Variables `0 = α`, `1 = γ`, `2 = b₀`, `3 = M`, `4 = k`. -/
def k3Formula : Fm PTm 5 :=
  le (var 0) (var 1) ⟶ (le (var 1) (succ (var 2)) ⟶ (le (pw two (var 4)) (var 3) ⟶
    (le (num 256 * succ (var 2)) (monus (var 1) (var 0) * var 4) ⟶
      (le (monus (var 1) (var 0) * (pw two (var 4) * pw two (var 4)))
          (num 16 * succ (var 2) * redR (pw two (var 4)) (pairT (var 3) (pairT (var 0) (pairT (var 1) (succ (var 2)))))) ⋏
        le (succ (var 2) * redR (pw two (var 4)) (pairT (var 3) (pairT (var 0) (pairT (var 1) (succ (var 2))))))
          (num 2 * monus (var 1) (var 0) * (pw two (var 4) * pw two (var 4)))))))

/-- (K3), as a closed sentence of iPRA. -/
theorem k3_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 k3Formula :=
  closeUniv 5 (.impI (.impI (.impI (.impI (k3_bounds hyp3' hyp2 Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinReduced
