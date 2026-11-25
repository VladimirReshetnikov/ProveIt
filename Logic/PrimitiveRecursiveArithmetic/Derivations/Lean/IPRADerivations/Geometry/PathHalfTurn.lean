import IPRADerivations.Geometry.PathShoelace
import IPRADerivations.Combinatorics.CatalanPowers
import IPRADerivations.Core.SumSplit
import IPRADerivations.Geometry.ConwayAlgebra
import IPRADerivations.Core.LinearCombination

/-!
# The half-turn law, concatenation and centrally symmetric paths (`lem:Jlaws`, `lem:Jcentral`)

Packet: `geometry/conway_criterion_ipra_2026-11-16`, `lem:Jlaws` (`eq:Jconcat`, `eq:Jhalf`) and
`lem:Jcentral`. `Geometry/PathShoelace` derives `eq:Jtranslate` and `eq:Jreverse` for the
open-path shoelace functional `J = ∑_{i<n} det(p_i, p_{i+1})` of a path with coordinate terms
`x(i, p)`, `y(i, p)`, written as the pair of natural-number sums `J⁺ = ∑ x_i y_{i+1}` (`jp`) and
`J⁻ = ∑ x_{i+1} y_i` (`jm`).

**The half-turn law.** A second path `x′(i, q)`, `y′(i, q)` is the half-turn of the first about
the doubled centre `s = (s₁, s₂)` on the indices `i ≤ N` when `x′_i + x_i = s₁` and
`y′_i + y_i = s₂` there; this hypothesis is the bounded bit `halfBit … ≐ 1`
(`Foundations/BoundedReflection`, through `Combinatorics/CatalanPowers.eqB`), read by
`half_at`. Natural numbers and the hypothesis replace the subtraction `s − p`.

* `half_step`, `J_half` (`eq:Jhalf`): `J(Q) = J(P) + det(s, p_0 − p_N)`, as the equation of
  natural numbers `J⁺(Q) + J⁻(P) + s₁ y_N + s₂ x_0 = J⁻(Q) + J⁺(P) + s₁ y_0 + s₂ x_N`, by
  quantifier-free induction on the number of edges `m ≤ N` (the formula `m ≤ N → …`) with a
  polynomial step. The packet's route (negate, then translate) needs negative coordinates; the
  induction here is direct.

**Concatenation.** `J_concat_plus`, `J_concat_minus` (`eq:Jconcat`): the sums over the first
`M + K` edges split as the sums over the first `M` edges plus the sums of the path
`p_M, …, p_{M+K}` (`offB` of `Core/SumSplit`, reindexed from `0`): `J(P * Q) = J(P) + J(Q)` for
the two pieces of one path.

**Centrally symmetric paths.** `J_central` (`lem:Jcentral`): if the reversed path
`i ↦ p_{N ∸ i}` is the half-turn of `P` about `p_0 + p_N` on `i ≤ N`, then
`J⁺(P) + x_N y_0 = J⁻(P) + x_0 y_N`, that is `J(P) = det(p_0, p_N)` (`eq:Jcentral`): from
`J_half` with `J_reverse_plus`, `J_reverse_minus` one gets the doubled equation, and the
cancellation of the numeral `2` is `Geometry/ConwayAlgebra.cancel_two_nat`.
-/

namespace LeanProofs.IPRA.Geometry.PathHalfTurn

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)
open LeanProofs.IPRA.Geometry.PathShoelace (mB inst2_mB jp jm rvB rvB_at
  J_reverse_plus J_reverse_minus)
open LeanProofs.IPRA.Combinatorics.CatalanPowers (eqB allEq_elim shift_pair shift_succ shift_zero
  lt_succ_of_le)
open LeanProofs.IPRA.Foundations.BoundedReflection (allB)
open LeanProofs.IPRA.Geometry.ConwayAlgebra (cancel_two_nat)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The bounded half-turn hypothesis -/

/-- `s`; variables `0 = i`, `1 = ⟨s, ⟨q, p⟩⟩`. -/
def hR : PTm 2 := fstT (var 1)

theorem hR_at (i s q p : PTm k) : Γ ⊢[PRAAx] inst2 hR i (pairT s (pairT q p)) ≐ s := by
  have e : inst2 hR i (pairT s (pairT q p)) = fstT (pairT s (pairT q p)) := by
    show Syn.subst ![i, pairT s (pairT q p)] hR = _
    simp [hR]
  rw [e]
  exact fst_pair _ _

section Bit

variable (z z' : PTm 2)

/-- `z′(i, q) + z(i, p)`; variables `0 = i`, `1 = ⟨s, ⟨q, p⟩⟩`. -/
def hL : PTm 2 := inst2 z' (var 0) (fstT (sndT (var 1))) + inst2 z (var 0) (sndT (sndT (var 1)))

theorem hL_at (i s q p : PTm k) :
    Γ ⊢[PRAAx] inst2 (hL z z') i (pairT s (pairT q p)) ≐ inst2 z' i q + inst2 z i p := by
  have e : inst2 (hL z z') i (pairT s (pairT q p)) =
      inst2 z' i (fstT (sndT (pairT s (pairT q p)))) +
        inst2 z i (sndT (sndT (pairT s (pairT q p)))) := by
    show Syn.subst ![i, pairT s (pairT q p)] (hL z z') = _
    simp [hL]
  rw [e]
  exact congrAdd (congrInst2 z' (.eqRefl _) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)))
    (congrInst2 z (.eqRefl _) ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)))

/-- The bit of `∀ i < B, z′(i, q) + z(i, p) = s`. -/
abbrev halfBit (B s q p : PTm k) : PTm k := allB (eqB (hL z z') hR) B (pairT s (pairT q p))

/-- Reading the half-turn hypothesis at an index `i < B`. -/
theorem half_at {B s q p i : PTm k} (h : Γ ⊢[PRAAx] halfBit z z' B s q p ≐ one)
    (hi : Γ ⊢[PRAAx] lt i B) : Γ ⊢[PRAAx] inst2 z' i q + inst2 z i p ≐ s :=
  (hL_at z z' i s q p).eqSymm.eqTrans ((allEq_elim (hL z z') hR h hi).eqTrans (hR_at i s q p))

end Bit

/-! ## The half-turn law -/

section Half

variable (x y x' y' : PTm 2)

/-- The cleared form of `eq:Jhalf` after `m` edges. -/
abbrev halfEq (m s₁ s₂ q p : PTm k) : Fm PTm k :=
  jp x' y' m q + jm x y m p + s₁ * inst2 y m p + s₂ * inst2 x zero p ≐
    jm x' y' m q + jp x y m p + s₁ * inst2 y zero p + s₂ * inst2 x m p

/-- One more edge. -/
theorem half_step {B n s₁ s₂ q p : PTm k}
    (hx : Γ ⊢[PRAAx] halfBit x x' B s₁ q p ≐ one) (hy : Γ ⊢[PRAAx] halfBit y y' B s₂ q p ≐ one)
    (h₀ : Γ ⊢[PRAAx] lt n B) (h₁ : Γ ⊢[PRAAx] lt (succ n) B)
    (ih : Γ ⊢[PRAAx] halfEq x y x' y' n s₁ s₂ q p) :
    Γ ⊢[PRAAx] halfEq x y x' y' (succ n) s₁ s₂ q p := by
  have s₁' := sum_succ' (Γ := Γ) (PathShoelace.pB x' y') n q
  rw [PathShoelace.inst2_pB] at s₁'
  have s₂' := sum_succ' (Γ := Γ) (mB x y) n p
  rw [inst2_mB] at s₂'
  have s₃' := sum_succ' (Γ := Γ) (mB x' y') n q
  rw [inst2_mB] at s₃'
  have s₄' := sum_succ' (Γ := Γ) (PathShoelace.pB x y) n p
  rw [PathShoelace.inst2_pB] at s₄'
  ipra_lc natEq ih + natEq s₁' + natEq s₂' - natEq s₃' - natEq s₄' +
    𝔞 (inst2 y' (succ n) q) * natEq (half_at x x' hx h₀) + (𝔞 s₁ - 𝔞 (inst2 x n p)) * natEq (half_at y y' hy h₁) -
    𝔞 (inst2 y' n q) * natEq (half_at x x' hx h₁) - (𝔞 s₁ - 𝔞 (inst2 x (succ n) p)) * natEq (half_at y y' hy h₀)

/-- The induction formula of `J_half`; variable `0 = m`. -/
abbrev halfF (N s₁ s₂ q p : PTm k) : Fm PTm (k + 1) :=
  le (var 0) (Syn.shift N) ⟶
    halfEq x y x' y' (var 0) (Syn.shift s₁) (Syn.shift s₂) (Syn.shift q) (Syn.shift p)

/-- `eq:Jhalf`: if `x′_i + x_i = s₁` and `y′_i + y_i = s₂` for `i ≤ N`, then
`J(Q) = J(P) + det(s, p_0 − p_N)`, as an equation of natural numbers. -/
theorem J_half {N s₁ s₂ q p : PTm k}
    (hx : Γ ⊢[PRAAx] halfBit x x' (succ N) s₁ q p ≐ one)
    (hy : Γ ⊢[PRAAx] halfBit y y' (succ N) s₂ q p ≐ one) :
    Γ ⊢[PRAAx] halfEq x y x' y' N s₁ s₂ q p := by
  have hall : Γ ⊢[PRAAx] Fm.all (halfF x y x' y' N s₁ s₂ q p) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · have z₁ := natEq (sum_zero (Γ := le zero N :: Γ) (PathShoelace.pB x' y') q)
      have b : Γ ⊢[PRAAx] le zero N ⟶ halfEq x y x' y' zero s₁ s₂ q p := by
        refine .impI ?_
        ipra_lc z₁ + natEq (sum_zero (Γ := le zero N :: Γ) (mB x y) p) -
          natEq (sum_zero (Γ := le zero N :: Γ) (mB x' y') q) -
          natEq (sum_zero (Γ := le zero N :: Γ) (PathShoelace.pB x y) p)
      simpa using b
    · have hx' : (Γ.map Fm.shift) ⊢[PRAAx]
          halfBit x x' (succ (Syn.shift N)) (Syn.shift s₁) (Syn.shift q) (Syn.shift p) ≐ one := by
        simpa [Fm.shift, Syn.shift] using hx.shift
      have hy' : (Γ.map Fm.shift) ⊢[PRAAx]
          halfBit y y' (succ (Syn.shift N)) (Syn.shift s₂) (Syn.shift q) (Syn.shift p) ≐ one := by
        simpa [Fm.shift, Syn.shift] using hy.shift
      have st : (halfF x y x' y' N s₁ s₂ q p :: Γ.map Fm.shift) ⊢[PRAAx]
          le (succ (var 0)) (Syn.shift N) ⟶
            halfEq x y x' y' (succ (var 0)) (Syn.shift s₁) (Syn.shift s₂) (Syn.shift q)
              (Syn.shift p) := by
        refine .impI ?_
        have hle : (le (succ (var 0)) (Syn.shift N) :: halfF x y x' y' N s₁ s₂ q p ::
            Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
          le_trans (le_succ_self _) Prf.hyp0
        have l₀ : (le (succ (var 0)) (Syn.shift N) :: halfF x y x' y' N s₁ s₂ q p ::
            Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (succ (Syn.shift N)) :=
          lt_succ_of_le hle
        have l₁ : (le (succ (var 0)) (Syn.shift N) :: halfF x y x' y' N s₁ s₂ q p ::
            Γ.map Fm.shift) ⊢[PRAAx] lt (succ (var 0)) (succ (Syn.shift N)) :=
          lt_succ_of_le Prf.hyp0
        exact half_step x y x' y' hx'.wk.wk hy'.wk.wk l₀ l₁ (.impE Prf.hyp1 hle)
      simpa [subst_repl_shift, Syn.repl_zero] using st
  have h2 := Prf.allE N hall
  simp only [halfF, halfEq, Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, PTm.subst_add,
    PTm.subst_mul, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero] at h2
  exact .impE h2 (le_refl N)

end Half

/-! ## Concatenation -/

section Concat

variable (x y : PTm 2)

theorem concat_pt_plus (i M p : PTm k) :
    Γ ⊢[PRAAx] inst2 (offB (PathShoelace.pB x y)) i (pairT M p) ≐
      inst2 (PathShoelace.pB (offB x) (offB y)) i (pairT M p) := by
  rw [inst2_offB, PathShoelace.inst2_pB, PathShoelace.inst2_pB, inst2_offB, inst2_offB]
  exact congrMul (.eqRefl _)
    (congrInst2 y (add_succ _ _).eqSymm (.eqRefl _))

theorem concat_pt_minus (i M p : PTm k) :
    Γ ⊢[PRAAx] inst2 (offB (mB x y)) i (pairT M p) ≐
      inst2 (mB (offB x) (offB y)) i (pairT M p) := by
  rw [inst2_offB, inst2_mB, inst2_mB, inst2_offB, inst2_offB]
  exact congrMul
    (congrInst2 x (add_succ _ _).eqSymm (.eqRefl _)) (.eqRefl _)

/-- `eq:Jconcat`, the sums `J⁺`: the first `M + K` edges are the first `M` edges followed by
the path `p_M, …, p_{M+K}`. -/
theorem J_concat_plus (M K p : PTm k) :
    Γ ⊢[PRAAx] jp x y (M + K) p ≐ jp x y M p + jp (offB x) (offB y) K (pairT M p) := by
  refine (sum_split (PathShoelace.pB x y) M K p).eqTrans (congrAdd (.eqRefl _) ?_)
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [shift_pair]
  exact concat_pt_plus x y _ _ _

/-- `eq:Jconcat`, the sums `J⁻`. -/
theorem J_concat_minus (M K p : PTm k) :
    Γ ⊢[PRAAx] jm x y (M + K) p ≐ jm x y M p + jm (offB x) (offB y) K (pairT M p) := by
  refine (sum_split (mB x y) M K p).eqTrans (congrAdd (.eqRefl _) ?_)
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [shift_pair]
  exact concat_pt_minus x y _ _ _

end Concat

/-! ## Centrally symmetric paths -/

section Central

variable (x y : PTm 2)

/-- `lem:Jcentral`: if the reversed path `i ↦ p_{N ∸ i}` is the half-turn of `P` about
`p_0 + p_N` on `i ≤ N`, then `J⁺(P) + x_N y_0 = J⁻(P) + x_0 y_N`, i.e. `J(P) = det(p_0, p_N)`. -/
theorem J_central {N p : PTm k}
    (hx : Γ ⊢[PRAAx]
      halfBit x (rvB x) (succ N) (inst2 x zero p + inst2 x N p) (pairT N p) p ≐ one)
    (hy : Γ ⊢[PRAAx]
      halfBit y (rvB y) (succ N) (inst2 y zero p + inst2 y N p) (pairT N p) p ≐ one) :
    Γ ⊢[PRAAx] jp x y N p + inst2 x N p * inst2 y zero p ≐
      jm x y N p + inst2 x zero p * inst2 y N p := by
  refine cancel_two_nat ?_
  ipra_lc -natEq (J_half x y (rvB x) (rvB y) hx hy) + natEq (J_reverse_plus (Γ := Γ) x y N p) -
    natEq (J_reverse_minus (Γ := Γ) x y N p)

end Central

end LeanProofs.IPRA.Geometry.PathHalfTurn
