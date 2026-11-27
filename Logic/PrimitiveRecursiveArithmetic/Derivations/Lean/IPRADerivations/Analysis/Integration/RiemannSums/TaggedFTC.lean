import IPRADerivations.Core.SumLemmas
import IPRADerivations.Core.OrderCertificates

/-!
# The finite tagged-division estimate of the fundamental theorem

Packet: `analysis/calculus_ipra`, Theorem `thm:taggedFTC` ("FTC II with effective tagged divisions"), the
finite estimate `eq:taggedfinite` of its proof: "the cell error is at most
`(x_{i+1} − x_i) ε_k + (4 + x_{i+1} − x_i) ε_p`. Summing and telescoping gives
`|H(b, p) − H(a, p) − S(𝒫(k), p)| ≤ L ε_k + (4N + L) ε_p`."

For an arbitrary (not necessarily uniform) division with cell widths `Δ(j, x)`, sampled values `G(j, x)`
of the antiderivative at the division points, and the tagged terms `f(t_j) Δ_j` given by their positive
and negative parts `F⁺(j, x)`, `F⁻(j, x)`; `D(J) = ∑_{j<J} Δ_j` (so `D(N) = L`):

* `tagged_upper`: if `G(j + 1) + F⁻(j) ≤ G(j) + F⁺(j) + Δ_j ε_k + (4 + Δ_j) ε_p` for `j < N`, then
  `G(N) + ∑ F⁻ ≤ G(0) + ∑ F⁺ + D(N) ε_k + (4N + D(N)) ε_p`;
* `tagged_lower`: the reverse inequality from the reverse cell hypothesis.

Together: `|G(N) − G(0) − ∑ (F⁺ − F⁻)| ≤ L ε_k + (4N + L) ε_p`. The constant-error case is
`Analysis/FiniteFTC`. The cell estimate itself (from the pointwise derivative contract at the tag) and
the passage to names are not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.TaggedFTC

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

section Tagged

variable (G Hp Hm Δ : PTm 2)

/-- The upper invariant at the cell count `J`. -/
abbrev UInv (ek ep J x : PTm n) : Fm PTm n :=
  le (inst2 G J x + ap2 (sumF Hm) J x)
    (inst2 G zero x + ap2 (sumF Hp) J x + ap2 (sumF Δ) J x * ek + (num 4 * J + ap2 (sumF Δ) J x) * ep)

/-- The lower invariant at the cell count `J`. -/
abbrev LInv (ek ep J x : PTm n) : Fm PTm n :=
  le (inst2 G zero x + ap2 (sumF Hp) J x)
    (inst2 G J x + ap2 (sumF Hm) J x + ap2 (sumF Δ) J x * ek + (num 4 * J + ap2 (sumF Δ) J x) * ep)

theorem u_base (ek ep x : PTm n) : Γ ⊢[PRAAx] UInv G Hp Hm Δ ek ep zero x := by
  have zp := natEq (sum_zero (Γ := Γ) Hp x)
  have zm := natEq (sum_zero (Γ := Γ) Hm x)
  have zd := natEq (sum_zero (Γ := Γ) Δ x)
  ipra_le 0 using linear_combination zp + (𝔟 ek + 𝔟 ep) * zd - zm

theorem l_base (ek ep x : PTm n) : Γ ⊢[PRAAx] LInv G Hp Hm Δ ek ep zero x := by
  have zp := natEq (sum_zero (Γ := Γ) Hp x)
  have zm := natEq (sum_zero (Γ := Γ) Hm x)
  have zd := natEq (sum_zero (Γ := Γ) Δ x)
  ipra_le 0 using linear_combination zm + (𝔟 ek + 𝔟 ep) * zd - zp

theorem u_step {ek ep J x : PTm n}
    (c : Γ ⊢[PRAAx] le (inst2 G (succ J) x + inst2 Hm J x)
      (inst2 G J x + inst2 Hp J x + inst2 Δ J x * ek + (num 4 + inst2 Δ J x) * ep))
    (ih : Γ ⊢[PRAAx] UInv G Hp Hm Δ ek ep J x) : Γ ⊢[PRAAx] UInv G Hp Hm Δ ek ep (succ J) x := by
  have ap := natEq (sum_succ' (Γ := Γ) Hp J x)
  have am := natEq (sum_succ' (Γ := Γ) Hm J x)
  have ad := natEq (sum_succ' (Γ := Γ) Δ J x)
  ipra_le sl ih + sl c using linear_combination ap + (𝔟 ek + 𝔟 ep) * ad - am

theorem l_step {ek ep J x : PTm n}
    (c : Γ ⊢[PRAAx] le (inst2 G J x + inst2 Hp J x)
      (inst2 G (succ J) x + inst2 Hm J x + inst2 Δ J x * ek + (num 4 + inst2 Δ J x) * ep))
    (ih : Γ ⊢[PRAAx] LInv G Hp Hm Δ ek ep J x) : Γ ⊢[PRAAx] LInv G Hp Hm Δ ek ep (succ J) x := by
  have ap := natEq (sum_succ' (Γ := Γ) Hp J x)
  have am := natEq (sum_succ' (Γ := Γ) Hm J x)
  have ad := natEq (sum_succ' (Γ := Γ) Δ J x)
  ipra_le sl ih + sl c using linear_combination am + (𝔟 ek + 𝔟 ep) * ad - ap

theorem u_guard {ek ep J N x : PTm n} (hJ : Γ ⊢[PRAAx] le (succ J) N)
    (c : Γ ⊢[PRAAx] lt J N ⟶ le (inst2 G (succ J) x + inst2 Hm J x)
      (inst2 G J x + inst2 Hp J x + inst2 Δ J x * ek + (num 4 + inst2 Δ J x) * ep))
    (ih : Γ ⊢[PRAAx] le J N ⟶ UInv G Hp Hm Δ ek ep J x) :
    Γ ⊢[PRAAx] UInv G Hp Hm Δ ek ep (succ J) x :=
  u_step G Hp Hm Δ (Prf.impE c hJ) (Prf.impE ih (le_trans (le_succ_self J) hJ))

theorem l_guard {ek ep J N x : PTm n} (hJ : Γ ⊢[PRAAx] le (succ J) N)
    (c : Γ ⊢[PRAAx] lt J N ⟶ le (inst2 G J x + inst2 Hp J x)
      (inst2 G (succ J) x + inst2 Hm J x + inst2 Δ J x * ek + (num 4 + inst2 Δ J x) * ep))
    (ih : Γ ⊢[PRAAx] le J N ⟶ LInv G Hp Hm Δ ek ep J x) :
    Γ ⊢[PRAAx] LInv G Hp Hm Δ ek ep (succ J) x :=
  l_step G Hp Hm Δ (Prf.impE c hJ) (Prf.impE ih (le_trans (le_succ_self J) hJ))

/-- `eq:taggedfinite`, upper side. -/
theorem tagged_upper {ek ep N x : PTm n}
    (c : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 G (succ (var 0)) (Syn.shift x) + inst2 Hm (var 0) (Syn.shift x))
        (inst2 G (var 0) (Syn.shift x) + inst2 Hp (var 0) (Syn.shift x) +
          inst2 Δ (var 0) (Syn.shift x) * Syn.shift ek +
          (num 4 + inst2 Δ (var 0) (Syn.shift x)) * Syn.shift ep))) :
    Γ ⊢[PRAAx] UInv G Hp Hm Δ ek ep N x := by
  let P := UInv G Hp Hm Δ (Syn.shift ek) (Syn.shift ep) (var 0) (Syn.shift x)
  have atBound : Γ ⊢[PRAAx] P.subst (Syn.inst N) := by
    refine qfIndUpTo N (le_QF _ _) ?_ ?_
    · simpa [P, UInv] using u_base (Γ := Γ) G Hp Hm Δ ek ep x
    · ipra_ind_simp [P, UInv, subst_le, subst_ap2, subst_inst2, subst_repl_shift]
      exact .impI (u_step G Hp Hm Δ (.impE c.allOpen.wk.wk Prf.hyp0) Prf.hyp1)
  simpa [P, UInv] using atBound

/-- `eq:taggedfinite`, lower side. -/
theorem tagged_lower {ek ep N x : PTm n}
    (c : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 G (var 0) (Syn.shift x) + inst2 Hp (var 0) (Syn.shift x))
        (inst2 G (succ (var 0)) (Syn.shift x) + inst2 Hm (var 0) (Syn.shift x) +
          inst2 Δ (var 0) (Syn.shift x) * Syn.shift ek +
          (num 4 + inst2 Δ (var 0) (Syn.shift x)) * Syn.shift ep))) :
    Γ ⊢[PRAAx] LInv G Hp Hm Δ ek ep N x := by
  let P := LInv G Hp Hm Δ (Syn.shift ek) (Syn.shift ep) (var 0) (Syn.shift x)
  have atBound : Γ ⊢[PRAAx] P.subst (Syn.inst N) := by
    refine qfIndUpTo N (le_QF _ _) ?_ ?_
    · simpa [P, LInv] using l_base (Γ := Γ) G Hp Hm Δ ek ep x
    · ipra_ind_simp [P, LInv, subst_le, subst_ap2, subst_inst2, subst_repl_shift]
      exact .impI (l_step G Hp Hm Δ (.impE c.allOpen.wk.wk Prf.hyp0) Prf.hyp1)
  simpa [P, LInv] using atBound

end Tagged

end LeanProofs.IPRA.Analysis.TaggedFTC
