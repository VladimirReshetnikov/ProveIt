import IPRADerivations.Core.Search
import IPRADerivations.Core.Powers
import IPRADerivations.Foundations.Adjunction

/-!
# Square roots without zero testing (`ipra_evidence_framework`, worked example)

Packet: `foundations/ipra_evidence_framework`, Section "Set-valued precision names instead of
discontinuous choice", worked example "square roots without zero testing". For an exact
nonnegative rational `a = u / v` (`v ≥ 1`) and precision `n`, the packet chooses

`j_n` = the least integer `j` with `j² ≥ a · 2^{2n}`,

and states that consecutive choices are compatible by "a direct integer comparison ...
without mentioning `√a`". Here `j_n` is the bounded search `jn u v n` for the least `j` with
`u · (2^n)² ≤ j² · v`, below the bound `u · 2^n + 2`. Derived, for `v ≥ 1`:

* `sqrt_cross`: `u · (2^n)² ≤ j_n² · v` (the crossing exists, at `u · 2^n + 1` at the latest);
* `sqrt_below`: `i² · v < u · (2^n)²` for every `i < j_n` (it is the first crossing);
* `sqrt_upper`: `j_{n+1} ≤ 2 j_n`;
* `sqrt_lower`: `2 j_n ≤ j_{n+1} + 1`;
* `sqrt_compatible`: both, as one closed sentence of iPRA.

So `|2 j_n − j_{n+1}| ≤ 1` (the packet states the bound `2`), that is
`|j_n / 2^n − j_{n+1} / 2^{n+1}| ≤ 2^{−(n+1)}`: the dyadic names of `√a` at consecutive
precisions are compatible, by integer comparisons only. No square root, no zero test on `a`
and no division occurs.

The finite relational name `L_n(a)`, its residual bound and the compatibility relation `T` of
the packet are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.SquareRootNames

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Search (mu search_found search_minimal)
open LeanProofs.IPRA.Foundations.Adjunction (par_le_one)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The defect `u · (2^n)² ∸ j² · v`, zero exactly when `j² ≥ (u / v) · 4^n`; variables
`0 = j`, `1 = ⟨u, ⟨v, n⟩⟩`. -/
def f : PTm 2 :=
  monus (fstT (var 1) * (pw two (sndT (sndT (var 1))) * pw two (sndT (sndT (var 1)))))
    (var 0 * var 0 * fstT (sndT (var 1)))

theorem f_at (j u v n : PTm k) :
    Γ ⊢[PRAAx] inst2 f j (pairT u (pairT v n)) ≐
      monus (u * (pw two n * pw two n)) (j * j * v) := by
  have e₁ : inst2 f j (pairT u (pairT v n)) =
      Syn.subst ![j, fstT (pairT u (pairT v n)), fstT (sndT (pairT u (pairT v n))),
          sndT (sndT (pairT u (pairT v n)))]
        (monus ((var 1 : PTm 4) * (pw two (var 3) * pw two (var 3))) (var 0 * var 0 * var 2)) := by
    show Syn.subst ![j, pairT u (pairT v n)] f = _
    simp [f]
  have e₂ : monus (u * (pw two n * pw two n)) (j * j * v) =
      Syn.subst ![j, u, v, n]
        (monus ((var 1 : PTm 4) * (pw two (var 3) * pw two (var 3))) (var 0 * var 0 * var 2)) := by
    simp
  rw [e₁, e₂]
  have s : Γ ⊢[PRAAx] sndT (pairT u (pairT v n)) ≐ pairT v n := snd_pair _ _
  exact Prf.eqCongr _ fun l => by
    fin_cases l
    · exact .eqRefl _
    · exact fst_pair _ _
    · exact (congrFst s).eqTrans (fst_pair _ _)
    · exact (congrSnd s).eqTrans (snd_pair _ _)

/-- `j_n`: the least `j < u · 2^n + 2` with `u · (2^n)² ≤ j² · v`. -/
def jn (u v n : PTm k) : PTm k := mu f (succ (succ (u * pw two n))) (pairT u (pairT v n))

/-- The crossing condition at `j` from the vanishing of the defect, and conversely. -/
theorem le_of_f {j u v n : PTm k} (h : Γ ⊢[PRAAx] inst2 f j (pairT u (pairT v n)) ≐ zero) :
    Γ ⊢[PRAAx] le (u * (pw two n * pw two n)) (j * j * v) :=
  (f_at j u v n).eqSymm.eqTrans h

theorem f_of_le {j u v n : PTm k} (h : Γ ⊢[PRAAx] le (u * (pw two n * pw two n)) (j * j * v)) :
    Γ ⊢[PRAAx] inst2 f j (pairT u (pairT v n)) ≐ zero :=
  (f_at j u v n).eqTrans h

/-- The candidate `u · 2^n + 1` crosses. -/
theorem top_cross {u v n : PTm k} (hv : Γ ⊢[PRAAx] v ≐ succ (pred v)) :
    Γ ⊢[PRAAx] le (u * (pw two n * pw two n))
      (succ (u * pw two n) * succ (u * pw two n) * v) := by
  have ev := natEq hv
  refine .orE (zero_or_succ u) ?_ ?_
  · have eu := natEq (Prf.hyp0 (Γ := Γ) (φ := u ≐ zero))
    have ev' := natEq (hv.wk (ψ := u ≐ zero))
    refine le_of_eq_add (d := succ (u * pw two n) * succ (u * pw two n) * v) ?_
    apply deriveNat; ipra_simps
    linear_combination (-(𝔞 (pw two n) * 𝔞 (pw two n))) * eu
  · have eu := natEq (Prf.hyp0 (Γ := Γ) (φ := u ≐ succ (pred u)))
    have ev' := natEq (hv.wk (ψ := u ≐ succ (pred u)))
    refine le_of_eq_add (d := pred u * u * (pw two n * pw two n) +
      (u * pw two n) * (u * pw two n) * pred v + two * (u * pw two n) * v + v) ?_
    apply deriveNat; ipra_simps
    linear_combination (𝔞 u * 𝔞 u * 𝔞 (pw two n) * 𝔞 (pw two n)) * ev' +
      (𝔞 u * 𝔞 (pw two n) * 𝔞 (pw two n)) * eu

/-- The crossing exists: `u · (2^n)² ≤ j_n² · v`. -/
theorem sqrt_cross {u v : PTm k} (hv : Γ ⊢[PRAAx] v ≐ succ (pred v)) (n : PTm k) :
    Γ ⊢[PRAAx] le (u * (pw two n * pw two n)) (jn u v n * jn u v n * v) :=
  le_of_f (Prf.andE₁ (Prf.andE₂
    (search_found (f_of_le (top_cross hv)) (le_refl (succ (succ (u * pw two n)))))))

/-- It is the first crossing: `i² · v < u · (2^n)²` for `i < j_n`. -/
theorem sqrt_below {u v n i : PTm k} (hi : Γ ⊢[PRAAx] lt i (jn u v n)) :
    Γ ⊢[PRAAx] lt (i * i * v) (u * (pw two n * pw two n)) := by
  have m := search_minimal (f := f) hi
  refine .orE (lt_or_le (i * i * v) (u * (pw two n * pw two n))) Prf.hyp0 ?_
  exact .botE _ (.impE m.wk (f_of_le Prf.hyp0))

/-- `j_{n+1} ≤ 2 j_n`: the doubled index crosses at the next precision. -/
theorem sqrt_upper {u v : PTm k} (hv : Γ ⊢[PRAAx] v ≐ succ (pred v)) (n : PTm k) :
    Γ ⊢[PRAAx] le (jn u v (succ n)) (two * jn u v n) := by
  refine .orE (lt_or_le (two * jn u v n) (jn u v (succ n))) ?_ Prf.hyp0
  have m := search_minimal (f := f)
    (Prf.hyp0 (Γ := Γ) (φ := lt (two * jn u v n) (jn u v (succ n))))
  refine .botE _ (.impE m (f_of_le ?_))
  have e := natEq (eq_add_of_le (sqrt_cross (Γ := lt (two * jn u v n) (jn u v (succ n)) :: Γ)
    (u := u) hv.wk n))
  have ep := natEq (pw_succ (Γ := lt (two * jn u v n) (jn u v (succ n)) :: Γ) two n)
  refine le_of_eq_add (d := (two * two) *
    monus (jn u v n * jn u v n * v) (u * (pw two n * pw two n))) ?_
  apply deriveNat; ipra_simps
  linear_combination 4 * e - 𝔞 u * (𝔞 (pw two (succ n)) + 2 * 𝔞 (pw two n)) * ep

private theorem half_up (j' : PTm k) : Γ ⊢[PRAAx] le j' (two * half (succ j')) := by
  have e₁ := natEq (half_par (Γ := Γ) (succ j'))
  have e₂ := natEq (eq_add_of_le (par_le_one (Γ := Γ) (succ j')))
  refine le_of_eq_add (d := monus one (par (succ j'))) ?_
  apply deriveNat; ipra_simps
  linear_combination e₂ - e₁

private theorem half_lt {j j' : PTm k} (h : Γ ⊢[PRAAx] lt (succ j') (two * j)) :
    Γ ⊢[PRAAx] lt (half (succ j')) j := by
  refine .orE (lt_or_le (half (succ j')) j) Prf.hyp0 ?_
  have e₁ := natEq (half_par (Γ := le j (half (succ j')) :: Γ) (succ j'))
  have ea := natEq (eq_add_of_le (h.wk (ψ := le j (half (succ j')))))
  have eb := natEq (eq_add_of_le (Prf.hyp0 (Γ := Γ) (φ := le j (half (succ j')))))
  refine not_succ_le_self (succ j') _ (le_of_eq_add
    (d := monus (two * j) (succ (succ j')) + two * monus (half (succ j')) j + par (succ j')) ?_)
  apply deriveNat; ipra_simps
  linear_combination e₁ + 2 * eb + ea

private theorem half_cross {u v n j' : PTm k}
    (hc : Γ ⊢[PRAAx] le (u * (pw two (succ n) * pw two (succ n))) (j' * j' * v)) :
    Γ ⊢[PRAAx] le (u * (pw two n * pw two n)) (half (succ j') * half (succ j') * v) := by
  refine .orE (lt_or_le (half (succ j') * half (succ j') * v) (u * (pw two n * pw two n))) ?_
    Prf.hyp0
  have ec := natEq (eq_add_of_le (hc.wk
    (ψ := lt (half (succ j') * half (succ j') * v) (u * (pw two n * pw two n)))))
  have et := natEq (eq_add_of_le (half_up
    (Γ := lt (half (succ j') * half (succ j') * v) (u * (pw two n * pw two n)) :: Γ) j'))
  have es := natEq (eq_add_of_le (Prf.hyp0 (Γ := Γ)
    (φ := lt (half (succ j') * half (succ j') * v) (u * (pw two n * pw two n)))))
  have ep := natEq (pw_succ
    (Γ := lt (half (succ j') * half (succ j') * v) (u * (pw two n * pw two n)) :: Γ) two n)
  refine not_succ_le_self (j' * j' * v) _ (le_of_eq_add
    (d := two * j' * monus (two * half (succ j')) j' * v +
      monus (two * half (succ j')) j' * monus (two * half (succ j')) j' * v +
      succ (two * one) + (two * two) * monus (u * (pw two n * pw two n))
        (succ (half (succ j') * half (succ j') * v)) +
      monus (j' * j' * v) (u * (pw two (succ n) * pw two (succ n)))) ?_)
  apply deriveNat; ipra_simps
  linear_combination ec + 𝔞 u * (𝔞 (pw two (succ n)) + 2 * 𝔞 (pw two n)) * ep + 4 * es +
    𝔞 v * (2 * 𝔞 (half (succ j')) + 𝔞 j' + 𝔞 (monus (two * half (succ j')) j')) * et

/-- `2 j_n ≤ j_{n+1} + 1`: otherwise `⌈j_{n+1} / 2⌉ < j_n` would already cross at precision
`n`. -/
theorem sqrt_lower {u v : PTm k} (hv : Γ ⊢[PRAAx] v ≐ succ (pred v)) (n : PTm k) :
    Γ ⊢[PRAAx] le (two * jn u v n) (succ (jn u v (succ n))) := by
  refine .orE (lt_or_le (succ (jn u v (succ n))) (two * jn u v n)) ?_ Prf.hyp0
  have hl := half_lt (Prf.hyp0 (Γ := Γ) (φ := lt (succ (jn u v (succ n))) (two * jn u v n)))
  have m := search_minimal (f := f) hl
  exact .botE _ (.impE m (f_of_le (half_cross (sqrt_cross hv.wk (succ n)))))

/-- Compatibility of the dyadic square-root names at consecutive precisions, as one closed
sentence: for `v ≥ 1`, `j_{n+1} ≤ 2 j_n ≤ j_{n+1} + 1`. Variables: `0 = u`, `1 = v`,
`2 = n`. -/
theorem sqrt_compatible : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((var 1 ≐ succ (pred (var 1))) ⟶
      (le (jn (var 0) (var 1) (succ (var 2))) (two * jn (var 0) (var 1) (var 2)) ⋏
        le (two * jn (var 0) (var 1) (var 2)) (succ (jn (var 0) (var 1) (succ (var 2)))))) :=
  closeUniv 3 (.impI (.andI (sqrt_upper Prf.hyp0 _) (sqrt_lower Prf.hyp0 _)))

end LeanProofs.IPRA.Foundations.SquareRootNames
