import IPRADerivations.Foundations.RiseAlternative
import IPRADerivations.Foundations.WindowStability
import IPRADerivations.Foundations.CoherentTower

/-!
# The rational finite window: a nonrise of the floors

Packet: `foundations/ipra_framework`, `paper/sections/05_metastability.tex`, Theorem `thm:rational-window`
("Rational finite-window stability"): "The integers `r_i = ⌊s_{n_i}/ε⌋` form a nondecreasing sequence
bounded by `B`. Lemma `lem:rise` gives an index `i ≤ B` where two adjacent values coincide."

For the values `σ(i, x)` of the sequence at the candidate starts (numerators over a common denominator)
and `ε = e′ + 1`:

* `rB σ`, `r_at`: the floors `r_i = ⌊σ(i, x)/ε⌋` as a body with the parameter `⟨e′, x⟩`;
* `floor_nonrise`: if `⌊σ(B + 1, x)/ε⌋ ≤ B` (the floors are bounded by `B`), then
  `∃ i < B + 1. ⌊σ(i + 1, x)/ε⌋ ≤ ⌊σ(i, x)/ε⌋`.

At such an index, `window_of_nonrise` of `Foundations/WindowStability` gives `s_v < s_u + ε` for all values
between the two endpoint values, which is the conclusion of the theorem for a monotone sequence. The index
is the least one (bounded search); the candidate starts `n_i` are data of the application.
-/

namespace LeanProofs.IPRA.Foundations.RationalWindow

open_ipra exports
open LeanProofs.IPRA.Foundations.RiseAlternative (riseB nxB inst2_riseB inst2_nxB nonrise_of_bound)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The floors `⌊σ(i, snd y)/(fst y + 1)⌋`; variables `0 = i`, `1 = y = ⟨e′, x⟩`. -/
def rB (σ : PTm 2) : PTm 2 := quo (rdB σ) (succ (fstT (var 1)))

theorem inst2_rB (σ : PTm 2) (i y : PTm n) :
    inst2 (rB σ) i y = quo (inst2 (rdB σ) i y) (succ (fstT y)) := by
  simp [inst2, rB]

theorem r_at (σ : PTm 2) (i e' x : PTm n) :
    Γ ⊢[PRAAx] inst2 (rB σ) i (pairT e' x) ≐ quo (inst2 σ i x) (succ e') := by
  rw [inst2_rB, inst2_rdB]
  exact congrAp2 quoF (congrInst2 σ (.eqRefl i) (snd_pair e' x)) (congrSucc (fst_pair e' x))

/-- `thm:rational-window`: bounded floors do not rise at some index `i ≤ B`. -/
theorem floor_nonrise {σ : PTm 2} {B e' x : PTm n}
    (hB : Γ ⊢[PRAAx] le (quo (inst2 σ (succ B) x) (succ e')) B) :
    Γ ⊢[PRAAx] Fm.ex (lt (var 0) (Syn.shift (succ B)) ⋏
      le (quo (inst2 σ (succ (var 0)) (Syn.shift x)) (succ (Syn.shift e')))
        (quo (inst2 σ (var 0) (Syn.shift x)) (succ (Syn.shift e')))) := by
  have h := nonrise_of_bound (rB σ) (x := pairT e' x)
    (le_congr (r_at σ (succ B) e' x).eqSymm (.eqRefl B) hB)
  refine ex_mono h ?_
  have z : ((lt (var 0) (Syn.shift (succ B)) ⋏
        (inst2 (riseB (rB σ)) (var 0) (Syn.shift (pairT e' x)) ≐ zero)) :: Γ.map Fm.shift) ⊢[PRAAx]
      (lt (var 0) (Syn.shift (succ B)) ⋏
        (inst2 (riseB (rB σ)) (var 0) (Syn.shift (pairT e' x)) ≐ zero)) := Prf.hyp0
  have e : inst2 (riseB (rB σ)) (var 0) (Syn.shift (pairT e' x)) =
      PTm.monus (inst2 (rB σ) (succ (var 0)) (pairT (Syn.shift e') (Syn.shift x)))
        (inst2 (rB σ) (var 0) (pairT (Syn.shift e') (Syn.shift x))) := by
    rw [shift_pairT, inst2_riseB, inst2_nxB]
  have key : ∀ {Δ : List (Fm PTm (n + 1))} {T T' : PTm (n + 1)}, T = T' →
      (Δ ⊢[PRAAx] (T ≐ zero)) → (Δ ⊢[PRAAx] (T' ≐ zero)) := fun h q => h ▸ q
  have z₃ := key e (Prf.andE₂ z)
  exact .andI (Prf.andE₁ z)
    (le_congr (r_at σ (succ (var 0)) (Syn.shift e') (Syn.shift x))
      (r_at σ (var 0) (Syn.shift e') (Syn.shift x)) z₃)

end LeanProofs.IPRA.Foundations.RationalWindow
