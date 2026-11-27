import IPRADerivations.Foundations.EliminationDegree
import IPRADerivations.Foundations.BoundedFormulas

/-!
# Counting under a fixed-point-free involution

A reusable piece of the embedding framework for parity arguments (the door count of the
cubical Sperner lemma `thm:sperner` of `topology/dimension_invariance_ipra` in every dimension,
sign-change counts, pairings of facets): if an involution `ι` of `{i < N}` has no fixed point
and preserves a summand `b`, then `∑_{i<N} b(i)` is even.

With `rangeAll`, `invAll`, `retAll` of `Core/Permutation` for `σ = τ = ι` (so `ι` maps every
index below `N`, and `ι(ι(i)) = i` there), `fixFree ι N x` (`ι(i) ≠ i` for `i < N`) and
`invariant b ι N x` (`b(ι(i)) = b(i)` for `i < N`):

* `sg_split`: for `a ≠ c`, `[a < c] + [c < a] = 1`, with `[a < c] = sg(c ∸ a)`;
* `lower_half`, `upper_half`: the summands `b(i) [i < ι(i)]` (`loB`) and `b(i) [ι(i) < i]`
  (`hiB`) add up to `b(i)` below `N`, and `hiB(i) = loB(ι(i))`;
* `involution_even`: `∑_{i<N} b(i) = 2 ∑_{i<N} b(i) [i < ι(i)]`, through the permutation sum
  `Foundations/EliminationDegree.sum_perm` (`∑ F(ι(i)) = ∑ F(i)`).

No case distinction on the summand is needed: `b` is an arbitrary binary symbol, so the
theorem counts with multiplicities as well as counting the indices with a property.
-/

namespace LeanProofs.IPRA.Foundations.InvolutionParity

open_ipra exports
open LeanProofs.IPRA.Permutation (FS rangeAll invAll retAll inst2_FS)
open LeanProofs.IPRA.Foundations.EliminationDegree (sum_perm)
open LeanProofs.IPRA.Signum (sg)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The order indicator -/

/-- `a < c` gives `[a < c] = 1` and `[c < a] = 0`. -/
theorem sg_lt {a c : PTm n} (h : Γ ⊢[PRAAx] lt a c) :
    Γ ⊢[PRAAx] sg (monus c a) + sg (monus a c) ≐ one := by
  have z : Γ ⊢[PRAAx] sg (monus a c) ≐ zero := sg_of_zero (le_of_lt h)
  have e₂ : Γ ⊢[PRAAx] c ≐ succ (monus c (succ a)) + a := by
    ipra_lc natEq (eq_add_of_le h)
  have p : Γ ⊢[PRAAx] sg (monus c a) ≐ one :=
    sg_of_pos ((congrMonus e₂ (.eqRefl a)).eqTrans (add_monus _ _))
  exact (congrAdd p z).eqTrans (add_zero _)

/-- For `a ≠ c`, `[a < c] + [c < a] = 1`, with `[a < c] = sg(c ∸ a)`. -/
theorem sg_split {a c : PTm n} (h : Γ ⊢[PRAAx] neg (a ≐ c)) :
    Γ ⊢[PRAAx] sg (monus c a) + sg (monus a c) ≐ one :=
  .orE (Order.lt_or_gt_of_ne h) (sg_lt Prf.hyp0)
    ((add_comm _ _).eqTrans (sg_lt Prf.hyp0))

/-! ## The two halves -/

section Halves

variable (b ι : PTm 2)

/-- `b(i) [i < ι(i)]`. -/
def loB : PTm 2 := b * sg (monus ι (var 0))
/-- `b(i) [ι(i) < i]`. -/
def hiB : PTm 2 := b * sg (monus (var 0) ι)

theorem inst2_loB (i x : PTm n) :
    inst2 (loB b ι) i x = inst2 b i x * sg (monus (inst2 ι i x) i) := by simp [inst2, loB]

theorem inst2_hiB (i x : PTm n) :
    inst2 (hiB b ι) i x = inst2 b i x * sg (monus i (inst2 ι i x)) := by simp [inst2, hiB]

/-- `ι(i) ≠ i` for `i < N`. -/
abbrev fixFree (N x : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift N) ⟶ neg (inst2 ι (var 0) (Syn.shift x) ≐ var 0))

/-- `b(ι(i)) = b(i)` for `i < N`. -/
abbrev invariant (N x : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift N) ⟶
    (inst2 b (inst2 ι (var 0) (Syn.shift x)) (Syn.shift x) ≐ inst2 b (var 0) (Syn.shift x)))

/-- Below `N` the two halves add up to the summand. -/
theorem lower_half {i x : PTm n} (hne : Γ ⊢[PRAAx] neg (inst2 ι i x ≐ i)) :
    Γ ⊢[PRAAx] inst2 b i x ≐ inst2 (addBody (loB b ι) (hiB b ι)) i x := by
  rw [inst2_addBody, inst2_loB, inst2_hiB]
  ipra_lc (-(𝔞 (inst2 b i x))) * natEq (sg_split (Order.ne_symm hne))

/-- `hiB(i) = loB(ι(i))` below `N`. -/
theorem upper_half {i x : PTm n} (hb : Γ ⊢[PRAAx] inst2 b (inst2 ι i x) x ≐ inst2 b i x)
    (hii : Γ ⊢[PRAAx] inst2 ι (inst2 ι i x) x ≐ i) :
    Γ ⊢[PRAAx] inst2 (hiB b ι) i x ≐ inst2 (FS (loB b ι) ι) i x := by
  rw [inst2_FS, inst2_loB, inst2_hiB]
  exact (congrMul hb
    (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (congrMonus hii (.eqRefl _))))).eqSymm

end Halves

/-! ## The parity theorem -/

/-- `∑_{i<N} b(i) = 2 ∑_{i<N} b(i) [i < ι(i)]` for a fixed-point-free involution `ι` of
`{i < N}` that preserves `b`; in particular the sum is even. -/
theorem involution_even (b ι : PTm 2) {N x : PTm n} (hr : Γ ⊢[PRAAx] rangeAll ι N x)
    (hinv : Γ ⊢[PRAAx] invAll ι ι N x) (hret : Γ ⊢[PRAAx] retAll ι ι N x)
    (hfix : Γ ⊢[PRAAx] fixFree ι N x) (hb : Γ ⊢[PRAAx] invariant b ι N x) :
    Γ ⊢[PRAAx] ap2 (sumF b) N x ≐ two * ap2 (sumF (loB b ι)) N x := by
  have split : Γ ⊢[PRAAx] ap2 (sumF b) N x ≐ ap2 (sumF (addBody (loB b ι) (hiB b ι))) N x := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    exact lower_half b ι (.impE hfix.allOpen.wk Prf.hyp0)
  have swap : Γ ⊢[PRAAx] ap2 (sumF (hiB b ι)) N x ≐ ap2 (sumF (FS (loB b ι) ι)) N x := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    have hii : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
        inst2 ι (inst2 ι (var 0) (Syn.shift x)) (Syn.shift x) ≐ var 0 := by
      have r := hret.allOpen
      exact .impE r.wk Prf.hyp0
    exact upper_half b ι (.impE hb.allOpen.wk Prf.hyp0) hii
  have perm := sum_perm (F := loB b ι) hr hinv hret
  ipra_lc natEq split + natEq (sum_add (loB b ι) (hiB b ι) N x) + natEq (swap.eqTrans perm)

end LeanProofs.IPRA.Foundations.InvolutionParity
