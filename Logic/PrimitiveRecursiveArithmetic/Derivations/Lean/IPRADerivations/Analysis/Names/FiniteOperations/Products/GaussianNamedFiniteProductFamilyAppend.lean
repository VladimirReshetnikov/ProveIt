import IPRADerivations.Analysis.Names.FiniteOperations.Products.GaussianNamedFiniteProductAppend
import IPRADerivations.Analysis.Names.FiniteOperations.Products.GaussianNamedFiniteProductFamily

/-!
# Removing a final row from an original regular family

This gives a direct named multiplication for singleton and other
short folds, and works at arbitrary internal family length.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedFiniteProductFamilyAppend

open_ipra
open GaussianNamedFiniteProductAppend (lastRow append_cross singleton_cross)
open GaussianNamedFiniteProductFamily (rowF row_at productData regularRows regular_at radius
  family_bounds family_regular)
open GaussianNamedFiniteProductName (nameF)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem regular_prefix (f : PR 2) (t : PTm 2) (N M x : PTm n) (hm : Γ ⊢[PRAAx] le N M)
    (h : Γ ⊢[PRAAx] regularRows f t M x) : Γ ⊢[PRAAx] regularRows f t N x := by
  refine .allI (.impI ?_)
  let sh (v : PTm n) := Syn.shift v
  let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] regularRows f t (sh M) (sh x) := by
    simpa [Fm.shift, Syn.shift, sh, Δ] using h.shift.wk
  have bound : Δ ⊢[PRAAx] le (sh N) (sh M) := by simpa [Fm.shift, Syn.shift, sh, Δ] using hm.shift.wk
  exact regular_at f t (sh M) (sh x) (var 0) hs (le_trans Prf.hyp0 bound)

theorem family_append_cross (f : PR 2) (t : PTm 2) (N x : PTm n)
    (h : Γ ⊢[PRAAx] regularRows f t (succ N) x) :
    Γ ⊢[PRAAx] crossEquivalent (nameF (rowF f t)) (multiplyF (nameF (rowF f t)) f)
      (productData f t (succ N) x) (multiplyData (nameF (rowF f t)) f (productData f t N x) (inst2 t N x)) := by
  have hr := regular_prefix f t N (succ N) x (le_succ_self N) h
  have he : Γ ⊢[PRAAx] lastRow (rowF f t) f N x (inst2 t N x) := by
    refine .allI ?_
    simpa [lastRow, Syn.shift] using row_at (Γ := Γ.map Fm.shift) f t (var 0) (Syn.shift N) (Syn.shift x)
  exact append_cross _ _ _ _ _ _ _ _ _ (family_bounds f t N x hr) (family_regular f t N x hr)
    (family_bounds f t (succ N) x h) (family_regular f t (succ N) x h) (regular_at f t _ _ _ h (le_refl _)) he

theorem family_singleton_cross (f : PR 2) (t : PTm 2) (x : PTm n)
    (h : Γ ⊢[PRAAx] regularRows f t one x) :
    Γ ⊢[PRAAx] crossEquivalent (nameF (rowF f t)) f (productData f t one x) (inst2 t zero x) := by
  have he : Γ ⊢[PRAAx] lastRow (rowF f t) f zero x (inst2 t zero x) := by
    refine .allI ?_
    simpa [lastRow,Syn.shift] using row_at (Γ := Γ.map Fm.shift) f t (var 0) zero (Syn.shift x)
  exact singleton_cross _ _ (radius f t one x) one x (inst2 t zero x)
    (family_bounds f t one x h) (family_regular f t one x h) (regular_at f t one x zero h (le_refl one)) he

theorem actual_family_append_closed (f : PR 2) (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (regularRows f t (succ (var 0)) (var 1) ⟶
      crossEquivalent (nameF (rowF f t)) (multiplyF (nameF (rowF f t)) f)
        (productData f t (succ (var 0)) (var 1))
        (multiplyData (nameF (rowF f t)) f (productData f t (var 0) (var 1)) (inst2 t (var 0) (var 1)))) :=
  closeUniv 2 (.impI (family_append_cross f t _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedFiniteProductFamilyAppend
