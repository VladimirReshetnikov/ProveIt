import ZFCinPA.NativePeel

set_option autoImplicit false
noncomputable section

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.InternalInterpretation
open LeanProofs.BoundedPAConsistency.InternalRelativization
open LeanProofs.ZFCinPA.NativePeel

#print axioms LeanProofs.ZFCinPA.NativePeel.derivable_mp
#print axioms LeanProofs.ZFCinPA.NativePeel.domSet_succ_subset
#print axioms LeanProofs.ZFCinPA.NativePeel.shift_qqAlls
#print axioms LeanProofs.ZFCinPA.NativePeel.free_subst_qVec_fvarVec
#print axioms LeanProofs.ZFCinPA.NativePeel.peel_step
#print axioms LeanProofs.ZFCinPA.NativePeel.peel

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {U : SetTheory} [U.Δ₁]

example {A B s : V} (hB : IsFormula ℒₛₑₜ B)
    (hC : Provable U (Bootstrapping.imp ℒₛₑₜ A B)) (hA : Derivable U (insert A s)) :
    Derivable U (insert B s) := derivable_mp hB hC hA

example {d : V} (hd : IsSemiformula ℒₛₑₜ 1 d) (hds : shift ℒₛₑₜ d = d) (k : V) :
    domSet ℒₛₑₜ d (k + 1) ⊆ insert (domF ℒₛₑₜ d 0) (setShift ℒₛₑₜ (domSet ℒₛₑₜ d k)) :=
  domSet_succ_subset hd hds k

example {body : V} (hb : IsUFormula ℒₛₑₜ body) (count : V) :
    shift ℒₛₑₜ (qqAlls body count) = qqAlls (shift ℒₛₑₜ body) count := shift_qqAlls hb count

example {k B : V} (hB : IsSemiformula ℒₛₑₜ (k + 1) B) (hs : shift ℒₛₑₜ B = B) :
    free ℒₛₑₜ (subst ℒₛₑₜ (qVec ℒₛₑₜ (fvarVec k)) B) =
      subst ℒₛₑₜ (fvarVec (k + 1)) B := free_subst_qVec_fvarVec hB hs

example {P j x : V} (hP : Good P) (hx : IsSemiformula ℒₛₑₜ 1 x)
    (h : Derivable U (insert (interp P (free ℒₛₑₜ x)) (domSet ℒₛₑₜ (dom P) (j + 1)))) :
    Derivable U (insert (interp P (^∀ x)) (domSet ℒₛₑₜ (dom P) j)) := peel_step hP hx h

example {P m b e : V} (hP : Good P) (hb : IsSemiformula ℒₛₑₜ m b)
    (hs : shift ℒₛₑₜ b = b)
    (base : Derivable U (insert (interp P (subst ℒₛₑₜ (fvarVec m) b))
      (domSet ℒₛₑₜ (dom P) (m + e)))) :
    Derivable U (insert (interp P (qqAlls b m)) (domSet ℒₛₑₜ (dom P) e)) := peel hP hb hs base

-- Closing every opened binder retains the literal empty-domain side set.
example {P m b : V} (hP : Good P) (hb : IsSemiformula ℒₛₑₜ m b)
    (hs : shift ℒₛₑₜ b = b)
    (base : Derivable U (insert (interp P (subst ℒₛₑₜ (fvarVec m) b))
      (domSet ℒₛₑₜ (dom P) (m + 0)))) :
    Derivable U (insert (interp P (qqAlls b m)) (domSet ℒₛₑₜ (dom P) 0)) :=
  peel (e := 0) hP hb hs base

example {P x : V} (hP : Good P) (hx : IsSemiformula ℒₛₑₜ 1 x)
    (h : Derivable U (insert (interp P (free ℒₛₑₜ x)) (domSet ℒₛₑₜ (dom P) (0 + 1)))) :
    Derivable U (insert (interp P (^∀ x)) (domSet ℒₛₑₜ (dom P) 0)) :=
  peel_step (j := 0) hP hx h
