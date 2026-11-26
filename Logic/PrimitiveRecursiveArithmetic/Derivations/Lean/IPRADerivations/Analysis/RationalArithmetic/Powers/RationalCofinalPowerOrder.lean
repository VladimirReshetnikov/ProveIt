import IPRADerivations.Analysis.RationalArithmetic.Powers.RationalIntervalPowerComparison
import IPRADerivations.Analysis.Optimization.RationalConvexIntervalBounds

/-!
# Order of power names at a common finer precision offset

A cofinal midpoint comparison gives an exact lower-to-upper comparison
at every later original precision. If the shifted power and product
intervals have the prescribed width, their two midpoint errors fit
within the source tolerance at the new offset. This lets independently
scheduled source comparisons use one common offset in the local
modulus proof.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalCofinalPowerOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero)
open RationalNestedIntervals (regular positiveWitness)
open RationalIntervalPowerComparison (stage powerEndpoint productEndpoint powerCenter productCenter
  centerOrder multiplicative_of_center_order)
open RationalCubeGrid (scale)
open RationalValueBounds (upper)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

def widthsAt (L U : PR 3) (X Y Z a b o k x : PTm n) : Fm PTm n :=
  upper (powerEndpoint U Z (a+b) o k x) (powerEndpoint L Z (a+b) o k x) one (scale k) ⋏
    upper (productEndpoint U X Y a b o k x) (productEndpoint L X Y a b o k x) one (scale k)

def widths (L U : PR 3) (X Y Z a b o x : PTm n) : Fm PTm n := .all
  (widthsAt L U (Syn.shift X) (Syn.shift Y) (Syn.shift Z) (Syn.shift a) (Syn.shift b) (Syn.shift o) (var 0) (Syn.shift x))

@[simp] theorem subst_widthsAt {m : ℕ} (σ : Fin n → PTm m) (L U : PR 3) (X Y Z a b o k x : PTm n) :
    (widthsAt L U X Y Z a b o k x).subst σ =
      widthsAt L U (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ Z) (Syn.subst σ a) (Syn.subst σ b)
        (Syn.subst σ o) (Syn.subst σ k) (Syn.subst σ x) := by
  simp [widthsAt,scale]
@[simp] theorem subst_widths {m : ℕ} (σ : Fin n → PTm m) (L U : PR 3) (X Y Z a b o x : PTm n) :
    (widths L U X Y Z a b o x).subst σ =
      widths L U (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ Z) (Syn.subst σ a) (Syn.subst σ b)
        (Syn.subst σ o) (Syn.subst σ x) := by
  simp [widths,Syn.subst_shift,Syn.shift_subst]

theorem widths_at (L U : PR 3) (X Y Z a b o k x : PTm n) (h : Γ ⊢[PRAAx] widths L U X Y Z a b o x) :
    Γ ⊢[PRAAx] widthsAt L U X Y Z a b o k x := by
  simpa only [widths,subst_widthsAt,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE k

theorem transport_at (L U : PR 3) (X Y Z a b o f k sx sy sz x : PTm n)
    (hx : Γ ⊢[PRAAx] regular L U X x) (hy : Γ ⊢[PRAAx] regular L U Y x) (hz : Γ ⊢[PRAAx] regular L U Z x)
    (px : Γ ⊢[PRAAx] positiveWitness L X o sx x) (py : Γ ⊢[PRAAx] positiveWitness L Y o sy x)
    (pz : Γ ⊢[PRAAx] positiveWitness L Z o sz x)
    (hf : Γ ⊢[PRAAx] le o f) (h : Γ ⊢[PRAAx] centerOrder L U X Y Z a b o x)
    (hw : Γ ⊢[PRAAx] widthsAt L U X Y Z a b f k x) :
    Γ ⊢[PRAAx] upper (powerCenter L U Z (a+b) f k x) (productCenter L U X Y a b f k x) one (scale k) := by
  let s := scale k
  let A := powerCenter L U Z (a+b) f k x
  let B := productCenter L U X Y a b f k x
  let l := powerEndpoint L Z (a+b) f k x
  let u := productEndpoint U X Y a b f k x
  have fine := le_trans hf (RationalIntervalPowerComparison.stage_after_offset f k)
  have rel := multiplicative_of_center_order L U X Y Z a b o (stage f k) sx sy sz x
    hx hy hz px py pz fine h
  have first : Γ ⊢[PRAAx] upper A l one (two*s) :=
    RationalCubeInfimumName.midpoint_half_left _ _ _ _ hw.andE₁
  have last : Γ ⊢[PRAAx] upper u B one (two*s) :=
    RationalCubeInfimumName.midpoint_half_right _ _ _ _ hw.andE₂
  have first' : Γ ⊢[PRAAx] upper A u one (two*s) :=
    RationalValueBounds.upper_order_right _ _ _ _ _ first rel
  have both := RationalValueBounds.upper_triangle A u B one (two*s) one (two*s) first' last
  have positive := RationalConvexIntervalBounds.half_width_positive (Γ := Γ) k
  exact RationalValueBounds.upper_mono _ _ _ _ _ _ (RationalAlgebra.positive_product positive positive) both
    (le_of_eq_add (d := zero) (by dsimp only [s,scale]; ipra_ring))

def witnessInput (L U : PR 3) (X Y Z o sx sy sz x : PTm n) : Fm PTm n :=
  regular L U X x ⋏ (regular L U Y x ⋏ (regular L U Z x ⋏
    (positiveWitness L X o sx x ⋏ (positiveWitness L Y o sy x ⋏ positiveWitness L Z o sz x))))

@[simp] theorem subst_witnessInput {m : ℕ} (σ : Fin n → PTm m) (L U : PR 3) (X Y Z o sx sy sz x : PTm n) :
    (witnessInput L U X Y Z o sx sy sz x).subst σ =
      witnessInput L U (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ Z) (Syn.subst σ o)
        (Syn.subst σ sx) (Syn.subst σ sy) (Syn.subst σ sz) (Syn.subst σ x) := by
  simp [witnessInput,RationalNestedIntervals.positiveWitness,RationalConvexFiniteModulus.eps]

theorem transport (L U : PR 3) (X Y Z a b o f sx sy sz x : PTm n)
    (hi : Γ ⊢[PRAAx] witnessInput L U X Y Z o sx sy sz x)
    (hf : Γ ⊢[PRAAx] le o f) (h : Γ ⊢[PRAAx] centerOrder L U X Y Z a b o x)
    (hw : Γ ⊢[PRAAx] widths L U X Y Z a b f x) :
    Γ ⊢[PRAAx] centerOrder L U X Y Z a b f x := by
  let X' := Syn.shift X
  let Y' := Syn.shift Y
  let Z' := Syn.shift Z
  let a' := Syn.shift a
  let b' := Syn.shift b
  let o' := Syn.shift o
  let f' := Syn.shift f
  let x' := Syn.shift x
  have hi' : Γ.map Fm.shift ⊢[PRAAx] witnessInput L U X' Y' Z' o' (Syn.shift sx) (Syn.shift sy) (Syn.shift sz) x' := by
    simpa only [X',Y',Z',o',x',Syn.shift,Fm.shift,subst_witnessInput] using hi.shift
  have hf' : Γ.map Fm.shift ⊢[PRAAx] le o' f' := by
    simpa only [o',f',Syn.shift,Fm.shift,subst_le] using hf.shift
  have h' : Γ.map Fm.shift ⊢[PRAAx] centerOrder L U X' Y' Z' a' b' o' x' := by
    simpa only [X',Y',Z',a',b',o',x',Syn.shift,Fm.shift,RationalIntervalPowerComparison.subst_centerOrder] using h.shift
  have hw' : Γ.map Fm.shift ⊢[PRAAx] widths L U X' Y' Z' a' b' f' x' := by
    simpa only [X',Y',Z',a',b',f',x',Syn.shift,Fm.shift,subst_widths] using hw.shift
  exact .allI (transport_at L U X' Y' Z' a' b' o' f' (var 0) (Syn.shift sx) (Syn.shift sy) (Syn.shift sz) x'
    hi'.andE₁ hi'.andE₂.andE₁ hi'.andE₂.andE₂.andE₁ hi'.andE₂.andE₂.andE₂.andE₁
    hi'.andE₂.andE₂.andE₂.andE₂.andE₁ hi'.andE₂.andE₂.andE₂.andE₂.andE₂ hf' h'
    (widths_at L U X' Y' Z' a' b' f' (var 0) x' hw'))

theorem actual_cofinal_power_order_transport_closed (L U : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    ((witnessInput L U (var 0) (var 1) (var 2) (var 5) (var 7) (var 8) (var 9) (var 10) ⋏ le (var 5) (var 6)) ⟶
      centerOrder L U (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 10) ⟶
      widths L U (var 0) (var 1) (var 2) (var 3) (var 4) (var 6) (var 10) ⟶
      centerOrder L U (var 0) (var 1) (var 2) (var 3) (var 4) (var 6) (var 10)) :=
  closeUniv 11 (.impI (.impI (.impI (transport L U _ _ _ _ _ _ _ _ _ _ _
    hyp2.andE₁ hyp2.andE₂ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.RationalCofinalPowerOrder
