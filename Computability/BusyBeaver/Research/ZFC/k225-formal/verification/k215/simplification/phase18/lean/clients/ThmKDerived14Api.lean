import BusyBeaver.ZFC.KThmK

namespace ThmKDerived14Api
open SetTheory.BusyBeaver.ZFC
open Tarski (NF Thm Rows rn)
open Tarski.NF

variable {Ax : NF → Prop}

example : Rows (Thm Ax) := inferInstance
example : Rows (KThmK.ThmK Ax) := inferInstance

/-- The concrete restricted calculus still exposes only its exact helper binder. -/
example (a b : Nat) :
    KThmK.ThmK Ax (imp (NF.eq a b) (all (Code254.wel a b) (NF.eq a b))) :=
  KThmK.ThmK.helper a b

/-- The ordinary calculus retains its separate, unrestricted Leibniz interface. -/
example (hC : Kalmar.Classical NF.imp NF.bot (Thm Ax)) (x y : Nat) (f : NF)
    (hx : ¬ Tarski.Bound x f) (hy : ¬ Tarski.Bound y f) :
    Thm Ax (imp (NF.eq x y) (imp f (rn x y f))) ∧
    Thm Ax (imp (NF.eq x y) (imp (rn x y f) f)) := Tarski.leibniz hC x y f hx hy

example (hC : Kalmar.Classical NF.imp NF.bot (Thm Ax)) (i : Nat) (a b : NF) :
    Thm Ax (imp (all i (imp a b)) (imp (ex i a) (ex i b))) :=
  Tarski.all_imp_ex hC i a b

theorem reflexivity (x : Nat) : KThmK.ThmK Ax (NF.eq x x) := KThmK.eq_refl x

theorem leibniz (x y : Nat) (f : NF) (hq : KThmK.QF f) (hf : KThmK.EqFree f) :
    KThmK.ThmK Ax (imp (NF.eq x y) (imp f (rn x y f))) ∧
    KThmK.ThmK Ax (imp (NF.eq x y) (imp (rn x y f) f)) := KThmK.leibniz x y f hq hf

theorem specialization {x y : Nat} (hxy : y ≠ x) {f : NF}
    (hq : KThmK.QF f) (hf : KThmK.EqFree f) :
    KThmK.ThmK Ax (imp (all x f) (rn x y f)) := KThmK.spec hxy hq hf

theorem alpha {x y : Nat} (hxy : y ≠ x) {f : NF} (hq : KThmK.QF f)
    (hf : KThmK.EqFree f) (hy : ¬ Occurs y f) :
    KThmK.ThmK Ax (imp (all x f) (all y (rn x y f))) ∧
    KThmK.ThmK Ax (imp (all y (rn x y f)) (all x f)) :=
  ⟨KThmK.alpha_fwd hxy hq hf hy, KThmK.alpha_bwd hxy hq hf hy⟩

#print axioms reflexivity
#print axioms leibniz
#print axioms specialization
#print axioms alpha
end ThmKDerived14Api
