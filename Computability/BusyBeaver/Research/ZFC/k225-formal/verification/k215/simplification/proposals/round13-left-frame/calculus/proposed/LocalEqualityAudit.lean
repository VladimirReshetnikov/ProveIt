import BusyBeaver.ZFC.KThmK

/-! UNCOMPILED compatibility obligations for the local-equality-capability proposal. -/
namespace SetTheory.BusyBeaver.ZFC.LocalEqualityAudit
open Tarski NF Kalmar
variable {Ax : NF → Prop}

example (hC : Classical NF.imp NF.bot (Thm Ax)) (x : Nat) : Thm Ax (NF.eq x x) :=
  Tarski.eq_refl hC x

example (hC : Classical NF.imp NF.bot (Thm Ax)) (x y : Nat) (f : NF)
    (hx : ¬ Bound x f) (hy : ¬ Bound y f) :
    Thm Ax (imp (NF.eq x y) (imp f (rn x y f))) ∧
    Thm Ax (imp (NF.eq x y) (imp (rn x y f) f)) := Tarski.leibniz hC x y f hx hy

example (hC : Classical NF.imp NF.bot (Thm Ax)) {x y : Nat} (hxy : y ≠ x)
    {f : NF} (hx : ¬ Bound x f) (hy : ¬ Bound y f) :
    Thm Ax (imp (all x f) (rn x y f)) := Tarski.spec hC hxy hx hy

example (x : Nat) : KThmK.ThmK Ax (NF.eq x x) := KThmK.eq_refl x

example (x y : Nat) (f : NF) (hq : KThmK.QF f) (hf : KThmK.EqFree f) :
    KThmK.ThmK Ax (imp (NF.eq x y) (imp f (rn x y f))) ∧
    KThmK.ThmK Ax (imp (NF.eq x y) (imp (rn x y f) f)) := KThmK.leibniz x y f hq hf

example {x y : Nat} (hxy : y ≠ x) {f : NF} (hq : KThmK.QF f) (hf : KThmK.EqFree f) :
    KThmK.ThmK Ax (imp (all x f) (rn x y f)) := KThmK.spec hxy hq hf

-- Extra consequence of the core, NOT a change to the compatibility theorem:
-- QF rewriting can include equality atoms; specialization still needs its old EqFree premise.
theorem k_qf_leibniz (x y : Nat) (f : NF) (hq : KThmK.QF f) :
    KThmK.ThmK Ax (imp (NF.eq x y) (imp f (rn x y f))) ∧
    KThmK.ThmK Ax (imp (NF.eq x y) (imp (rn x y f) f)) :=
  leibniz_core KThmK.classical KThmK.eq_symm KThmK.eq_trans x y f
    (KThmK.qf_bound hq) (KThmK.qf_bound hq)
    (fun _ hi => (KThmK.qf_bound hq hi).elim)

#print axioms Tarski.eq_refl_of_vac
#print axioms Tarski.leibniz_core
#print axioms Tarski.specialize_core
#print axioms Tarski.spec
#print axioms KThmK.spec
#print axioms k_qf_leibniz
end SetTheory.BusyBeaver.ZFC.LocalEqualityAudit
