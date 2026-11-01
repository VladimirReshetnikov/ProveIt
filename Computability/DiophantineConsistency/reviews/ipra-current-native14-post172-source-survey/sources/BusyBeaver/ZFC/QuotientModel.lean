import BusyBeaver.ZFC.KQ1Power

/-!
The actual quotient structure of an equality-free CP/GIC model.

An inhabited CP/GIC model supplies every field of `KQHyp.QHyp` (`ofCPGIC`): the GIC half, the
bisimilarity laws and profile pairs of the model, and interpreted union, power and
singleton-closed containers bounded by its raw CP container. The quotient is the `KQ1Model`
quotient of that structure. This module and `QuotientSeparation` … `QuotientCPGIC` state the
`KQ1*` results for CP/GIC models under their original names.
-/

namespace SetTheory.BusyBeaver.ZFC.QuotientModel

open KQHyp
open Form ProfileCollection ProfileComposition ProfileAxioms ProfileModel CompositionModel
open DeepPositiveClosure

universe u
variable {V : Type u}

theorem ofCPGIC (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem) : QHyp mem :=
  have hc := (sat_containerForm mem (fun _ => witness)).mp (h.1 _)
  have refl := eqv_refl_of_model mem witness h
  have symm : ∀ x y, Eqv mem x y → Eqv mem y x := fun _ _ => eqv_symm_of_model mem witness h
  have trans : ∀ x y z, Eqv mem x y → Eqv mem y z → Eqv mem x z :=
    fun _ _ _ => eqv_trans_of_model mem witness h
  ⟨h.2, refl, symm _ _, trans _ _ _, eqv_extensionality_of_model mem witness h,
    pairs_of_model mem witness h,
    fun a => union_of_instance mem a hc refl trans (union_instance mem h.2 a),
    fun a => power_of_instances mem a hc refl symm trans
      (eqv_extensionality_of_model mem witness h) (KQ1Power.trace_instance mem h.2 a)
      (PowerSyntax.power_instance mem h.2 a),
    fun root => singleton_closed_of_containers mem root hc (pairs_of_model mem witness h)
      refl symm trans⟩

theorem member_right_congr (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem)
    {x y y' : V} (hyy' : Eqv mem y y') : Member mem x y ↔ Member mem x y' :=
  KQ1Model.member_right_congr mem witness (ofCPGIC mem witness h) hyy'

abbrev memberForm := KQ1Model.memberForm

abbrev translate := KQ1Model.translate

abbrev RelSat (mem : V → V → Prop) (env : Nat → V) := KQ1Model.RelSat mem env

theorem sat_memberForm (mem : V → V → Prop) (env : Nat → V) (i j : Nat) :
    Sat mem env (memberForm i j) ↔ Member mem (env i) (env j) :=
  KQ1Model.sat_memberForm mem env i j

theorem sat_translate (mem : V → V → Prop) (phi : Form) (env : Nat → V) :
    Sat mem env (translate phi) ↔ RelSat mem env phi :=
  KQ1Model.sat_translate mem phi env

theorem equalityFree_translate (phi : Form) : EqualityFree (translate phi) :=
  KQ1Model.equalityFree_translate phi

abbrev Domain (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem) :=
  KQ1Model.Domain mem witness (ofCPGIC mem witness h)

abbrev mk (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem) (x : V) :
    Domain mem witness h :=
  KQ1Model.mk mem witness (ofCPGIC mem witness h) x

abbrev quotientMember (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem) :
    Domain mem witness h → Domain mem witness h → Prop :=
  KQ1Model.quotientMember mem witness (ofCPGIC mem witness h)

theorem mk_eq_iff (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem) (x y : V) :
    mk mem witness h x = mk mem witness h y ↔ Eqv mem x y :=
  KQ1Model.mk_eq_iff mem witness (ofCPGIC mem witness h) x y

theorem mk_scons (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem)
    (x : V) (env : Nat → V) :
    (fun i => mk mem witness h (scons x env i)) =
      scons (mk mem witness h x) (fun i => mk mem witness h (env i)) :=
  KQ1Model.mk_scons mem witness (ofCPGIC mem witness h) x env

theorem sat_quotient (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem)
    (phi : Form) (env : Nat → V) :
    Sat (quotientMember mem witness h) (fun i => mk mem witness h (env i)) phi ↔
      RelSat mem env phi :=
  KQ1Model.sat_quotient mem witness (ofCPGIC mem witness h) phi env

theorem relSat_congr (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem)
    (phi : Form) (env env' : Nat → V) (he : ∀ i, Eqv mem (env i) (env' i)) :
    RelSat mem env phi ↔ RelSat mem env' phi :=
  KQ1Model.relSat_congr mem witness (ofCPGIC mem witness h) phi env env' he

theorem quotient_extensional (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem)
    (x y : Domain mem witness h)
    (hMembers : ∀ z, quotientMember mem witness h z x ↔ quotientMember mem witness h z y) :
    x = y :=
  KQ1Model.quotient_extensional mem witness (ofCPGIC mem witness h) x y hMembers

#print axioms sat_quotient
#print axioms quotient_extensional
#print axioms equalityFree_translate

end SetTheory.BusyBeaver.ZFC.QuotientModel
