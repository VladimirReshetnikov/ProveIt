import BusyBeaver.ZFC.KQ1Model
import BusyBeaver.ZFC.QuotientModel

open SetTheory SetTheory.BusyBeaver.ZFC
open Form Profile ProfileComposition ProfileSyntax ProfileModel ProfileCollection

namespace QuotientSharing15Api
universe u
variable {V : Type u}

theorem shared_syntax (mem : V → V → Prop) (env : Nat → V) (phi : Form) (i j : Nat) :
    KQ1Model.memberForm i j = QuotientModel.memberForm i j ∧
    KQ1Model.translate phi = QuotientModel.translate phi ∧
    (KQ1Model.RelSat mem env phi ↔ QuotientModel.RelSat mem env phi) :=
  ⟨rfl, rfl, Iff.rfl⟩

theorem strong_congruence (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem)
    (phi : Form) (env env' : Nat → V) (he : ∀ i, Eqv mem (env i) (env' i)) :
    QuotientModel.RelSat mem env phi ↔ QuotientModel.RelSat mem env' phi :=
  QuotientModel.relSat_congr mem witness h phi env env' he

theorem weak_congruence (mem : V → V → Prop) (witness : V) (h : KQHyp.QHyp mem)
    (phi : Form) (env env' : Nat → V) (he : ∀ i, Eqv mem (env i) (env' i)) :
    KQ1Model.RelSat mem env phi ↔ KQ1Model.RelSat mem env' phi :=
  KQ1Model.relSat_congr mem witness h phi env env' he

theorem strong_satisfaction (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem)
    (phi : Form) (env : Nat → V) :
    Sat (QuotientModel.quotientMember mem witness h)
      (fun i => QuotientModel.mk mem witness h (env i)) phi ↔
      QuotientModel.RelSat mem env phi :=
  QuotientModel.sat_quotient mem witness h phi env

theorem weak_satisfaction (mem : V → V → Prop) (witness : V) (h : KQHyp.QHyp mem)
    (phi : Form) (env : Nat → V) :
    Sat (KQ1Model.quotientMember mem witness h)
      (fun i => KQ1Model.mk mem witness h (env i)) phi ↔ KQ1Model.RelSat mem env phi :=
  KQ1Model.sat_quotient mem witness h phi env

theorem strong_extensionality (mem : V → V → Prop) (witness : V)
    (h : ModelsCPGIC mem) (x y : QuotientModel.Domain mem witness h)
    (hm : ∀ z, QuotientModel.quotientMember mem witness h z x ↔
      QuotientModel.quotientMember mem witness h z y) : x = y :=
  QuotientModel.quotient_extensional mem witness h x y hm

theorem weak_extensionality (mem : V → V → Prop) (witness : V)
    (h : KQHyp.QHyp mem) (x y : KQ1Model.Domain mem witness h)
    (hm : ∀ z, KQ1Model.quotientMember mem witness h z x ↔
      KQ1Model.quotientMember mem witness h z y) : x = y :=
  KQ1Model.quotient_extensional mem witness h x y hm

#print axioms shared_syntax
#print axioms strong_congruence
#print axioms weak_congruence
#print axioms strong_satisfaction
#print axioms weak_satisfaction
#print axioms strong_extensionality
#print axioms weak_extensionality
end QuotientSharing15Api
