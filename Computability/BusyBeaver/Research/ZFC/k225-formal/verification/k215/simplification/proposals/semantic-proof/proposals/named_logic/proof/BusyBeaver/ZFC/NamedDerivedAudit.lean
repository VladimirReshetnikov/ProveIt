import BusyBeaver.ZFC.KThmK

namespace SetTheory.BusyBeaver.ZFC.NamedDerivedAudit
open Tarski Tarski.NF Kalmar
variable {Ax : NF → Prop}
section Standard
variable (hC : Classical NF.imp NF.bot (Thm Ax))
example {G : List NF} {a : NF} : Der NF.imp (Thm Ax) (a :: G) a := by
  first | exact Tarski.h0 | apply Tarski.h0 <;> assumption

example {G : List NF} {a b : NF} : Der NF.imp (Thm Ax) (b :: a :: G) a := by
  first | exact Tarski.h1 | apply Tarski.h1 <;> assumption

example {G : List NF} {a b c : NF} : Der NF.imp (Thm Ax) (c :: b :: a :: G) a := by
  first | exact Tarski.h2 | apply Tarski.h2 <;> assumption

example {a : NF} (d : Der NF.imp (Thm Ax) [] a) : Thm Ax a := by
  first | exact Tarski.thm_of_der0 hC | apply Tarski.thm_of_der0 hC <;> assumption

example {a b c : NF} (d : Der NF.imp (Thm Ax) [b, a] c) : Thm Ax (imp a (imp b c)) := by
  first | exact Tarski.ded2 hC | apply Tarski.ded2 hC <;> assumption

example {a c : NF} (d : Der NF.imp (Thm Ax) [a] c) : Thm Ax (imp a c) := by
  first | exact Tarski.ded1 hC | apply Tarski.ded1 hC <;> assumption

example {a b c d : NF} (dd : Der NF.imp (Thm Ax) [c, b, a] d) :
    Thm Ax (imp a (imp b (imp c d))) := by
  first | exact Tarski.ded3 hC | apply Tarski.ded3 hC <;> assumption

example {a b c : NF} (hab : Thm Ax (imp a b)) (hbc : Thm Ax (imp b c)) :
    Thm Ax (imp a c) := by
  first | exact Tarski.syl hC | apply Tarski.syl hC <;> assumption

example (a b : NF) : Thm Ax (imp (imp a b) (imp (neg b) (neg a))) := by
  first | exact Tarski.contra_thm hC | apply Tarski.contra_thm hC <;> assumption

example {a b : NF} (h : Thm Ax (imp a b)) : Thm Ax (imp (neg b) (neg a)) := by
  first | exact Tarski.contra hC | apply Tarski.contra hC <;> assumption

example (a : NF) : Thm Ax (imp (neg (neg a)) a) := by
  first | exact Tarski.dne hC | apply Tarski.dne hC <;> assumption

example (a : NF) : Thm Ax (imp a (neg (neg a))) := by
  first | exact Tarski.dni hC | apply Tarski.dni hC <;> assumption

example (a b c : NF) :
    Thm Ax (imp (imp (neg a) c) (imp (imp b c) (imp (imp a b) c))) := by
  first | exact Tarski.imp_cases hC | apply Tarski.imp_cases hC <;> assumption

example (i : Nat) {a b : NF} (h : Thm Ax (imp a b)) :
    Thm Ax (imp (all i a) (all i b)) := by
  first | exact Tarski.all_mono hC | apply Tarski.all_mono hC <;> assumption

example (i : Nat) {a b : NF} (h : Thm Ax (imp a b)) :
    Thm Ax (imp (ex i a) (ex i b)) := by
  first | exact Tarski.ex_mono hC | apply Tarski.ex_mono hC <;> assumption

example {i : Nat} {a : NF} (h : Thm Ax (imp a (all i a))) :
    Thm Ax (imp (ex i a) a) := by
  first | exact Tarski.ex_elim_of_vac hC | apply Tarski.ex_elim_of_vac hC <;> assumption

example {i : Nat} {a : NF} (h : Thm Ax (imp a (all i a))) :
    Thm Ax (imp (neg a) (all i (neg a))) := by
  first | exact Tarski.vac_neg hC | apply Tarski.vac_neg hC <;> assumption

example (i : Nat) : ∀ f : NF, ¬ Occurs i f → Thm Ax (imp f (all i f)) :=
  Tarski.vac_of_not_occurs hC i

end Standard
section Restricted
open KThmK
example {G : List NF} {a : NF} : Der NF.imp (ThmK Ax) (a :: G) a := by
  first | exact KThmK.h0 | apply KThmK.h0 <;> assumption

example {G : List NF} {a b : NF} : Der NF.imp (ThmK Ax) (b :: a :: G) a := by
  first | exact KThmK.h1 | apply KThmK.h1 <;> assumption

example {G : List NF} {a b c : NF} : Der NF.imp (ThmK Ax) (c :: b :: a :: G) a := by
  first | exact KThmK.h2 | apply KThmK.h2 <;> assumption

example {a : NF} (d : Der NF.imp (ThmK Ax) [] a) : ThmK Ax a := by
  first | exact KThmK.thm_of_der0 | apply KThmK.thm_of_der0 <;> assumption

example {a c : NF} (d : Der NF.imp (ThmK Ax) [a] c) : ThmK Ax (imp a c) := by
  first | exact KThmK.ded1 | apply KThmK.ded1 <;> assumption

example {a b c : NF} (d : Der NF.imp (ThmK Ax) [b, a] c) : ThmK Ax (imp a (imp b c)) := by
  first | exact KThmK.ded2 | apply KThmK.ded2 <;> assumption

example {a b c d : NF} (dd : Der NF.imp (ThmK Ax) [c, b, a] d) :
    ThmK Ax (imp a (imp b (imp c d))) := by
  first | exact KThmK.ded3 | apply KThmK.ded3 <;> assumption

example {a b c : NF} (hab : ThmK Ax (imp a b)) (hbc : ThmK Ax (imp b c)) :
    ThmK Ax (imp a c) := by
  first | exact KThmK.syl | apply KThmK.syl <;> assumption

example (a b : NF) : ThmK Ax (imp (imp a b) (imp (neg b) (neg a))) := by
  first | exact KThmK.contra_thm | apply KThmK.contra_thm <;> assumption

example {a b : NF} (h : ThmK Ax (imp a b)) : ThmK Ax (imp (neg b) (neg a)) := by
  first | exact KThmK.contra | apply KThmK.contra <;> assumption

example (a : NF) : ThmK Ax (imp (neg (neg a)) a) := by
  first | exact KThmK.dne | apply KThmK.dne <;> assumption

example (a : NF) : ThmK Ax (imp a (neg (neg a))) := by
  first | exact KThmK.dni | apply KThmK.dni <;> assumption

example (a b c : NF) :
    ThmK Ax (imp (imp (neg a) c) (imp (imp b c) (imp (imp a b) c))) := by
  first | exact KThmK.imp_cases | apply KThmK.imp_cases <;> assumption

example (i : Nat) {a b : NF} (h : ThmK Ax (imp a b)) :
    ThmK Ax (imp (all i a) (all i b)) := by
  first | exact KThmK.all_mono | apply KThmK.all_mono <;> assumption

example (i : Nat) {a b : NF} (h : ThmK Ax (imp a b)) :
    ThmK Ax (imp (ex i a) (ex i b)) := by
  first | exact KThmK.ex_mono | apply KThmK.ex_mono <;> assumption

example {i : Nat} {a : NF} (h : ThmK Ax (imp a (all i a))) :
    ThmK Ax (imp (ex i a) a) := by
  first | exact KThmK.ex_elim_of_vac | apply KThmK.ex_elim_of_vac <;> assumption

example {i : Nat} {a : NF} (h : ThmK Ax (imp a (all i a))) :
    ThmK Ax (imp (neg a) (all i (neg a))) := by
  first | exact KThmK.vac_neg | apply KThmK.vac_neg <;> assumption

example (i : Nat) : ∀ f : NF, KThmK.EqFree f → ¬ Occurs i f →
    KThmK.ThmK Ax (imp f (all i f)) := KThmK.vac_of_not_occurs i

end Restricted
#print axioms NamedDerived.vac_of_not_occurs
#print axioms Tarski.vac_of_not_occurs
#print axioms KThmK.vac_of_not_occurs
#print axioms KThmK.spec
#print axioms KThmK.alpha_bwd
end SetTheory.BusyBeaver.ZFC.NamedDerivedAudit
