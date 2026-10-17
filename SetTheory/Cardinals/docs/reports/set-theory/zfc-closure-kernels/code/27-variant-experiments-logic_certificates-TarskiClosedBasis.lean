import BusyBeaver.ZFC.TarskiComplete
import BusyBeaver.ZFC.LukasiewiczCertificate

/-! Proposed adapter: uncompiled in the delivery environment. -/
namespace SetTheory.BusyBeaver.ZFC.Tarski
open NF

/-- Completeness with no propositional-basis assumptions. -/
theorem completeness_from_certificate {Ax : NF → Prop} (f : NF)
    (hval : ∀ (D : Type) (mem : D → D → Prop),
      (∀ a, Ax a → ∀ e : Nat → D, Sat mem e a) →
        ∀ e : Nat → D, Sat mem e f) : Thm Ax f :=
  completeness (certificate_classical Ax)
    (certificate_classical (fun _ => False)) f hval

#print axioms completeness_from_certificate
end SetTheory.BusyBeaver.ZFC.Tarski
