import DiophantineConsistency.ScalarPRCode
import Mathlib.Computability.RE

/-! The existing data-valued certificate implies primitive recursiveness.
    No actual program is synthesized from a proposition-valued proof. -/
namespace CertificateReuse
open DiophantineConsistency

/-- Consume the stronger, already supplied certificate. -/
theorem realizes_natPrimrec {f : ℕ → ℕ} (p : ScalarPRCode.Realizes f) :
    Nat.Primrec f :=
  p.val.primrec.of_eq p.property

/-- Semidecidability of eventual success, directly from a scalar test. -/
theorem eventually_one_re (f : ℕ → ℕ) (hf : Nat.Primrec f) :
    REPred (fun _ : ℕ => ∃ t, f t = 1) := by
  have ht : Primrec (fun v : ℕ × ℕ => decide (f v.2 = 1)) :=
    (Primrec.eq.comp ((Primrec.nat_iff.mpr hf).comp Primrec.snd)
      (Primrec.const 1)).decide
  have hsearch : Partrec (fun _ : ℕ => Nat.rfind
      (fun t => Part.some (decide (f t = 1)))) :=
    Partrec.rfind ht.to_comp.partrec
  apply hsearch.dom_re.of_eq
  intro _
  simp only [Nat.rfind_dom, Part.mem_some_iff, true_eq_decide_iff,
    Part.some_dom, implies_true, and_true]

/-- The bridge has a generic interface matching the actual repository endpoint. -/
theorem represented_success_re {f : ℕ → ℕ} {P : Prop}
    (p : ScalarPRCode.Realizes f) (h : (∃ t, f t = 1) ↔ P) :
    REPred (fun _ : ℕ => P) :=
  (eventually_one_re f (realizes_natPrimrec p)).of_eq (fun _ => h)

#print axioms realizes_natPrimrec
#print axioms eventually_one_re
#print axioms represented_success_re
end CertificateReuse
