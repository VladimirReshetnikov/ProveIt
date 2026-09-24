import Diophantine.Common.MRDPCore
import Diophantine.Common.MathlibDiophFinite

/-!
# Recursively enumerable predicates are Diophantine

The concise Chinese-remainder proof in `Common/MRDPCore.lean` produces one
integer polynomial with finitely many natural witnesses. This module adapts
that result to Mathlib's `Dioph` predicate, the interface used by the article
formalizations. The scalar bounded-evaluator lemma remains available as an
independent computational interface.
-/

namespace Diophantine

/-- The encoded bounded evaluation of a fixed program is primitive recursive
as a scalar natural function. The paired input contains the bound first. -/
theorem encoded_evaln_natPrimrec (c : Nat.Partrec.Code) :
    Nat.Primrec (fun packed : ℕ => Encodable.encode
      (Nat.Partrec.Code.evaln packed.unpair.1 c packed.unpair.2)) := by
  have hinput : Primrec (fun packed : ℕ => ((packed.unpair.1, c), packed.unpair.2)) :=
    ((Primrec.fst.comp Primrec.unpair).pair (Primrec.const c)).pair
      (Primrec.snd.comp Primrec.unpair)
  have heval : Primrec (fun packed : ℕ =>
      Nat.Partrec.Code.evaln packed.unpair.1 c packed.unpair.2) :=
    Nat.Partrec.Code.primrec_evaln.comp hinput
  exact Primrec.nat_iff.mp (Primrec.encode_iff.mpr heval)

/-- Every recursively enumerable predicate on the natural numbers is
Diophantine, including its behavior at zero. All computational and trace
representation steps are proved; no computability theorem is assumed. -/
theorem rePred_dioph {S : Set ℕ} (hS : REPred S) :
    Dioph {v : Unit → ℕ | v () ∈ S} := by
  obtain ⟨k, polynomial, hPolynomial⟩ := MRDP.mrdp hS
  refine dioph_iff_exists_fin_polynomial.mpr ⟨k, polynomial, ?_⟩
  intro v
  -- A Unit-indexed assignment is determined by its sole input coordinate.
  have hInput : (fun _ : Unit => v ()) = v :=
    funext fun i => congrArg v (Subsingleton.elim _ _)
  simpa [hInput, Function.comp_def, Int.ofNatHom] using hPolynomial (v ())

end Diophantine
