(** Assumption audit for the closed successor-bound case theorem. *)

From BoundedPAConsistency Require Import RawCodedLtSuccCasesSource.

Import PABoundedRawCodedLtSuccCasesSource.

Check codedLtSuccCasesFormula.
Check codedLtSuccCasesFormula_sentence.
Check codedLtSuccCasesFormula_raw_valid.
Check PA_proves_codedLtSuccCasesFormula.

Print Assumptions codedLtSuccCasesFormula_sentence.
Print Assumptions codedLtSuccCasesFormula_raw_valid.
Print Assumptions PA_proves_codedLtSuccCasesFormula.
