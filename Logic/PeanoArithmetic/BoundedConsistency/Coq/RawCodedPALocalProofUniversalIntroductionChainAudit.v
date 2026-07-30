(** Public surface and assumption audit for repeated represented [AllI]. *)

From BoundedPAConsistency Require Import
  RawCodedPALocalProofUniversalIntroductionChain.

Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.

Check templateContextShiftMany.
Check templateFormulaAllMany.
Check raw_codedPALocalProofOf_universal_introduction_chain.

Print Assumptions raw_codedPALocalProofOf_universal_introduction_chain.
