From BoundedPAConsistency Require Import
  RawCodedFormulaBoundAllCarrierTotality.

Import PABoundedRawCodedFormulaBoundAllCarrierTotality.

(** The audit deliberately exposes the definable prefix, rather than only
    the final existential theorem.  This makes it possible to check that the
    proof really constructs source/bound beta columns through a nonstandard
    carrier limit. *)
Check RawCodedTermBoundPrefixRows.
Check RawCodedTermBoundPrefixNormalized.
Check RawCodedTermBoundPrefix.
Check RawCodedTermBoundPrefixExists.
Check RawCodedTermBoundPrefixWithin.

Check raw_termBoundTraversalRow_prefix_extend.
Check raw_codedTermBoundPrefix_zero.
Check raw_codedTermBoundPrefix_succ.
Check raw_codedTermBoundPrefixWithin_all.
Check raw_codedTermBound_exists_of_syntax_realizable.

Print Assumptions raw_sat_codedTermBoundPrefixRowsTermAt_iff.
Print Assumptions raw_sat_codedTermBoundPrefixNormalizedTermAt_iff.
Print Assumptions raw_sat_codedTermBoundPrefixTermAt_iff.
Print Assumptions raw_sat_codedTermBoundPrefixExistsTermAt_iff.
Print Assumptions raw_sat_codedTermBoundPrefixWithinTermAt_iff.
Print Assumptions raw_termBoundTraversalRow_prefix_extend.
Print Assumptions raw_codedTermBoundPrefix_succ.
Print Assumptions raw_codedTermBoundPrefixWithin_all.
Print Assumptions raw_codedTermBound_exists_of_syntax_realizable.
