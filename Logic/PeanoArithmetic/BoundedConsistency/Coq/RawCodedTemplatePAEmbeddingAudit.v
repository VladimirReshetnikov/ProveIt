(** Assumption and API audit for the ordinary-PA/template bridge. *)

From BoundedPAConsistency Require Import
  RawCodedTemplatePAEmbedding.

Import PABoundedRawCodedTemplatePAEmbedding.

Check embedRawProof.
Check embedRawProof_context.
Check embedRawProof_conclusion.
Check embedRawProof_valid.

Check RawCodedTemplatePAAgreement.
Check rawTemplateTerm_embedPA.
Check rawTemplateFormula_embedPA.
Check raw_templateContextCode_embedPA.
Check raw_templateContextCode_embedPA_numeral.
Check raw_templateProofCode_embedPA.

Check rawTemplatePAProofCertificate.
Check raw_codedTemplatePAProofOf_standard.
Check raw_codedTemplatePAProofOf_of_BProv.

Print Assumptions embedRawProof_valid.
Print Assumptions raw_templateContextCode_embedPA.
Print Assumptions raw_templateProofCode_embedPA.
Print Assumptions raw_codedTemplatePAProofOf_standard.
Print Assumptions raw_codedTemplatePAProofOf_of_BProv.
