(** Assumption and API audit for the generic-FOL/template proof bridge. *)

From BoundedPAConsistency Require Import
  RawCodedFolTemplateProofCompiler.

Import PABoundedRawCodedFolTemplateProofCompiler.

Check folMembershipTemplatePredicateName.
Check folTemplateFormula.
Check folTemplateContext.

Check folTemplateFormula_rename.
Check folTemplateContext_rename.
Check folTemplateContext_shift.
Check folTemplateFormula_inst.

Check FolTemplateCompiledDerivation.
Check fol_prov_compiles.
Check fol_prov_has_valid_template_raw_proof.

Check FolLogicallyValid.
Check fol_logically_valid_compiles.

(** The structural compiler itself is constructive.  The final optional
    theorem deliberately exposes whatever classical assumptions are carried
    by the repository's generic Goedel-completeness proof. *)
Print Assumptions folTemplateFormula_rename.
Print Assumptions folTemplateFormula_inst.
Print Assumptions fol_prov_compiles.
Print Assumptions fol_prov_has_valid_template_raw_proof.
Print Assumptions fol_logically_valid_compiles.
