(** Audit surface for template renaming/substitution interchange. *)

From BoundedPAConsistency Require Import
  RawCodedTemplateRenamingSubstitution.

Import PABoundedRawCodedTemplateRenamingSubstitution.

Check templateTermRename_subst.
Check templateTermsRename_subst.
Check templateTermRename_upSubst.
Check templateFormulaRename_subst.
Check templateTermSubst_rename.
Check templateTermsSubst_rename.
Check templateTermUpSubst_upRenaming.
Check templateFormulaSubst_rename.
Check templateFormulaOpen_rename_succ.
Check templateFormulaRename_open.

Print Assumptions templateFormulaRename_subst.
Print Assumptions templateFormulaSubst_rename.
Print Assumptions templateFormulaOpen_rename_succ.
Print Assumptions templateFormulaRename_open.
