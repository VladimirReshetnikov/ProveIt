(** Public surface and assumption audit for model-coded proof templates. *)

From BoundedPAConsistency Require Import RawCodedTemplateSyntax.

Import PABoundedRawCodedTemplateSyntax.

Check TemplateTerm.
Check TemplateFormula.
Check TemplateContext.
Check ttVar.
Check ttParameter.
Check tfOpaque.

Check templateUpRenaming.
Check templateTermRename.
Check templateFormulaRename.
Check templateTermUpSubst.
Check templateTermSubst.
Check templateFormulaSubst.
Check templateInstTerm.
Check templateFormulaOpen.
Check templateContextShift.

Check templateTermRename_id.
Check templateFormulaRename_id.
Check templateTermRename_comp.
Check templateFormulaRename_comp.
Check templateTermSubst_id.
Check templateFormulaSubst_id.
Check templateFormulaSubst_variables.
Check templateOpaqueRename_arity.
Check templateOpaqueSubst_arity.

Check embedPATerm.
Check embedPAFormula.
Check embedPAContext.
Check embedPATerm_rename.
Check embedPATerm_subst.
Check embedPAFormula_rename.
Check embedPAFormula_subst.
Check embedPAFormula_instTerm.
Check embedPAContext_shift.
Check embedPAContext_subst.

Check TemplateRawProof.
Check trpAss.
Check trpImpI.
Check trpImpE.
Check trpBotE.
Check trpLem.
Check trpAndI.
Check trpAndE1.
Check trpAndE2.
Check trpOrI1.
Check trpOrI2.
Check trpOrE.
Check trpAllI.
Check trpAllE.
Check trpExI.
Check trpExE.
Check trpEqRefl.
Check trpEqElim.
Check templateRawContext.
Check templateRawConclusion.
Check TemplateRawProofValid.
Check TemplateRawDerives.
Check templateRawDerives_assumption.
Check templateRawDerives_eqRefl.

Print Assumptions templateFormulaRename_comp.
Print Assumptions templateFormulaSubst_id.
Print Assumptions templateFormulaSubst_variables.
Print Assumptions embedPAFormula_rename.
Print Assumptions embedPAFormula_subst.
Print Assumptions embedPAFormula_instTerm.
Print Assumptions embedPAContext_shift.
Print Assumptions templateRawDerives_assumption.
Print Assumptions templateRawDerives_eqRefl.
