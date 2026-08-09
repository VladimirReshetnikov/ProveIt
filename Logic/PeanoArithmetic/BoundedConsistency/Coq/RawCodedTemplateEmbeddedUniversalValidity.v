(**
  A generic bridge from embedded-template validity to raw PA validity.

  The body formula stays universally quantified in this proof.  Clients can
  therefore instantiate the theorem with a very large concrete PA formula
  without forcing the kernel to normalize its full semantic expansion while
  matching [rawTemplateFormulaSat_embedPA].
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateSemantics.

Module PABoundedRawCodedTemplateEmbeddedUniversalValidity.

Import PA.
Import PAHierarchyReduction.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateSemantics.

(** Any environments may be used for template parameters and opaque
    predicates: an embedded PA formula consults neither of them. *)
Theorem raw_formula_sat_all_of_embedded_template_validity : forall
    (M : RawPAModel) (body : formula)
    (parameters : TemplateParameterName -> M)
    (predicates : TemplatePredicateName -> list M -> Prop),
  (forall (variables : nat -> M) level,
    rawTemplateFormulaSat M (scons M level variables)
      parameters predicates (embedPAFormula body)) ->
  forall variables,
    raw_formula_sat M variables (pAll body).
Proof.
  intros M body parameters predicates htemplate variables.
  cbn [raw_formula_sat]. intro level.
  apply (proj1 (rawTemplateFormulaSat_embedPA M
    (scons M level variables) parameters predicates body)).
  exact (htemplate variables level).
Qed.

End PABoundedRawCodedTemplateEmbeddedUniversalValidity.
