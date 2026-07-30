(** Letterless formulas coincide in intuitionistic and classical logic.

    This ports Foundation's [Propositional/Logic/Letterless_Int_Cl.lean].
    The source routes the main result through modal companions.  Here a more
    direct semantic invariant is available: a formula without atoms has the
    same truth value at every intuitionistic Kripke world as under Boolean
    evaluation.  Classical soundness and intuitionistic completeness then
    give the result immediately, without atom equality or coding premises. *)

From FoundationModal Require Import
  Syntax LogicInfrastructure GodelTranslation PropositionalFormula
  PropositionalHilbert PropositionalBoolean PropositionalBooleanHilbert
  PropositionalKripke PropositionalKripkeCanonical.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Lemma godel_translate_letterless :
  forall (Atom : Type) (p : pformula Atom),
    pformula_letterless p ->
    formula_letterless (godel_translate p).
Proof.
  intros Atom p; induction p as
      [a| |p IHp q IHq|p IHp q IHq|p IHp q IHq];
    cbn [godel_translate And Or Neg formula_letterless] in *; firstorder.
Qed.

(** The Boolean valuation is arbitrary: letterlessness makes its atom values
    irrelevant.  The implication case is the useful core—both subformulas
    retain their Boolean values at every future world. *)
Theorem pkripke_letterless_forces_iff_boolean :
  forall (Atom : Type) (p : pformula Atom),
    pformula_letterless p ->
    forall (M : pkripke_model Atom)
      (w : pkripke_world (pkripke_model_frame M))
      (rho : pvaluation Atom),
      pkripke_forces M w p <-> pboolean_eval rho p.
Proof.
  intros Atom p; induction p as
      [a| |p IHp q IHq|p IHp q IHq|p IHp q IHq];
    intros Hletter M w rho.
  - contradiction.
  - reflexivity.
  - destruct Hletter as [Hp Hq]. cbn.
    now rewrite (IHp Hp M w rho), (IHq Hq M w rho).
  - destruct Hletter as [Hp Hq]. cbn.
    now rewrite (IHp Hp M w rho), (IHq Hq M w rho).
  - destruct Hletter as [Hp Hq]. cbn. split.
    + intros Hforce Hboolp.
      apply (proj1 (IHq Hq M w rho)).
      apply (Hforce w (pkripke_access_refl _ w)).
      now apply (proj2 (IHp Hp M w rho)).
    + intros Hbool u Rwu Hup.
      apply (proj2 (IHq Hq M u rho)), Hbool.
      now apply (proj1 (IHp Hp M u rho)).
Qed.

Corollary pkripke_letterless_forcing_invariant :
  forall (Atom : Type) (p : pformula Atom),
    pformula_letterless p ->
    forall (M N : pkripke_model Atom)
      (w : pkripke_world (pkripke_model_frame M))
      (u : pkripke_world (pkripke_model_frame N)),
      pkripke_forces M w p <-> pkripke_forces N u p.
Proof.
  intros Atom p Hletter M N w u.
  transitivity (pboolean_eval (fun _ => False) p).
  - exact (@pkripke_letterless_forces_iff_boolean Atom p Hletter M w
      (fun _ => False)).
  - symmetry. exact (@pkripke_letterless_forces_iff_boolean Atom p Hletter N u
      (fun _ => False)).
Qed.

Theorem ph_hilbert_letterless_int_iff_cl :
  forall p : pformula nat,
    pformula_letterless p ->
    (ph_hilbert_provable (ph_hilbert_int nat) p <->
     ph_hilbert_provable (ph_hilbert_cl nat) p).
Proof.
  intros p Hletter; split.
  - intro Hint.
    eapply ph_hilbert_provable_of_schema_inclusion; [| exact Hint].
    exact (@ph_hilbert_int_le_cl nat).
  - intro Hcl. apply ph_hilbert_int_pkripke_complete.
    intros F _ V w.
    apply (proj2 (@pkripke_letterless_forces_iff_boolean nat p Hletter
      {| pkripke_model_frame := F; pkripke_model_valuation := V |}
      w (fun _ => False))).
    exact (ph_cl_provable_sound Hcl (fun _ => False)).
Qed.
