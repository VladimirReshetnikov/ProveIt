(** Abstract substitution- and modus-ponens-closed propositional logics.

    This module ports [Propositional/Logic/Basic.lean].  Predicate fields are
    used directly instead of a SetLike coercion, keeping all closure laws
    explicit and constructive. *)

From FoundationModal Require Import PropositionalFormula.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record pformula_logic (Atom : Type) : Type := {
  pformula_logic_theorems : pformula Atom -> Prop;
  pformula_logic_substitute :
    forall (sigma : psubstitution Atom Atom) p,
      pformula_logic_theorems p ->
      pformula_logic_theorems (pformula_substitute sigma p);
  pformula_logic_mdp :
    forall p q,
      pformula_logic_theorems (PImp p q) ->
      pformula_logic_theorems p ->
      pformula_logic_theorems q
}.

Arguments pformula_logic_theorems {Atom} _ _.
Arguments pformula_logic_substitute {Atom} _ _ _ _.
Arguments pformula_logic_mdp {Atom} _ _ _ _ _.

Definition pformula_logic_trivial {Atom : Type} : pformula_logic Atom :=
  {| pformula_logic_theorems := fun _ => True;
     pformula_logic_substitute := fun _ _ _ => I;
     pformula_logic_mdp := fun _ _ _ _ => I |}.

Definition pformula_logic_is_trivial {Atom : Type}
    (L : pformula_logic Atom) : Prop :=
  forall p, pformula_logic_theorems L p.

Lemma pformula_logic_trivial_is_trivial :
  forall Atom : Type,
    pformula_logic_is_trivial (@pformula_logic_trivial Atom).
Proof. intros Atom p. exact I. Qed.

Record pformula_logic_extension {Atom : Type}
    (L : pformula_logic Atom) : Type := {
  pformula_logic_extension_logic : pformula_logic Atom;
  pformula_logic_extension_includes :
    forall p,
      pformula_logic_theorems L p ->
      pformula_logic_theorems pformula_logic_extension_logic p
}.

Arguments pformula_logic_extension_logic {Atom L} _.
Arguments pformula_logic_extension_includes {Atom L} _ _ _.

Definition pformula_logic_subset {Atom : Type}
    (L K : pformula_logic Atom) : Prop :=
  forall p,
    pformula_logic_theorems L p -> pformula_logic_theorems K p.

Lemma pformula_logic_subset_refl :
  forall (Atom : Type) (L : pformula_logic Atom),
    pformula_logic_subset L L.
Proof. intros Atom L p Hp. exact Hp. Qed.

Lemma pformula_logic_subset_trans :
  forall (Atom : Type) (L K M : pformula_logic Atom),
    pformula_logic_subset L K ->
    pformula_logic_subset K M ->
    pformula_logic_subset L M.
Proof. intros Atom L K M Hlk Hkm p Hp. apply Hkm, Hlk, Hp. Qed.
