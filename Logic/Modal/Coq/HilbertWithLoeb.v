(**
  The raw axiom-parametric Hilbert calculus with Loeb's rule.

  This file independently ports the complete active declaration surface of
  the pinned Foundation module [Modal/Hilbert/WithLoeb/Basic.lean].  The
  source calculus fixes both an atom type and a predicate of raw axiom
  templates.  A template may enter a derivation through any endosubstitution;
  the remaining rules are modus ponens, necessitation, Loeb's rule, and the
  classical Lukasiewicz K/S/EC basis.

  Foundation's final [Entailment.K4Loeb] instance is represented by the
  weakest matching structural record.  In particular, it does not silently
  strengthen the calculus to this repository's extensional
  [normal_logic].  Diamond duality is proved constructively from K/S because
  diamond is definitionally [not box not] in this syntax.  Structural
  substitution remains a separate theorem, just as requested by the source
  interface boundary.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  Syntax Axioms HilbertK LogicInfrastructure EntailmentExtensions
  HilbertAxiom HilbertWithRE.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Arguments raw_K_p {AtomType Ax} _.
Arguments raw_K_q {AtomType Ax} _.
Arguments raw_K_ne {AtomType Ax} _.
Arguments raw_K_mem {AtomType Ax} _.
Arguments raw_Four_p {AtomType Ax} _.
Arguments raw_Four_mem {AtomType Ax} _.

(** The rule component used by Foundation's [Entailment.LoebRule]. *)
Definition loeb_rule {AtomType}
    (L0 : modal_logic_set AtomType) : Prop :=
  forall p, L0 (Imp (Box p) p) -> L0 p.

(** The exact local capability surface of Foundation's
    [Entailment.K4Loeb]: Lukasiewicz propositional reasoning, modal K,
    explicit diamond duality, necessitation, axiom Four, and Loeb's rule. *)
Record structural_k4loeb_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_k4loeb_lukasiewicz : lukasiewicz_entailment L0;
  structural_k4loeb_K : has_K L0;
  structural_k4loeb_dia_duality : has_DiaDuality L0;
  structural_k4loeb_necessitation : necessitation L0;
  structural_k4loeb_Four : has_Four L0;
  structural_k4loeb_loeb_rule : loeb_rule L0
}.

(** Source declaration 1/17: the seven constructors of [WithLoeb Ax]. *)
Inductive with_loeb_proves {AtomType : Type}
    (Ax : raw_modal_axiom AtomType) : formula AtomType -> Prop :=
| WL_axm : forall p (sigma : AtomType -> formula AtomType),
    Ax p -> with_loeb_proves Ax (substitute sigma p)
| WL_mp : forall p q,
    with_loeb_proves Ax (Imp p q) ->
    with_loeb_proves Ax p ->
    with_loeb_proves Ax q
| WL_nec : forall p,
    with_loeb_proves Ax p ->
    with_loeb_proves Ax (Box p)
| WL_loeb : forall p,
    with_loeb_proves Ax (Imp (Box p) p) ->
    with_loeb_proves Ax p
| WL_imply_K : forall p q,
    with_loeb_proves Ax (Hilbert_imply_K p q)
| WL_imply_S : forall p q r,
    with_loeb_proves Ax (Hilbert_imply_S p q r)
| WL_elim_contra : forall p q,
    with_loeb_proves Ax (Hilbert_elim_contra p q).

Arguments WL_axm {AtomType Ax p} sigma _.
Arguments WL_mp {AtomType Ax p q} _ _.
Arguments WL_nec {AtomType Ax p} _.
Arguments WL_loeb {AtomType Ax p} _.
Arguments WL_imply_K {AtomType Ax} p q.
Arguments WL_imply_S {AtomType Ax} p q r.
Arguments WL_elim_contra {AtomType Ax} p q.

(** Source declaration 2/17: [axm!], with an arbitrary substitution. *)
Lemma with_loeb_axm_substituted :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType) p
         (sigma : AtomType -> formula AtomType),
    Ax p -> with_loeb_proves Ax (substitute sigma p).
Proof. intros; now apply WL_axm. Qed.

(** Source declaration 3/17: [axm'!], using the identity substitution. *)
Lemma with_loeb_axm :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType) p,
    Ax p -> with_loeb_proves Ax p.
Proof.
  intros AtomType Ax p Hp.
  replace p with (substitute (@Atom AtomType) p).
  - now apply WL_axm.
  - apply substitute_id.
Qed.

(** Source declaration 4/17: the Lukasiewicz entailment instance. *)
Lemma with_loeb_lukasiewicz :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType),
    lukasiewicz_entailment (@with_loeb_proves AtomType Ax).
Proof.
  intros AtomType Ax; constructor.
  - apply WL_imply_K.
  - apply WL_imply_S.
  - apply WL_elim_contra.
  - intros p q Hpq Hp. exact (WL_mp Hpq Hp).
Qed.

(** Source declaration 5/17: necessitation. *)
Lemma with_loeb_necessitation :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType),
    necessitation (@with_loeb_proves AtomType Ax).
Proof.
  intros AtomType Ax p Hp. exact (WL_nec Hp).
Qed.

(** Source declaration 6/17: Loeb's rule. *)
Lemma with_loeb_loeb_rule :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType),
    loeb_rule (@with_loeb_proves AtomType Ax).
Proof.
  intros AtomType Ax p Hp. exact (WL_loeb Hp).
Qed.

(** Source declaration 7/17: structural endosubstitution. *)
Lemma with_loeb_proves_substitute :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (sigma : AtomType -> formula AtomType) p,
    with_loeb_proves Ax p ->
    with_loeb_proves Ax (substitute sigma p).
Proof.
  intros AtomType Ax sigma p Hp; induction Hp; simpl.
  - rewrite substitute_comp. now apply WL_axm.
  - exact (WL_mp IHHp1 IHHp2).
  - exact (WL_nec IHHp).
  - exact (WL_loeb IHHp).
  - apply WL_imply_K.
  - apply WL_imply_S.
  - apply WL_elim_contra.
Qed.

(** Source declaration 8/17: the proof-indexed, Prop-valued [rec!] fold.
    Foundation writes the motive codomain as bare [Sort], which elaborates to
    [Sort 0]; retaining the derivation index is therefore exact. *)
Lemma with_loeb_proves_fold :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (P : forall p, with_loeb_proves Ax p -> Prop),
    (forall p sigma (h : Ax p),
      P (substitute sigma p) (@WL_axm AtomType Ax p sigma h)) ->
    (forall p q
       (hpq : with_loeb_proves Ax (Imp p q))
       (hp : with_loeb_proves Ax p),
      P (Imp p q) hpq -> P p hp ->
      P q (@WL_mp AtomType Ax p q hpq hp)) ->
    (forall p (hp : with_loeb_proves Ax p),
      P p hp -> P (Box p) (@WL_nec AtomType Ax p hp)) ->
    (forall p (hp : with_loeb_proves Ax (Imp (Box p) p)),
      P (Imp (Box p) p) hp ->
      P p (@WL_loeb AtomType Ax p hp)) ->
    (forall p q,
      P (Hilbert_imply_K p q) (@WL_imply_K AtomType Ax p q)) ->
    (forall p q r,
      P (Hilbert_imply_S p q r) (@WL_imply_S AtomType Ax p q r)) ->
    (forall p q,
      P (Hilbert_elim_contra p q) (@WL_elim_contra AtomType Ax p q)) ->
    forall p (d : with_loeb_proves Ax p), P p d.
Proof.
  intros AtomType Ax P Hax Hmp Hnec Hloeb HK HS HEC p d.
  exact ((fix fold p0 (d0 : with_loeb_proves Ax p0) {struct d0}
      : P p0 d0 :=
    match d0 as d1 in with_loeb_proves _ p1 return P p1 d1 with
    | @WL_axm _ _ q sigma h => Hax q sigma h
    | @WL_mp _ _ q r hqr hq =>
        Hmp q r hqr hq (fold (Imp q r) hqr) (fold q hq)
    | @WL_nec _ _ q hq => Hnec q hq (fold q hq)
    | @WL_loeb _ _ q hq => Hloeb q hq (fold (Imp (Box q) q) hq)
    | @WL_imply_K _ _ q r => HK q r
    | @WL_imply_S _ _ q r s => HS q r s
    | @WL_elim_contra _ _ q r => HEC q r
    end) p d).
Qed.

(** Source declaration 9/17: weakening by target-provable raw axioms. *)
Lemma with_loeb_weaker_of_provable_axioms :
  forall (AtomType : Type)
         (Ax1 Ax2 : raw_modal_axiom AtomType),
    (forall p, Ax1 p -> with_loeb_proves Ax2 p) ->
    logic_subset (@with_loeb_proves AtomType Ax1)
                 (@with_loeb_proves AtomType Ax2).
Proof.
  intros AtomType Ax1 Ax2 Haxioms p Hp; induction Hp.
  - now apply with_loeb_proves_substitute, Haxioms.
  - exact (WL_mp IHHp1 IHHp2).
  - exact (WL_nec IHHp).
  - exact (WL_loeb IHHp).
  - apply WL_imply_K.
  - apply WL_imply_S.
  - apply WL_elim_contra.
Qed.

(** Source declaration 10/17: weakening by inclusion of raw axioms. *)
Lemma with_loeb_weaker_of_subset_axioms :
  forall (AtomType : Type)
         (Ax1 Ax2 : raw_modal_axiom AtomType),
    (forall p, Ax1 p -> Ax2 p) ->
    logic_subset (@with_loeb_proves AtomType Ax1)
                 (@with_loeb_proves AtomType Ax2).
Proof.
  intros AtomType Ax1 Ax2 Hsubset.
  apply with_loeb_weaker_of_provable_axioms.
  intros p Hp. apply with_loeb_axm. now apply Hsubset.
Qed.

(** Constructive propositional support for definitional diamond duality. *)
Local Lemma with_loeb_identity :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (p : formula AtomType),
    with_loeb_proves Ax (Imp p p).
Proof.
  intros AtomType Ax p.
  eapply WL_mp.
  - eapply WL_mp.
    + exact (WL_imply_S p (Imp p p) p).
    + exact (WL_imply_K p (Imp p p)).
  - exact (WL_imply_K p p).
Qed.

Local Lemma with_loeb_imply_intro :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (p q : formula AtomType),
    with_loeb_proves Ax q ->
    with_loeb_proves Ax (Imp p q).
Proof.
  intros AtomType Ax p q Hq.
  eapply WL_mp; [exact (WL_imply_K q p) | exact Hq].
Qed.

Local Lemma with_loeb_under_mp :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (a p q : formula AtomType),
    with_loeb_proves Ax (Imp a (Imp p q)) ->
    with_loeb_proves Ax (Imp a p) ->
    with_loeb_proves Ax (Imp a q).
Proof.
  intros AtomType Ax a p q Hpq Hp.
  eapply WL_mp.
  - eapply WL_mp; [exact (WL_imply_S a p q) | exact Hpq].
  - exact Hp.
Qed.

Local Lemma with_loeb_and_intro :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (p q : formula AtomType),
    with_loeb_proves Ax p ->
    with_loeb_proves Ax q ->
    with_loeb_proves Ax (And p q).
Proof.
  intros AtomType Ax p q Hp Hq.
  unfold And, Neg.
  set (a := Imp p (Imp q Bottom)).
  pose proof
    (@with_loeb_imply_intro AtomType Ax a q Hq) as Haq.
  pose proof
    (@with_loeb_imply_intro AtomType Ax a p Hp) as Hap.
  pose proof (@with_loeb_identity AtomType Ax a) as Haa.
  change (with_loeb_proves Ax
    (Imp a (Imp p (Imp q Bottom)))) in Haa.
  pose proof
    (@with_loeb_under_mp AtomType Ax a p (Imp q Bottom) Haa Hap)
    as Hanq.
  exact (@with_loeb_under_mp AtomType Ax a q Bottom Hanq Haq).
Qed.

Local Lemma with_loeb_iff_refl :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (p : formula AtomType),
    with_loeb_proves Ax (Iff p p).
Proof.
  intros AtomType Ax p; unfold Iff.
  apply with_loeb_and_intro; apply with_loeb_identity.
Qed.

Local Lemma with_loeb_has_DiaDuality :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType),
    has_DiaDuality (@with_loeb_proves AtomType Ax).
Proof.
  intros AtomType Ax; constructor; intro p.
  unfold DiaDuality, Dia.
  apply with_loeb_iff_refl.
Qed.

(** Generic instantiation of unary and binary raw templates. *)
Local Lemma with_loeb_instantiate_unary :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (eq_dec : atom_decidable_equality AtomType)
         (Schema : formula AtomType -> formula AtomType) a,
    (forall sigma x,
      substitute sigma (Schema x) = Schema (substitute sigma x)) ->
    Ax (Schema (Atom a)) ->
    forall p, with_loeb_proves Ax (Schema p).
Proof.
  intros AtomType Ax eq_dec Schema a Hschema Hmem p.
  pose proof
    (@WL_axm AtomType Ax (Schema (Atom a))
      (with_re_single_substitution eq_dec a p) Hmem) as Hproof.
  rewrite Hschema in Hproof; simpl in Hproof.
  rewrite with_re_single_substitution_at in Hproof.
  exact Hproof.
Qed.

Local Lemma with_loeb_instantiate_binary :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (eq_dec : atom_decidable_equality AtomType)
         (Schema : formula AtomType -> formula AtomType -> formula AtomType)
         a b,
    a <> b ->
    (forall sigma x y,
      substitute sigma (Schema x y) =
      Schema (substitute sigma x) (substitute sigma y)) ->
    Ax (Schema (Atom a) (Atom b)) ->
    forall p q, with_loeb_proves Ax (Schema p q).
Proof.
  intros AtomType Ax eq_dec Schema a b Hab Hschema Hmem p q.
  pose proof
    (@WL_axm AtomType Ax (Schema (Atom a) (Atom b))
      (with_re_double_substitution eq_dec a b p q) Hmem) as Hproof.
  rewrite Hschema in Hproof; simpl in Hproof.
  rewrite with_re_double_substitution_left in Hproof.
  rewrite with_re_double_substitution_right in Hproof by exact Hab.
  exact Hproof.
Qed.

(** Source declaration 11/17: derive modal K from a raw K template. *)
Lemma with_loeb_has_K :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType),
    atom_decidable_equality AtomType ->
    raw_axioms_has_K Ax ->
    has_K (@with_loeb_proves AtomType Ax).
Proof.
  intros AtomType Ax eq_dec Hraw; constructor; intros p q.
  eapply (@with_loeb_instantiate_binary AtomType Ax eq_dec
    (@K AtomType) (raw_K_p Hraw) (raw_K_q Hraw)).
  - exact (raw_K_ne Hraw).
  - reflexivity.
  - exact (raw_K_mem Hraw).
Qed.

(** Source declaration 12/17: derive Four from a raw Four template. *)
Lemma with_loeb_has_Four :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType),
    atom_decidable_equality AtomType ->
    raw_axioms_has_Four Ax ->
    has_Four (@with_loeb_proves AtomType Ax).
Proof.
  intros AtomType Ax eq_dec Hraw; constructor; intro p.
  eapply (@with_loeb_instantiate_unary AtomType Ax eq_dec
    (@Four AtomType) (raw_Four_p Hraw));
    [reflexivity | exact (raw_Four_mem Hraw)].
Qed.

(** Source declaration 13/17: the exact two-template raw K4 axiom set. *)
Definition with_loeb_K4_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = Four (Atom 0).

(** Source declaration 14/17: membership witnesses modal K. *)
Definition with_loeb_K4_axioms_has_K :
  raw_axioms_has_K with_loeb_K4_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 15/17: membership witnesses Four. *)
Definition with_loeb_K4_axioms_has_Four :
  raw_axioms_has_Four with_loeb_K4_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; reflexivity.
Defined.

(** Source declaration 16/17: the named logic [K4Loeb]. *)
Definition with_loeb_K4_proves : modal_logic_set nat :=
  @with_loeb_proves nat with_loeb_K4_axioms.

(** Source declaration 17/17: the final [Entailment.K4Loeb] instance. *)
Lemma with_loeb_K4Loeb_entailment :
  structural_k4loeb_entailment with_loeb_K4_proves.
Proof.
  constructor.
  - apply with_loeb_lukasiewicz.
  - exact (@with_loeb_has_K nat with_loeb_K4_axioms Nat.eq_dec
      with_loeb_K4_axioms_has_K).
  - apply with_loeb_has_DiaDuality.
  - apply with_loeb_necessitation.
  - exact (@with_loeb_has_Four nat with_loeb_K4_axioms Nat.eq_dec
      with_loeb_K4_axioms_has_Four).
  - apply with_loeb_loeb_rule.
Qed.
