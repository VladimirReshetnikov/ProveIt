(**
  The raw-axiom Hilbert calculus with the Henkin rule.

  This file independently ports the complete 17-declaration surface of the
  pinned Foundation module [Modal/Hilbert/WithHenkin/Basic.lean].  The core
  calculus is polymorphic in its atom type and retains Foundation's raw
  axiom templates: an axiom enters a proof only through an endosubstitution
  over that same atom type.

  The existing [K4Henkin_proves] calculus in [GLAlternativeSystems] is a
  concrete nat-atom presentation built by closing [K4_proves] under the
  Henkin rule.  It remains useful for the checked equivalence with GL, but it
  is not the arbitrary-axiom calculus ported here.

  Foundation's final [Entailment.K4Henkin] instance is represented by the
  structural bundle at the end of the file.  Its classical component is kept
  as the constructive Lukasiewicz basis, and definitional diamond duality is
  proved directly from K/S and modus ponens.  No extensional
  [classical_logic], semantic completeness, or [normal_logic] is used.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  Syntax Axioms HilbertK LogicInfrastructure EntailmentExtensions
  HilbertAxiom HilbertWithRE.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Foundation's theorem-level [HenkinRule] capability. *)
Definition henkin_rule {AtomType}
    (L : modal_logic_set AtomType) : Prop :=
  forall p, L (Iff (Box p) p) -> L p.

(** * The seven constructors of [Hilbert.WithHenkin] *)

Inductive with_henkin_proves {AtomType : Type}
    (Ax : raw_modal_axiom AtomType) : formula AtomType -> Prop :=
| WH_axm : forall p (sigma : AtomType -> formula AtomType),
    Ax p -> with_henkin_proves Ax (substitute sigma p)
| WH_mp : forall p q,
    with_henkin_proves Ax (Imp p q) ->
    with_henkin_proves Ax p ->
    with_henkin_proves Ax q
| WH_nec : forall p,
    with_henkin_proves Ax p ->
    with_henkin_proves Ax (Box p)
| WH_henkin : forall p,
    with_henkin_proves Ax (Iff (Box p) p) ->
    with_henkin_proves Ax p
| WH_imply_K : forall p q,
    with_henkin_proves Ax (Hilbert_imply_K p q)
| WH_imply_S : forall p q r,
    with_henkin_proves Ax (Hilbert_imply_S p q r)
| WH_elim_contra : forall p q,
    with_henkin_proves Ax (Hilbert_elim_contra p q).

Arguments WH_axm {AtomType Ax p} sigma _.
Arguments WH_mp {AtomType Ax p q} _ _.
Arguments WH_nec {AtomType Ax p} _.
Arguments WH_henkin {AtomType Ax p} _.
Arguments WH_imply_K {AtomType Ax} p q.
Arguments WH_imply_S {AtomType Ax} p q r.
Arguments WH_elim_contra {AtomType Ax} p q.

(** [axm!] in the source. *)
Lemma with_henkin_axm_substituted :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType) p
         (sigma : AtomType -> formula AtomType),
    Ax p -> with_henkin_proves Ax (substitute sigma p).
Proof. intros; now apply WH_axm. Qed.

(** [axm'!] in the source. *)
Lemma with_henkin_axm :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType) p,
    Ax p -> with_henkin_proves Ax p.
Proof.
  intros AtomType Ax p Hp.
  replace p with (substitute (@Atom AtomType) p).
  - now apply WH_axm.
  - apply substitute_id.
Qed.

(** * The four structural instances *)

Lemma with_henkin_lukasiewicz :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType),
    lukasiewicz_entailment (@with_henkin_proves AtomType Ax).
Proof.
  intros AtomType Ax; constructor.
  - apply WH_imply_K.
  - apply WH_imply_S.
  - apply WH_elim_contra.
  - intros p q Hpq Hp. exact (WH_mp Hpq Hp).
Qed.

Lemma with_henkin_necessitation :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType),
    necessitation (@with_henkin_proves AtomType Ax).
Proof.
  intros AtomType Ax p Hp. exact (WH_nec Hp).
Qed.

Lemma with_henkin_henkin_rule :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType),
    henkin_rule (@with_henkin_proves AtomType Ax).
Proof.
  intros AtomType Ax p Hp. exact (WH_henkin Hp).
Qed.

Lemma with_henkin_proves_substitute :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (sigma : AtomType -> formula AtomType) p,
    with_henkin_proves Ax p ->
    with_henkin_proves Ax (substitute sigma p).
Proof.
  intros AtomType Ax sigma p Hp; induction Hp; simpl.
  - rewrite substitute_comp. now apply WH_axm.
  - exact (WH_mp IHHp1 IHHp2).
  - exact (WH_nec IHHp).
  - exact (WH_henkin IHHp).
  - apply WH_imply_K.
  - apply WH_imply_S.
  - apply WH_elim_contra.
Qed.

(** * Exact Prop-valued dependent fold corresponding to [rec!] *)

Lemma with_henkin_proves_fold :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (P : forall p, with_henkin_proves Ax p -> Prop),
    (forall p sigma (h : Ax p),
      P (substitute sigma p) (@WH_axm AtomType Ax p sigma h)) ->
    (forall p q
       (hpq : with_henkin_proves Ax (Imp p q))
       (hp : with_henkin_proves Ax p),
      P (Imp p q) hpq -> P p hp ->
      P q (@WH_mp AtomType Ax p q hpq hp)) ->
    (forall p (hp : with_henkin_proves Ax p),
      P p hp -> P (Box p) (@WH_nec AtomType Ax p hp)) ->
    (forall p (hfixed : with_henkin_proves Ax (Iff (Box p) p)),
      P (Iff (Box p) p) hfixed ->
      P p (@WH_henkin AtomType Ax p hfixed)) ->
    (forall p q,
      P (Hilbert_imply_K p q) (@WH_imply_K AtomType Ax p q)) ->
    (forall p q r,
      P (Hilbert_imply_S p q r) (@WH_imply_S AtomType Ax p q r)) ->
    (forall p q,
      P (Hilbert_elim_contra p q) (@WH_elim_contra AtomType Ax p q)) ->
    forall p (d : with_henkin_proves Ax p), P p d.
Proof.
  intros AtomType Ax P Hax Hmp Hnec Hhenkin HK HS HEC p d.
  exact ((fix fold p0 (d0 : with_henkin_proves Ax p0) {struct d0}
      : P p0 d0 :=
    match d0 as d1 in with_henkin_proves _ p1 return P p1 d1 with
    | @WH_axm _ _ q sigma h => Hax q sigma h
    | @WH_mp _ _ q r hqr hq =>
        Hmp q r hqr hq (fold (Imp q r) hqr) (fold q hq)
    | @WH_nec _ _ q hq => Hnec q hq (fold q hq)
    | @WH_henkin _ _ q hq => Hhenkin q hq (fold (Iff (Box q) q) hq)
    | @WH_imply_K _ _ q r => HK q r
    | @WH_imply_S _ _ q r s => HS q r s
    | @WH_elim_contra _ _ q r => HEC q r
    end) p d).
Qed.

(** * Axiom weakening *)

Lemma with_henkin_weaker_of_provable_axioms :
  forall (AtomType : Type)
         (Ax1 Ax2 : raw_modal_axiom AtomType),
    (forall p, Ax1 p -> with_henkin_proves Ax2 p) ->
    logic_subset (@with_henkin_proves AtomType Ax1)
                 (@with_henkin_proves AtomType Ax2).
Proof.
  intros AtomType Ax1 Ax2 Haxioms p Hp; induction Hp.
  - now apply with_henkin_proves_substitute, Haxioms.
  - exact (WH_mp IHHp1 IHHp2).
  - exact (WH_nec IHHp).
  - exact (WH_henkin IHHp).
  - apply WH_imply_K.
  - apply WH_imply_S.
  - apply WH_elim_contra.
Qed.

Lemma with_henkin_weaker_of_subset_axioms :
  forall (AtomType : Type)
         (Ax1 Ax2 : raw_modal_axiom AtomType),
    (forall p, Ax1 p -> Ax2 p) ->
    logic_subset (@with_henkin_proves AtomType Ax1)
                 (@with_henkin_proves AtomType Ax2).
Proof.
  intros AtomType Ax1 Ax2 Hsubset.
  apply with_henkin_weaker_of_provable_axioms.
  intros p Hp. apply with_henkin_axm. now apply Hsubset.
Qed.

(** * Generic raw-template instantiation *)

Arguments raw_K_p {AtomType Ax} _.
Arguments raw_K_q {AtomType Ax} _.
Arguments raw_K_ne {AtomType Ax} _.
Arguments raw_K_mem {AtomType Ax} _.
Arguments raw_Four_p {AtomType Ax} _.
Arguments raw_Four_mem {AtomType Ax} _.

Lemma with_henkin_instantiate_unary :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (eq_dec : atom_decidable_equality AtomType)
         (Schema : formula AtomType -> formula AtomType) a,
    (forall sigma x,
      substitute sigma (Schema x) = Schema (substitute sigma x)) ->
    Ax (Schema (Atom a)) ->
    forall p, with_henkin_proves Ax (Schema p).
Proof.
  intros AtomType Ax eq_dec Schema a Hschema Hmem p.
  pose proof
    (@WH_axm AtomType Ax (Schema (Atom a))
      (with_re_single_substitution eq_dec a p) Hmem) as Hproof.
  rewrite Hschema in Hproof; simpl in Hproof.
  rewrite with_re_single_substitution_at in Hproof.
  exact Hproof.
Qed.

Lemma with_henkin_instantiate_binary :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (eq_dec : atom_decidable_equality AtomType)
         (Schema : formula AtomType -> formula AtomType -> formula AtomType)
         a b,
    a <> b ->
    (forall sigma x y,
      substitute sigma (Schema x y) =
      Schema (substitute sigma x) (substitute sigma y)) ->
    Ax (Schema (Atom a) (Atom b)) ->
    forall p q, with_henkin_proves Ax (Schema p q).
Proof.
  intros AtomType Ax eq_dec Schema a b Hab Hschema Hmem p q.
  pose proof
    (@WH_axm AtomType Ax (Schema (Atom a) (Atom b))
      (with_re_double_substitution eq_dec a b p q) Hmem) as Hproof.
  rewrite Hschema in Hproof; simpl in Hproof.
  rewrite with_re_double_substitution_left in Hproof.
  rewrite with_re_double_substitution_right in Hproof by exact Hab.
  exact Hproof.
Qed.

(** The two source capability adapters. *)

Lemma with_henkin_has_K :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType),
    atom_decidable_equality AtomType ->
    raw_axioms_has_K Ax ->
    has_K (@with_henkin_proves AtomType Ax).
Proof.
  intros AtomType Ax eq_dec Hraw; constructor; intros p q.
  eapply (@with_henkin_instantiate_binary AtomType Ax eq_dec
    (@K AtomType) (raw_K_p Hraw) (raw_K_q Hraw)).
  - exact (raw_K_ne Hraw).
  - reflexivity.
  - exact (raw_K_mem Hraw).
Qed.

Lemma with_henkin_has_Four :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType),
    atom_decidable_equality AtomType ->
    raw_axioms_has_Four Ax ->
    has_Four (@with_henkin_proves AtomType Ax).
Proof.
  intros AtomType Ax eq_dec Hraw; constructor; intro p.
  eapply (@with_henkin_instantiate_unary AtomType Ax eq_dec
    (@Four AtomType) (raw_Four_p Hraw)).
  - reflexivity.
  - exact (raw_Four_mem Hraw).
Qed.

(** * Constructive support for definitional diamond duality *)

Lemma with_henkin_identity :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (p : formula AtomType),
    with_henkin_proves Ax (Imp p p).
Proof.
  intros AtomType Ax p.
  eapply WH_mp.
  - eapply WH_mp.
    + exact (WH_imply_S p (Imp p p) p).
    + exact (WH_imply_K p (Imp p p)).
  - exact (WH_imply_K p p).
Qed.

Lemma with_henkin_imply_intro :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (p q : formula AtomType),
    with_henkin_proves Ax q ->
    with_henkin_proves Ax (Imp p q).
Proof.
  intros AtomType Ax p q Hq.
  eapply WH_mp; [exact (WH_imply_K q p) | exact Hq].
Qed.

Lemma with_henkin_under_mp :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (a p q : formula AtomType),
    with_henkin_proves Ax (Imp a (Imp p q)) ->
    with_henkin_proves Ax (Imp a p) ->
    with_henkin_proves Ax (Imp a q).
Proof.
  intros AtomType Ax a p q Hpq Hp.
  eapply WH_mp.
  - eapply WH_mp; [exact (WH_imply_S a p q) | exact Hpq].
  - exact Hp.
Qed.

Lemma with_henkin_and_intro :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (p q : formula AtomType),
    with_henkin_proves Ax p ->
    with_henkin_proves Ax q ->
    with_henkin_proves Ax (And p q).
Proof.
  intros AtomType Ax p q Hp Hq.
  unfold And, Neg.
  set (a := Imp p (Imp q Bottom)).
  pose proof
    (@with_henkin_imply_intro AtomType Ax a q Hq) as Haq.
  pose proof
    (@with_henkin_imply_intro AtomType Ax a p Hp) as Hap.
  pose proof (@with_henkin_identity AtomType Ax a) as Haa.
  change (with_henkin_proves Ax
    (Imp a (Imp p (Imp q Bottom)))) in Haa.
  pose proof
    (@with_henkin_under_mp AtomType Ax a p (Imp q Bottom) Haa Hap)
    as Hanq.
  exact (@with_henkin_under_mp AtomType Ax a q Bottom Hanq Haq).
Qed.

Lemma with_henkin_iff_refl :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (p : formula AtomType),
    with_henkin_proves Ax (Iff p p).
Proof.
  intros AtomType Ax p; unfold Iff.
  apply with_henkin_and_intro; apply with_henkin_identity.
Qed.

Lemma with_henkin_has_DiaDuality :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType),
    has_DiaDuality (@with_henkin_proves AtomType Ax).
Proof.
  intros AtomType Ax; constructor; intro p.
  unfold DiaDuality, Dia.
  apply with_henkin_iff_refl.
Qed.

(** * The exact two-member nat-atom K/Four system *)

Definition with_henkin_K4_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = Four (Atom 0).

Definition with_henkin_K4_axioms_has_K :
    raw_axioms_has_K with_henkin_K4_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

Definition with_henkin_K4_axioms_has_Four :
    raw_axioms_has_Four with_henkin_K4_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; reflexivity.
Defined.

Definition with_henkin_K4 : modal_logic_set nat :=
  @with_henkin_proves nat with_henkin_K4_axioms.

(** Exact local counterpart of Foundation's [Entailment.K4Henkin].
    Substitution is deliberately separate, matching the source class rather
    than the stronger logic-level normality interface. *)
Record structural_k4_henkin_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  structural_k4_henkin_lukasiewicz : lukasiewicz_entailment L;
  structural_k4_henkin_K : has_K L;
  structural_k4_henkin_dia_duality : has_DiaDuality L;
  structural_k4_henkin_necessitation : necessitation L;
  structural_k4_henkin_Four : has_Four L;
  structural_k4_henkin_rule : henkin_rule L
}.

Lemma with_henkin_K4_entailment :
  structural_k4_henkin_entailment with_henkin_K4.
Proof.
  constructor.
  - apply with_henkin_lukasiewicz.
  - exact (with_henkin_has_K Nat.eq_dec with_henkin_K4_axioms_has_K).
  - apply with_henkin_has_DiaDuality.
  - apply with_henkin_necessitation.
  - exact
      (with_henkin_has_Four Nat.eq_dec
        with_henkin_K4_axioms_has_Four).
  - apply with_henkin_henkin_rule.
Qed.
