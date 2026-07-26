(**
  Finite connected completeness for GL.3.

  This module ports the active mathematical surface of Foundation's pinned
  [Modal/Kripke/Logic/GLPoint3.lean].  The completeness proof follows the
  source's selective canonical-model argument.  Starting from a canonical
  counterexample, it retains one root together with the unique terminal
  successor associated to every relevant failed box.  WeakPoint3 makes the
  canonical frame piecewise connected, hence these successors are linearly
  ordered; Loeb's axiom supplies their existence.  The resulting restricted
  model is finite, transitive, irreflexive, connected, and has a subformula
  truth lemma.

  [CanonicalGL]'s mini-canonical construction is intentionally not reused as
  a world type: it is specialized to [schema_L].  Its finite GL soundness and
  derived Loeb laws are reused below.  The named GL.3 calculus currently
  lives in [Boxdot], so this module also supplies the checked inhabitant of
  that file's finite-completeness interface without creating an import cycle.
*)

From Stdlib Require Import Lists.List.
From Stdlib Require Import
  Logic.Classical_Prop Logic.ClassicalDescription Logic.ProofIrrelevance.
From FoundationModal Require Import
  Syntax Axioms HilbertK Kripke HilbertKSoundness Filtration Correspondence
  CorrespondenceExtensions WeakCorrespondence Loeb FrameProperties
  FrameTransformations NormalHilbert LogicInfrastructure CanonicalExtensions
  FiniteMaximalContext GLGrzDerivations CanonicalGL Root CanonicalDB5
  CanonicalCombinations Boxdot
  CanonicalPoint2 CanonicalPoint3.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Calculus support and exact finite frame classes *)

Lemma schema_WeakPoint3_substitution_closed :
  schema_substitution_closed schema_WeakPoint3.
Proof.
  intros A B sigma p [q [r ->]].
  exists (substitute sigma q), (substitute sigma r). reflexivity.
Qed.

Lemma GLPoint3_schema_substitution_closed :
  schema_substitution_closed GLPoint3_schema.
Proof.
  apply schema_union_substitution_closed.
  - exact schema_L_substitution_closed.
  - exact schema_WeakPoint3_substitution_closed.
Qed.

Definition GLPoint3_normal_logic : normal_logic (@GLPoint3_proves nat) :=
  @normal_proves_logic_is_normal
    GLPoint3_schema GLPoint3_schema_substitution_closed.

Definition GLPoint3_classical_logic :
    classical_logic (@GLPoint3_proves nat) :=
  quasi_classical (normal_quasi GLPoint3_normal_logic).

Lemma K_weaker_than_GLPoint3 :
  forall (AtomType : Type) (p : formula AtomType),
    K_normal_proves p -> GLPoint3_proves p.
Proof. intros AtomType p Hp. now apply K_weaker_than_normal. Qed.

Lemma GL_weaker_than_GLPoint3 :
  forall (AtomType : Type) (p : formula AtomType),
    GL_proves p -> GLPoint3_proves p.
Proof.
  intros AtomType p Hp. eapply normal_proves_weaken; [|exact Hp].
  intros A q Hq. now left.
Qed.

Lemma GLPoint3_proves_L :
  forall p : formula nat, GLPoint3_proves (L p).
Proof. intro p. apply GL_weaker_than_GLPoint3, GL_proves_L. Qed.

Lemma GLPoint3_proves_Four :
  forall p : formula nat, GLPoint3_proves (Four p).
Proof. intro p. apply GL_weaker_than_GLPoint3, GL_proves_Four. Qed.

Definition GLPoint3_finite_frame_class (F : frame) : Prop :=
  finite_frame F /\ frame_transitive F /\ frame_irreflexive F /\
  frame_connected F.

Definition GLPoint3_finite_piecewise_frame_class (F : frame) : Prop :=
  finite_frame F /\ frame_transitive F /\ frame_irreflexive F /\
  frame_piecewise_connected F.

Lemma frame_connected_piecewise_connected :
  forall F, frame_connected F -> frame_piecewise_connected F.
Proof. intros F HC x y z _ _. exact (HC y z). Qed.

Theorem GLPoint3_proves_sound_on_transitive_cwf_piecewise_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    frame_transitive F -> frame_converse_well_founded F ->
    frame_piecewise_connected F ->
    GLPoint3_proves p -> valid F p.
Proof.
  intros AtomType F p HT HCWF HPC Hp.
  eapply normal_proves_sound_on_frame; [|exact Hp].
  apply schema_union_valid_on_frame.
  - now apply schema_L_valid_on_GL_frame.
  - now apply schema_WeakPoint3_valid_on_piecewise_connected.
Qed.

Theorem GLPoint3_finite_sound :
  forall p : formula nat,
    GLPoint3_proves p ->
    normal_valid_on_class GLPoint3_finite_frame_class p.
Proof.
  intros p Hp F [Hfinite [Htrans [Hirr Hconnected]]].
  eapply GLPoint3_proves_sound_on_transitive_cwf_piecewise_frame;
    [exact Htrans | | | exact Hp].
  - now apply finite_transitive_irreflexive_cwf.
  - now apply frame_connected_piecewise_connected.
Qed.

Theorem GLPoint3_finite_piecewise_sound :
  forall p : formula nat,
    GLPoint3_proves p ->
    normal_valid_on_class GLPoint3_finite_piecewise_frame_class p.
Proof.
  intros p Hp F [Hfinite [Htrans [Hirr Hpiece]]].
  eapply GLPoint3_proves_sound_on_transitive_cwf_piecewise_frame;
    [exact Htrans | | exact Hpiece | exact Hp].
  now apply finite_transitive_irreflexive_cwf.
Qed.

Theorem GLPoint3_is_consistent :
  forall AtomType, ~ @GLPoint3_proves AtomType Bottom.
Proof.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := GLPoint3_schema) (F := irreflexive_singleton_frame)).
  - now exists tt.
  - apply schema_union_valid_on_frame.
    + apply schema_L_valid_on_GL_frame.
      * exact irreflexive_singleton_transitive.
      * exact irreflexive_singleton_cwf.
    + apply schema_WeakPoint3_valid_on_piecewise_connected.
      intros [] [] [] H; contradiction.
Qed.

(** Loeb's axiom yields a terminal counterexample to every failed box. *)
Lemma GL_proves_terminal_successor_formula :
  forall p : formula nat,
    GL_proves
      (Imp (Neg (Box p)) (Dia (And (Box p) (Neg p)))).
Proof.
  intro p.
  assert (Hstep :
    GL_proves
      (Imp (Neg (And (Box p) (Neg p))) (Imp (Box p) p))).
  {
    apply (logic_classical_tautology GL_classical_logic).
    intro rho. unfold And, Neg; simpl; tauto.
  }
  assert (Hboxed :
    GL_proves
      (Imp (Box (Neg (And (Box p) (Neg p))))
           (Box (Imp (Box p) p)))).
  { exact (logic_box_regularity GL_normal_logic Hstep). }
  assert (Hterminal :
    GL_proves
      (Imp (Box (Neg (And (Box p) (Neg p)))) (Box p))).
  { exact (logic_imp_trans GL_classical_logic Hboxed (GL_proves_L p)). }
  assert (Hcontra :
    GL_proves
      (Imp
        (Imp (Box (Neg (And (Box p) (Neg p)))) (Box p))
        (Imp (Neg (Box p)) (Dia (And (Box p) (Neg p)))))).
  {
    apply (logic_classical_tautology GL_classical_logic).
    intro rho. unfold Dia, And, Neg; simpl; tauto.
  }
  exact (Np_mp Hcontra Hterminal).
Qed.

Corollary GLPoint3_proves_terminal_successor_formula :
  forall p : formula nat,
    GLPoint3_proves
      (Imp (Neg (Box p)) (Dia (And (Box p) (Neg p)))).
Proof.
  intro p. apply GL_weaker_than_GLPoint3.
  apply GL_proves_terminal_successor_formula.
Qed.

(** * The full canonical frame and unique terminal successors *)

Definition glpoint3_canonical_frame : frame :=
  normal_canonical_frame GLPoint3_schema.

Definition glpoint3_canonical_valuation :
    valuation nat glpoint3_canonical_frame :=
  @normal_canonical_valuation GLPoint3_schema.

Lemma glpoint3_canonical_transitive :
  frame_transitive glpoint3_canonical_frame.
Proof.
  intros X Y Z RXY RYZ p HboxpX.
  apply RYZ with (p := p). apply RXY with (p := Box p).
  apply normal_mct_derivable_mem. eapply ND_mp.
  - apply ND_theorem. apply GLPoint3_proves_Four.
  - apply ND_assumption. exact HboxpX.
Qed.

Lemma glpoint3_canonical_piecewise_connected :
  frame_piecewise_connected glpoint3_canonical_frame.
Proof.
  unfold glpoint3_canonical_frame.
  apply normal_canonical_piecewise_connected_of_schema_WeakPoint3.
  intros A p Hp. right. exact Hp.
Qed.

Definition glpoint3_terminal_spec
    (v : World glpoint3_canonical_frame) (p : formula nat)
    (u : World glpoint3_canonical_frame) : Prop :=
  Rel glpoint3_canonical_frame v u /\
  normal_mct_mem u (Box p) /\ normal_mct_mem u (Neg p).

Arguments glpoint3_terminal_spec v p u : clear implicits.

Theorem glpoint3_terminal_successor_unique :
  forall (v : World glpoint3_canonical_frame) p,
    normal_mct_mem v (Neg (Box p)) ->
    exists! u : World glpoint3_canonical_frame,
      glpoint3_terminal_spec v p u.
Proof.
  intros v p Hnegbox.
  assert (Hformula : normal_mct_mem v
    (Imp (Neg (Box p)) (Dia (And (Box p) (Neg p))))).
  {
    apply normal_mct_derivable_mem. apply ND_theorem.
    apply GLPoint3_proves_terminal_successor_formula.
  }
  pose proof (proj1 (@normal_canonical_truth_lemma GLPoint3_schema
    (Imp (Neg (Box p)) (Dia (And (Box p) (Neg p)))) v) Hformula)
    as Hsemantic.
  pose proof (proj1 (@normal_canonical_truth_lemma GLPoint3_schema
    (Neg (Box p)) v) Hnegbox) as Hsemantic_neg.
  destruct (@satisfies_dia_elim nat glpoint3_canonical_frame
    glpoint3_canonical_valuation v (And (Box p) (Neg p))
    (Hsemantic Hsemantic_neg))
    as [u [Rvu Hu]].
  destruct (proj1 (@satisfies_and nat glpoint3_canonical_frame
    glpoint3_canonical_valuation u (Box p) (Neg p)) Hu)
    as [Hubox Huneg].
  assert (Hubox_mem : normal_mct_mem u (Box p)).
  { now apply (proj2 (@normal_canonical_truth_lemma GLPoint3_schema
      (Box p) u)). }
  assert (Huneg_mem : normal_mct_mem u (Neg p)).
  { now apply (proj2 (@normal_canonical_truth_lemma GLPoint3_schema
      (Neg p) u)). }
  exists u; split.
  - exact (conj Rvu (conj Hubox_mem Huneg_mem)).
  - intros y [Rvy [Hybox Hyneg]].
    pose proof glpoint3_canonical_piecewise_connected as Hpiece.
    unfold frame_piecewise_connected in Hpiece.
    destruct (Hpiece v u y Rvu Rvy)
      as [Ruy | [Heq | Ryu]].
    + exfalso. exact (@normal_mct_not_both GLPoint3_schema y p
        (Ruy p Hubox_mem) Hyneg).
    + exact Heq.
    + exfalso. exact (@normal_mct_not_both GLPoint3_schema u p
        (Ryu p Hybox) Huneg_mem).
Qed.

(** * The selective finite canonical model *)

Definition glpoint3_filtered_member
    (v : World glpoint3_canonical_frame) (target : formula nat)
    (x : World glpoint3_canonical_frame) : Prop :=
  x = v \/
  (Rel glpoint3_canonical_frame v x /\
   exists p,
     In (Box p) (subformulas target) /\
     normal_mct_mem v (Neg (Box p)) /\
     normal_mct_mem x (Box p) /\ normal_mct_mem x (Neg p)).

Arguments glpoint3_filtered_member v target x : clear implicits.

Definition glpoint3_filtered_frame
    (v : World glpoint3_canonical_frame) (target : formula nat) : frame :=
  {| World := {x : World glpoint3_canonical_frame |
        glpoint3_filtered_member v target x};
     Rel := fun x y =>
       Rel glpoint3_canonical_frame (proj1_sig x) (proj1_sig y) |}.

Arguments glpoint3_filtered_frame v target : clear implicits.

Definition glpoint3_filtered_valuation
    (v : World glpoint3_canonical_frame) (target : formula nat) :
    valuation nat (glpoint3_filtered_frame v target) :=
  fun a x => normal_mct_mem (proj1_sig x) (Atom a).

Arguments glpoint3_filtered_valuation v target : clear implicits.

Definition glpoint3_filtered_root
    (v : World glpoint3_canonical_frame) (target : formula nat) :
    World (glpoint3_filtered_frame v target) :=
  exist (glpoint3_filtered_member v target) v (or_introl eq_refl).

Arguments glpoint3_filtered_root v target : clear implicits.

Lemma glpoint3_filtered_world_eq :
  forall v target (x y : World (glpoint3_filtered_frame v target)),
    proj1_sig x = proj1_sig y -> x = y.
Proof.
  intros v target [x Hx] [y Hy] Hxy. simpl in Hxy. subst y.
  f_equal. apply proof_irrelevance.
Qed.

Lemma glpoint3_filtered_transitive :
  forall v target, frame_transitive (glpoint3_filtered_frame v target).
Proof.
  intros v target x y z Rxy Ryz.
  pose proof glpoint3_canonical_transitive as Htrans.
  unfold frame_transitive in Htrans.
  exact (Htrans (proj1_sig x) (proj1_sig y) (proj1_sig z) Rxy Ryz).
Qed.

Lemma glpoint3_filtered_irreflexive :
  forall v target,
    normal_mct_mem v (Box target) -> normal_mct_mem v (Neg target) ->
    frame_irreflexive (glpoint3_filtered_frame v target).
Proof.
  intros v target Hvbox Hvneg [x Hx] Rxx. simpl in Rxx.
  destruct Hx as [-> | [_ [p [_ [_ [Hpbox Hpneg]]]]]].
  - exact (@normal_mct_not_both GLPoint3_schema v target
      (Rxx target Hvbox) Hvneg).
  - exact (@normal_mct_not_both GLPoint3_schema x p
      (Rxx p Hpbox) Hpneg).
Qed.

Lemma glpoint3_filtered_connected :
  forall v target, frame_connected (glpoint3_filtered_frame v target).
Proof.
  intros v target [x Hx] [y Hy]. simpl.
  destruct Hx as [Hx | [Rvx Hx]];
    destruct Hy as [Hy | [Rvy Hy]].
  - subst x; subst y. right; left.
    apply glpoint3_filtered_world_eq. reflexivity.
  - subst x. now left.
  - subst y. now right; right.
  - pose proof glpoint3_canonical_piecewise_connected as Hpiece.
    unfold frame_piecewise_connected in Hpiece.
    destruct (Hpiece v x y Rvx Rvy) as [Rxy | [Hxy | Ryx]].
    + now left.
    + right; left. apply glpoint3_filtered_world_eq. exact Hxy.
    + now right; right.
Qed.

(** Every non-root filtered world is the unique terminal successor indexed
    by one of the finitely many boxed subformulas. *)
Lemma glpoint3_filtered_successor_cover_list :
  forall v target (items : list (formula nat)),
    list_subset items (subformulas target) ->
    exists cover : list (World (glpoint3_filtered_frame v target)),
      forall (x : World (glpoint3_filtered_frame v target)) p,
        In (Box p) items ->
        normal_mct_mem v (Neg (Box p)) ->
        glpoint3_terminal_spec v p (proj1_sig x) ->
        In x cover.
Proof.
  intros v target items. induction items as [|item items IH]; intro Hsubset.
  - exists []. intros x p Hin. contradiction.
  - assert (Htail : list_subset items (subformulas target)).
    { intros q Hq. apply Hsubset. now right. }
    destruct (IH Htail) as [cover Hcover].
    destruct item as [a | | q r | q].
    + exists cover. intros x p [Heq | Hin] Hneg Hspec.
      * discriminate.
      * eapply Hcover; eauto.
    + exists cover. intros x p [Heq | Hin] Hneg Hspec.
      * discriminate.
      * eapply Hcover; eauto.
    + exists cover. intros x p [Heq | Hin] Hneg Hspec.
      * discriminate.
      * eapply Hcover; eauto.
    + destruct (classic (normal_mct_mem v (Neg (Box q))))
        as [Hnegq | Hnotnegq].
      * destruct (glpoint3_terminal_successor_unique Hnegq)
          as [u [Huspec Huunique]].
        assert (Huitem : In (Box q) (subformulas target)).
        { apply Hsubset. now left. }
        assert (Humember : glpoint3_filtered_member v target u).
        {
          right. split; [exact (proj1 Huspec) |].
          exists q. split; [exact Huitem |].
          split; [exact Hnegq |]. exact (proj2 Huspec).
        }
        set (U := exist (glpoint3_filtered_member v target) u Humember).
        exists (U :: cover).
        intros x p Hinbox Hneg Hspec. destruct Hinbox as [Heq | Hin].
        { inversion Heq; subst p. left.
          apply glpoint3_filtered_world_eq. simpl.
          exact (Huunique (proj1_sig x) Hspec). }
        { right. eapply Hcover; eauto. }
      * exists cover. intros x p Hinbox Hneg Hspec.
        destruct Hinbox as [Heq | Hin].
        { inversion Heq; subst p. contradiction. }
        { eapply Hcover; eauto. }
Qed.

Lemma glpoint3_filtered_finite :
  forall v target, finite_frame (glpoint3_filtered_frame v target).
Proof.
  intros v target.
  destruct (@glpoint3_filtered_successor_cover_list v target
    (subformulas target)) as [cover Hcover].
  - intros p Hp. exact Hp.
  - exists (glpoint3_filtered_root v target :: cover).
    intros [x Hx]. destruct Hx as [Hx | [Rvx [p
      [Hp [Hneg [Hpbox Hpneg]]]]]].
    + left. apply glpoint3_filtered_world_eq. simpl. exact (eq_sym Hx).
    + right. eapply Hcover with (p := p).
      * exact Hp.
      * exact Hneg.
      * exact (conj Rvx (conj Hpbox Hpneg)).
Qed.

(** * Truth in the selective model *)

Theorem glpoint3_filtered_truth_lemma :
  forall v target p,
    In p (subformulas target) ->
    forall x : World (glpoint3_filtered_frame v target),
      satisfies (glpoint3_filtered_frame v target)
        (glpoint3_filtered_valuation v target) x p <->
      normal_mct_mem (proj1_sig x) p.
Proof.
  intros v target p. revert v target.
  induction p as [a | | p IHp q IHq | p IHp];
    intros v target Hsub x; simpl.
  - reflexivity.
  - split.
    + contradiction.
    + intro Hbottom.
      exact (@normal_mct_bottom_absent GLPoint3_schema
        (proj1_sig x) Hbottom).
  - assert (Hp : In p (subformulas target)).
    { eapply subformulas_trans; [exact Hsub |].
      apply subformulas_imp_left. apply subformulas_self. }
    assert (Hq : In q (subformulas target)).
    { eapply subformulas_trans; [exact Hsub |].
      apply subformulas_imp_right. apply subformulas_self. }
    specialize (IHp v target Hp x).
    specialize (IHq v target Hq x).
    rewrite IHp, IHq. symmetry. apply normal_mct_imp_iff.
  - assert (Hp : In p (subformulas target)).
    { eapply subformulas_trans; [exact Hsub |].
      apply subformulas_box. apply subformulas_self. }
    split.
    + intro Hsemantic.
      destruct (classic (normal_mct_mem (proj1_sig x) (Box p)))
        as [Hbox | Hnotbox]; [exact Hbox |].
      exfalso.
      assert (Hnegbox_x : normal_mct_mem (proj1_sig x) (Neg (Box p))).
      { now apply (proj2 (@normal_mct_neg_iff GLPoint3_schema
          (proj1_sig x) (Box p))). }
      assert (Hnegbox_v : normal_mct_mem v (Neg (Box p))).
      {
        apply (proj2 (@normal_mct_neg_iff GLPoint3_schema v (Box p))).
        intro Hboxv. apply Hnotbox.
        destruct x as [x Hmember]. simpl in *.
        destruct Hmember as [-> | [Rvx _]].
        - exact Hboxv.
        - apply Rvx with (p := Box p).
          apply normal_mct_derivable_mem. eapply ND_mp.
          + apply ND_theorem. apply GLPoint3_proves_Four.
          + apply ND_assumption. exact Hboxv.
      }
      destruct (glpoint3_terminal_successor_unique Hnegbox_v)
        as [y [[Rvy [Hybox Hyneg]] _]].
      assert (Hymember : glpoint3_filtered_member v target y).
      {
        right. split; [exact Rvy |]. exists p.
        split; [exact Hsub |]. split; [exact Hnegbox_v |].
        now split.
      }
      set (Y := exist (glpoint3_filtered_member v target) y Hymember).
      assert (Rxy : Rel (glpoint3_filtered_frame v target) x Y).
      {
        unfold Y. simpl.
        destruct x as [x Hmember]. simpl in *.
        destruct Hmember as [-> | [Rvx _]].
        - exact Rvy.
        - pose proof glpoint3_canonical_piecewise_connected as Hpiece.
          unfold frame_piecewise_connected in Hpiece.
          destruct (Hpiece v x y Rvx Rvy) as [Rxy | [Hxy | Ryx]].
          + exact Rxy.
          + subst y. contradiction.
          + exfalso. apply Hnotbox.
            apply Ryx with (p := Box p).
            apply normal_mct_derivable_mem. eapply ND_mp.
            * apply ND_theorem. apply GLPoint3_proves_Four.
            * apply ND_assumption. exact Hybox.
      }
      assert (Hyp : normal_mct_mem y p).
      {
        apply (proj1 (IHp v target Hp Y)).
        exact (Hsemantic Y Rxy).
      }
      exact (@normal_mct_not_both GLPoint3_schema y p Hyp Hyneg).
    + intros Hbox y Rxy.
      apply (proj2 (IHp v target Hp y)).
      exact (Rxy p Hbox).
Qed.

(** * Finite countermodels and completeness *)

Theorem GLPoint3_unprovable_exists_finite_connected_countermodel :
  forall p : formula nat,
    ~ GLPoint3_proves p ->
    exists (F : frame) (V : valuation nat F) (r : World F),
      finite_frame F /\ frame_transitive F /\ frame_irreflexive F /\
      frame_connected F /\ ~ satisfies F V r p.
Proof.
  intros p Hunprovable.
  destruct (@normal_canonical_countermodel GLPoint3_schema
    (@GLPoint3_is_consistent nat) p Hunprovable) as [u Hcounter].
  assert (Hnegu : normal_mct_mem u (Neg p)).
  {
    apply (proj2 (@normal_mct_neg_iff GLPoint3_schema u p)).
    intro Hpu. apply Hcounter.
    now apply (proj1 (@normal_canonical_truth_lemma GLPoint3_schema p u)).
  }
  assert (Hv : exists v : World glpoint3_canonical_frame,
      normal_mct_mem v (Box p) /\ normal_mct_mem v (Neg p)).
  {
    destruct (classic (normal_mct_mem u (Box p))) as [Hubox | Hnotbox].
    - exists u. now split.
    - assert (Hunegbox : normal_mct_mem u (Neg (Box p))).
      { now apply (proj2 (@normal_mct_neg_iff GLPoint3_schema u (Box p))). }
      destruct (glpoint3_terminal_successor_unique Hunegbox)
        as [v [[_ [Hvbox Hvneg]] _]].
      exists v. now split.
  }
  destruct Hv as [v [Hvbox Hvneg]].
  exists (glpoint3_filtered_frame v p),
    (glpoint3_filtered_valuation v p),
    (glpoint3_filtered_root v p).
  split.
  - apply glpoint3_filtered_finite.
  - split.
    + apply glpoint3_filtered_transitive.
    + split.
      * now apply glpoint3_filtered_irreflexive.
      * split.
        -- apply glpoint3_filtered_connected.
        -- intro Hsat.
           assert (Hmem : normal_mct_mem v p).
           { apply (proj1 (@glpoint3_filtered_truth_lemma v p p
               (subformulas_self p) (glpoint3_filtered_root v p))).
             exact Hsat. }
           exact (@normal_mct_not_both GLPoint3_schema v p Hmem Hvneg).
Qed.

Theorem GLPoint3_finite_complete :
  forall p : formula nat,
    normal_valid_on_class GLPoint3_finite_frame_class p ->
    GLPoint3_proves p.
Proof.
  intros p Hvalid. apply NNPP. intro Hunprovable.
  destruct (GLPoint3_unprovable_exists_finite_connected_countermodel
    Hunprovable) as [F [V [r [Hfinite [Htrans [Hirr
      [Hconnected Hcounter]]]]]]].
  apply Hcounter. apply (Hvalid F).
  unfold GLPoint3_finite_frame_class.
  repeat split; assumption.
Qed.

Theorem GLPoint3_finite_sound_complete :
  forall p : formula nat,
    GLPoint3_proves p <->
    normal_valid_on_class GLPoint3_finite_frame_class p.
Proof.
  intro p; split.
  - apply GLPoint3_finite_sound.
  - apply GLPoint3_finite_complete.
Qed.

Theorem GLPoint3_finite_piecewise_complete :
  forall p : formula nat,
    normal_valid_on_class GLPoint3_finite_piecewise_frame_class p ->
    GLPoint3_proves p.
Proof.
  intros p Hvalid. apply GLPoint3_finite_complete.
  intros F [Hfinite [Htrans [Hirr Hconnected]]]. apply Hvalid.
  unfold GLPoint3_finite_piecewise_frame_class.
  repeat split; try assumption.
  now apply frame_connected_piecewise_connected.
Qed.

Theorem GLPoint3_finite_piecewise_sound_complete :
  forall p : formula nat,
    GLPoint3_proves p <->
    normal_valid_on_class GLPoint3_finite_piecewise_frame_class p.
Proof.
  intro p; split.
  - apply GLPoint3_finite_piecewise_sound.
  - apply GLPoint3_finite_piecewise_complete.
Qed.

(** The completeness proposition retained by [Boxdot] now has a checked
    inhabitant.  Its frame class uses converse well-foundedness rather than
    irreflexivity; finiteness and transitivity make the presentations
    equivalent. *)
Theorem boxdot_GLPoint3_finite_complete_checked :
  boxdot_GLPoint3_finite_complete.
Proof.
  intros p Hvalid. apply GLPoint3_finite_piecewise_complete.
  intros F [Hfinite [Htrans [Hirr Hpiece]]]. apply Hvalid.
  unfold boxdot_finite_GLPoint3_frame, boxdot_finite_GL_frame,
    boxdot_GL_frame.
  split.
  - split; [exact Hfinite |]. split; [exact Htrans |].
    now apply finite_transitive_irreflexive_cwf.
  - exact Hpiece.
Qed.

(** Low-risk unconditional specializations of Boxdot's existing gated API. *)
Corollary GLPoint3_proves_boxdot_Grz_axiom_unconditional :
  forall p : formula nat,
    GLPoint3_proves (boxdot_translate (Grz p)).
Proof.
  apply GLPoint3_proves_boxdot_Grz_axiom.
  exact boxdot_GLPoint3_finite_complete_checked.
Qed.

Corollary GLPoint3_proves_boxdot_Point3_axiom_unconditional :
  forall p q : formula nat,
    GLPoint3_proves (boxdot_translate (Point3 p q)).
Proof.
  apply GLPoint3_proves_boxdot_Point3_axiom.
  exact boxdot_GLPoint3_finite_complete_checked.
Qed.

Theorem GrzPoint3_proves_to_GLPoint3_boxdot_unconditional :
  forall p : formula nat,
    GrzPoint3_proves p -> GLPoint3_proves (boxdot_translate p).
Proof.
  apply GrzPoint3_proves_to_GLPoint3_boxdot.
  exact boxdot_GLPoint3_finite_complete_checked.
Qed.

Theorem GLPoint3_boxdot_iff_GrzPoint3_from_Grz_finite_completeness :
  boxdot_GrzPoint3_finite_complete ->
  forall p : formula nat,
    GLPoint3_proves (boxdot_translate p) <-> GrzPoint3_proves p.
Proof.
  intros HGrz p. apply GLPoint3_boxdot_iff_GrzPoint3.
  - exact boxdot_GLPoint3_finite_complete_checked.
  - exact HGrz.
Qed.

(** * The two strict inclusions from the source *)

Definition glpoint3_strict_fork_relation
    (x y : three_world) : Prop :=
  (x = W0 /\ y = W1) \/ (x = W0 /\ y = W2).

Definition glpoint3_strict_fork_frame : frame :=
  {| World := three_world; Rel := glpoint3_strict_fork_relation |}.

Lemma glpoint3_strict_fork_finite :
  finite_frame glpoint3_strict_fork_frame.
Proof. exists [W0; W1; W2]. intros []; simpl; auto. Qed.

Lemma glpoint3_strict_fork_transitive :
  frame_transitive glpoint3_strict_fork_frame.
Proof.
  intros x y z Hxy Hyz.
  destruct Hxy as [[_ ->] | [_ ->]];
    destruct Hyz as [[Hbad _] | [Hbad _]]; discriminate.
Qed.

Lemma glpoint3_strict_fork_irreflexive :
  frame_irreflexive glpoint3_strict_fork_frame.
Proof.
  intros x Hxx. destruct Hxx as [[-> Hbad] | [-> Hbad]]; discriminate.
Qed.

Lemma glpoint3_strict_fork_not_piecewise_connected :
  ~ frame_piecewise_connected glpoint3_strict_fork_frame.
Proof.
  intro HC.
  assert (H01 : Rel glpoint3_strict_fork_frame W0 W1).
  { now left. }
  assert (H02 : Rel glpoint3_strict_fork_frame W0 W2).
  { now right. }
  destruct (HC W0 W1 W2 H01 H02) as [H12 | [Heq | H21]].
  - destruct H12 as [[Hbad _] | [Hbad _]]; discriminate.
  - discriminate.
  - destruct H21 as [[Hbad _] | [Hbad _]]; discriminate.
Qed.

Theorem GL_strictly_weaker_GLPoint3 :
  normal_strictly_weaker GL_proves GLPoint3_proves.
Proof.
  split.
  - apply GL_weaker_than_GLPoint3.
  - exists (WeakPoint3 (Atom 0) (Atom 1)); split.
    + apply Np_extra. right. exists (Atom 0), (Atom 1). reflexivity.
    + intro HGL.
      pose proof (@GL_finite_sound _ HGL glpoint3_strict_fork_frame
        (conj glpoint3_strict_fork_finite
          (conj glpoint3_strict_fork_transitive
            glpoint3_strict_fork_irreflexive))) as Hvalid.
      apply glpoint3_strict_fork_not_piecewise_connected.
      now apply (proj1 (valid_WeakPoint3_atoms_iff_piecewise_connected
        glpoint3_strict_fork_frame)).
Qed.

Lemma K4Point3_weaker_than_GLPoint3 :
  forall p : formula nat, K4Point3_proves p -> GLPoint3_proves p.
Proof.
  intros p Hp. induction Hp.
  - apply Np_imply_K.
  - apply Np_imply_S.
  - apply Np_elim_contra.
  - apply Np_modal_K.
  - destruct H as [Hfour | Hweak].
    + destruct Hfour as [q ->]. apply GLPoint3_proves_Four.
    + apply Np_extra. right. exact Hweak.
  - eapply Np_mp; eauto.
  - now apply Np_nec.
Qed.

Lemma combo_two_preorder_piecewise_connected_GLPoint3 :
  frame_piecewise_connected combo_two_preorder_frame.
Proof.
  intros [] [] [] _ _; simpl; tauto.
Qed.

Theorem K4Point3_strictly_weaker_GLPoint3 :
  normal_strictly_weaker K4Point3_proves GLPoint3_proves.
Proof.
  split.
  - exact K4Point3_weaker_than_GLPoint3.
  - exists (L (Atom 0)); split.
    + apply GLPoint3_proves_L.
    + intro HK4Point3.
      pose proof (K4Point3_proves_sound_on_frame
        combo_two_preorder_transitive
        combo_two_preorder_piecewise_connected_GLPoint3 HK4Point3)
        as Hvalid.
      pose proof (cwf_of_valid_Loeb_atom Hvalid) as HCWF.
      pose proof (converse_well_founded_irreflexive HCWF) as Hirr.
      exact (Hirr DB0 (or_introl eq_refl)).
Qed.
