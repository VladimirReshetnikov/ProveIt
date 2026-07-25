(**
  Further Kripke-frame correspondences for named modal axioms.

  This file ports the semantic, non-canonical content of the pinned
  Foundation modules [AxiomFourN], [AxiomGrz], [AxiomH], [AxiomI],
  [AxiomMcK], [AxiomMk], [AxiomPoint4], and [AxiomVer].  The proofs are
  independent Coq proofs against the local syntax and semantics.

  The classical boundary is explicit.  Eliminating a syntactic diamond,
  or decoding the classical disjunction in axiom I, uses classical
  propositional logic.  The converse-well-foundedness direction for Grz
  additionally uses classical choice to select an infinite ascending chain
  from a set with no maximal element.  No canonical-model theorem is stated
  here; those results belong to the Hilbert/canonical layer.  In particular,
  Foundation's canonical tail for Mk contains an upstream [sorry].
*)

From Stdlib Require Import Arith.PeanoNat Lia.
From Stdlib Require Import Logic.Classical_Prop Logic.ClassicalChoice.
From FoundationModal Require Import
  Syntax Axioms Kripke Correspondence Loeb FrameProperties.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Iterated Four / weak transitivity *)

Definition frame_weakly_transitive (F : frame) (n : nat) : Prop :=
  forall x y : World F,
    rel_iter (Rel F) (n + 1) x y -> rel_iter (Rel F) n x y.

Definition four_n_geach (n : nat) : geach_tuple :=
  {| geach_i := 0;
     geach_j := n + 1;
     geach_m := n;
     geach_n := 0 |}.

Theorem geach_convergent_four_n_iff_weakly_transitive :
  forall (F : frame) n,
    geach_convergent F (four_n_geach n) <->
    frame_weakly_transitive F n.
Proof.
  intros F n; split.
  - intros Hg x z Hxz.
    destruct (Hg x x z eq_refl Hxz) as [u [Hxu Hzu]].
    simpl in Hzu. now subst u.
  - intros Hweak x y z Hxy Hxz.
    simpl in Hxy. subst y.
    exists z; split.
    + now apply Hweak.
    + reflexivity.
Qed.

Lemma valid_FourN_of_weakly_transitive :
  forall AtomType (F : frame) n (p : formula AtomType),
    frame_weakly_transitive F n -> valid F (FourN n p).
Proof.
  intros AtomType F n p Hweak.
  change (valid F (Geach (four_n_geach n) p)).
  apply valid_Geach_of_geach_convergent.
  apply (proj2 (geach_convergent_four_n_iff_weakly_transitive F n)).
  exact Hweak.
Qed.

Theorem valid_FourN_atom_iff_weakly_transitive :
  forall (F : frame) n,
    valid F (FourN n (Atom 0)) <-> frame_weakly_transitive F n.
Proof.
  intros F n.
  change (valid F (Geach (four_n_geach n) (Atom 0)) <->
          frame_weakly_transitive F n).
  rewrite valid_Geach_atom_iff_geach_convergent.
  apply geach_convergent_four_n_iff_weakly_transitive.
Qed.

(** * Ver / isolated frames *)

Definition frame_isolated (F : frame) : Prop :=
  forall x y : World F, ~ Rel F x y.

Lemma valid_Ver_of_isolated :
  forall AtomType (F : frame) (p : formula AtomType),
    frame_isolated F -> valid F (Ver p).
Proof.
  intros AtomType F p Hisolated V x y Rxy.
  exfalso. exact (Hisolated x y Rxy).
Qed.

Lemma isolated_of_valid_Ver_atom :
  forall F : frame,
    valid F (Ver (Atom 0)) -> frame_isolated F.
Proof.
  intros F Hvalid x y Rxy.
  pose (V := (fun _ _ => False) : valuation nat F).
  exact (Hvalid V x y Rxy).
Qed.

Theorem valid_Ver_atom_iff_isolated :
  forall F : frame,
    valid F (Ver (Atom 0)) <-> frame_isolated F.
Proof.
  intro F; split.
  - apply isolated_of_valid_Ver_atom.
  - intro H. exact (@valid_Ver_of_isolated nat F (Atom 0) H).
Qed.

(** * Point4 / Sobocinski's condition *)

Definition frame_sobocinski (F : frame) : Prop :=
  forall x y z : World F,
    x <> y -> Rel F x y -> Rel F x z -> Rel F z y.

Lemma sobocinski_piecewise_strongly_connected :
  forall F : frame,
    frame_sobocinski F -> frame_piecewise_strongly_connected F.
Proof.
  intros F Hsob x y z Rxy Rxz.
  destruct (classic (x = y)) as [-> | Hxy].
  - now left.
  - right. now apply (Hsob x y z).
Qed.

Lemma right_euclidean_sobocinski :
  forall F : frame,
    frame_right_euclidean F -> frame_sobocinski F.
Proof.
  intros F Heucl x y z _ Rxy Rxz.
  exact (Heucl x z y Rxz Rxy).
Qed.

Lemma valid_Point4_of_sobocinski :
  forall AtomType (F : frame) (p : formula AtomType),
    frame_sobocinski F -> valid F (Point4 p).
Proof.
  intros AtomType F p Hsob V x Hdia Hpx y Rxy.
  destruct (classic (x = y)) as [-> | Hxy]; [exact Hpx |].
  destruct (satisfies_dia_elim Hdia) as [z [Rxz Hzbox]].
  exact (Hzbox y (Hsob x y z Hxy Rxy Rxz)).
Qed.

Lemma sobocinski_of_valid_Point4_atom :
  forall F : frame,
    valid F (Point4 (Atom 0)) -> frame_sobocinski F.
Proof.
  intros F Hvalid x y z Hxy Rxy Rxz.
  pose (V := (fun _ w => w = x \/ Rel F z w) : valuation nat F).
  assert (Hdia : satisfies F V x (Dia (Box (Atom 0)))).
  {
    apply satisfies_dia_intro. exists z; split; [exact Rxz |].
    intros w Rzw. right. exact Rzw.
  }
  assert (Hpx : satisfies F V x (Atom 0)).
  { left. reflexivity. }
  pose proof (Hvalid V x Hdia Hpx y Rxy) as Hy.
  destruct Hy as [Hyx | Rzy].
  - symmetry in Hyx. contradiction.
  - exact Rzy.
Qed.

Theorem valid_Point4_atom_iff_sobocinski :
  forall F : frame,
    valid F (Point4 (Atom 0)) <-> frame_sobocinski F.
Proof.
  intro F; split.
  - apply sobocinski_of_valid_Point4_atom.
  - intro H. exact (@valid_Point4_of_sobocinski nat F (Atom 0) H).
Qed.

(** * McK / the McKinsey terminal-successor condition *)

Definition frame_mckinsey (F : frame) : Prop :=
  forall x : World F,
    exists y : World F,
      Rel F x y /\ forall z : World F, Rel F y z -> y = z.

Lemma valid_McK_of_mckinsey :
  forall AtomType (F : frame) (p : formula AtomType),
    frame_mckinsey F -> valid F (McK p).
Proof.
  intros AtomType F p Hmck V x Hboxdia.
  destruct (Hmck x) as [y [Rxy Hy]].
  destruct (satisfies_dia_elim (Hboxdia y Rxy))
    as [z [Ryz Hzp]].
  pose proof (Hy z Ryz) as Hyz. subst z.
  apply satisfies_dia_intro. exists y; split; [exact Rxy |].
  intros u Ryu.
  pose proof (Hy u Ryu) as Hyu. now subst u.
Qed.

(** Foundation proves only this semantic direction for McK; its canonical
    result is a separate Hilbert/Lindenbaum theorem. *)

(** * Mk / Makinson's condition *)

Definition frame_makinson (F : frame) : Prop :=
  forall x : World F,
    exists y : World F,
      Rel F x y /\
      Rel F y x /\
      forall z : World F, rel_iter (Rel F) 2 y z -> Rel F x z.

Lemma valid_Mk_of_makinson :
  forall AtomType (F : frame) (p q : formula AtomType),
    frame_makinson F -> valid F (Mk p q).
Proof.
  intros AtomType F p q Hmak V x Hantecedent.
  destruct (proj1 (@satisfies_and AtomType F V x (Box p) q) Hantecedent)
    as [Hboxp Hqx].
  destruct (Hmak x) as [y [Rxy [Ryx Hreach]]].
  apply satisfies_dia_intro. exists y; split; [exact Rxy |].
  apply (proj2 (@satisfies_and AtomType F V y (Box (Box p)) (Dia q))).
  split.
  - intros u Ryu z Ruz.
    apply (Hboxp z). apply Hreach.
    simpl. exists u; split; [exact Ryu |].
    exists z; split; [exact Ruz | reflexivity].
  - apply satisfies_dia_intro. exists x; auto.
Qed.

(** Foundation proves only this semantic direction for Mk.  Its canonical
    instance is unfinished at the pinned revision and is intentionally not
    reproduced as an axiom. *)

(** * H / detour-free frames *)

Definition frame_detour_free (F : frame) : Prop :=
  forall x u y : World F,
    Rel F x u -> Rel F u y -> u = x \/ u = y.

Definition frame_has_no_proper_detour (F : frame) : Prop :=
  forall x y : World F,
    ~ exists u : World F,
        u <> x /\ u <> y /\ Rel F x u /\ Rel F u y.

Theorem detour_free_iff_no_proper_detour :
  forall F : frame,
    frame_detour_free F <-> frame_has_no_proper_detour F.
Proof.
  intro F; split.
  - intros Hdet x y [u [Hux [Huy [Rxu Ruy]]]].
    destruct (Hdet x u y Rxu Ruy); contradiction.
  - intros Hnone x u y Rxu Ruy.
    destruct (classic (u = x \/ u = y)) as [H | H]; [exact H |].
    exfalso. apply (Hnone x y). exists u. tauto.
Qed.

Lemma detour_free_antisymmetric :
  forall F : frame,
    frame_detour_free F -> frame_antisymmetric F.
Proof.
  intros F Hdet x y Rxy Ryx.
  destruct (Hdet x y x Rxy Ryx) as [Hyx | Hyx];
    now symmetry.
Qed.

Lemma valid_H_of_detour_free :
  forall AtomType (F : frame) (p : formula AtomType),
    frame_detour_free F -> valid F (H p).
Proof.
  intros AtomType F p Hdet V x Hpx u Rxu Hdia.
  destruct (satisfies_dia_elim Hdia) as [y [Ruy Hpy]].
  destruct (Hdet x u y Rxu Ruy) as [-> | ->]; assumption.
Qed.

Lemma detour_free_of_valid_H_atom :
  forall F : frame,
    valid F (H (Atom 0)) -> frame_detour_free F.
Proof.
  intros F Hvalid x u y Rxu Ruy.
  apply NNPP. intro Hnot.
  assert (Hux : u <> x) by tauto.
  assert (Huy : u <> y) by tauto.
  pose (V := (fun _ w => w <> u) : valuation nat F).
  assert (Hpx : satisfies F V x (Atom 0)).
  { intro Hxu. apply Hux. now symmetry. }
  assert (Hdia : satisfies F V u (Dia (Atom 0))).
  {
    apply satisfies_dia_intro. exists y; split; [exact Ruy |].
    intro Hyu. apply Huy. now symmetry.
  }
  pose proof (Hvalid V x Hpx u Rxu Hdia) as Hpu.
  exact (Hpu eq_refl).
Qed.

Theorem valid_H_atom_iff_detour_free :
  forall F : frame,
    valid F (H (Atom 0)) <-> frame_detour_free F.
Proof.
  intro F; split.
  - apply detour_free_of_valid_H_atom.
  - intro Hdet. exact (@valid_H_of_detour_free nat F (Atom 0) Hdet).
Qed.

(** * I / Boolos's prewellordering condition *)

Definition frame_boolos (F : frame) : Prop :=
  forall x y : World F,
    Rel F x y -> forall z : World F, Rel F x z \/ Rel F z y.

Lemma valid_I_of_transitive_boolos :
  forall AtomType (F : frame) (p q : formula AtomType),
    frame_transitive F -> frame_boolos F -> valid F (I p q).
Proof.
  intros AtomType F p q Htrans Hbool V x.
  apply (proj2 (@satisfies_or AtomType F V x
    (Box (Imp (Box p) (Box q)))
    (Box (Imp (Box q) (Boxdot p))))).
  destruct (classic (satisfies F V x (Box (Imp (Box p) (Box q)))))
    as [Hleft | Hnotleft]; [now left | right].
  assert (Hex : exists y : World F,
      Rel F x y /\ satisfies F V y (Box p) /\
      ~ satisfies F V y (Box q)).
  {
    apply NNPP. intro Hnone. apply Hnotleft.
    intros y Rxy Hboxp.
    apply NNPP. intro Hnotboxq. apply Hnone.
    exists y; auto.
  }
  destruct Hex as [y [Rxy [Hboxp Hnotboxq]]].
  assert (Hez : exists z : World F,
      Rel F y z /\ ~ satisfies F V z q).
  {
    apply NNPP. intro Hnone. apply Hnotboxq.
    intros z Ryz. apply NNPP. intro Hnotq.
    apply Hnone. exists z; auto.
  }
  destruct Hez as [z [Ryz Hnotq]].
  intros w Rxw Hboxq.
  apply (proj2 (@satisfies_and AtomType F V w p (Box p))).
  destruct (Hbool y z Ryz w) as [Ryw | Rwz].
  - split.
    + exact (Hboxp w Ryw).
    + intros v Rwv. apply Hboxp.
      eapply Htrans; eauto.
  - exfalso. exact (Hnotq (Hboxq z Rwz)).
Qed.

(** Foundation states only this directional validity theorem for axiom I. *)

(** * Grz / reflexive transitive weakly converse-well-founded frames *)

(** A maximal-element presentation of converse well-foundedness after
    deleting reflexive edges.  It is Foundation's [WeaklyConverseWellFounded]
    definition, specialized to a frame relation. *)
Definition frame_weak_converse_well_founded (F : frame) : Prop :=
  forall X : World F -> Prop,
    (exists x, X x) ->
    exists m, X m /\
      forall y, X y -> Rel F m y -> m = y.

Definition frame_irreflexive_reduction (F : frame) : frame :=
  {| World := World F;
     Rel := fun x y => Rel F x y /\ x <> y |}.

(** This records literally the upstream definition: weak converse
    well-foundedness is ordinary converse well-foundedness after deleting
    all reflexive edges. *)
Theorem weak_cwf_iff_cwf_irreflexive_reduction :
  forall F : frame,
    frame_weak_converse_well_founded F <->
    frame_converse_well_founded (frame_irreflexive_reduction F).
Proof.
  intro F; split.
  - intros Hweak X HX.
    destruct (Hweak X HX) as [m [Hm Hmax]].
    exists m; split; [exact Hm |].
    intros y Hy [Rmy Hneq]. apply Hneq. now apply (Hmax y).
  - intros Hcwf X HX.
    destruct (Hcwf X HX) as [m [Hm Hmax]].
    exists m; split; [exact Hm |].
    intros y Hy Rmy. apply NNPP. intro Hneq.
    exact (Hmax y Hy (conj Rmy Hneq)).
Qed.

Lemma weak_cwf_antisymmetric :
  forall F : frame,
    frame_weak_converse_well_founded F -> frame_antisymmetric F.
Proof.
  intros F Hwcwf x y Rxy Ryx.
  destruct (Hwcwf (fun z => z = x \/ z = y))
    as [m [Hm Hmax]].
  - exists x. now left.
  - destruct Hm as [-> | ->].
    + apply (Hmax y); [now right | exact Rxy].
    + symmetry. apply (Hmax x); [now left | exact Ryx].
Qed.

Lemma valid_Grz_of_reflexive_transitive_weak_cwf :
  forall AtomType (F : frame) (p : formula AtomType),
    frame_reflexive F -> frame_transitive F ->
    frame_weak_converse_well_founded F -> valid F (Grz p).
Proof.
  intros AtomType F p Hrefl Htrans Hwcwf V x Houter.
  apply NNPP. intro Hnotx.
  pose (X := fun u : World F =>
    Rel F x u /\ ~ satisfies F V u p).
  destruct (Hwcwf X) as [m [[Rxm Hnotm] Hmax]].
  - exists x; split; [apply Hrefl | exact Hnotx].
  - apply Hnotm. apply (Houter m Rxm).
    intros y Rmy Hpy z Ryz.
    apply NNPP. intro Hnotz.
    assert (Rmz : Rel F m z) by (eapply Htrans; eauto).
    assert (Rxz : Rel F x z) by (eapply Htrans; eauto).
    pose proof (Hmax z (conj Rxz Hnotz) Rmz) as Hmz.
    subst z.
    pose proof (@weak_cwf_antisymmetric F Hwcwf m y Rmy Ryz) as Hmy.
    subst y. contradiction.
Qed.

Lemma reflexive_of_valid_Grz_atom :
  forall F : frame,
    valid F (Grz (Atom 0)) -> frame_reflexive F.
Proof.
  intros F Hvalid x.
  apply NNPP. intro Hnotxx.
  pose (V := (fun _ y => Rel F x y) : valuation nat F).
  assert (Houter : satisfies F V x
      (Box (Imp (Box (Imp (Atom 0) (Box (Atom 0)))) (Atom 0)))).
  {
    intros y Rxy _. exact Rxy.
  }
  exact (Hnotxx (Hvalid V x Houter)).
Qed.

Lemma transitive_of_valid_Grz_atom :
  forall F : frame,
    valid F (Grz (Atom 0)) -> frame_transitive F.
Proof.
  intros F Hvalid x y z Rxy Ryz.
  apply NNPP. intro Hnotxz.
  pose (V := (fun _ u => u <> x /\ u <> z) : valuation nat F).
  assert (Houter : satisfies F V x
      (Box (Imp (Box (Imp (Atom 0) (Box (Atom 0)))) (Atom 0)))).
  {
    intros u Rxu Hbox. split.
    - intro Hux. subst u.
      assert (Hy : V 0 y).
      {
        split.
        - intro Hyx. subst y. contradiction.
        - intro Hyz. subst y. contradiction.
      }
      pose proof (Hbox y Rxy Hy z Ryz) as Hz.
      exact (proj2 Hz eq_refl).
    - intro Huz. subst u. contradiction.
  }
  pose proof (Hvalid V x Houter) as Hx.
  exact (proj1 Hx eq_refl).
Qed.

(** The three following consequences are Foundation's semantic
    [Grz -> T / Four] lemmas, proved here directly from the recovered frame
    properties rather than through a Hilbert derivation. *)
Lemma valid_T_and_Four_of_valid_Grz_atom :
  forall F : frame,
    valid F (Grz (Atom 0)) ->
    valid F
      (Imp (Box (Atom 0))
        (And (Atom 0) (Box (Box (Atom 0))))).
Proof.
  intros F Hgrz V x Hbox.
  pose proof (reflexive_of_valid_Grz_atom Hgrz) as Hrefl.
  pose proof (transitive_of_valid_Grz_atom Hgrz) as Htrans.
  apply (proj2 (@satisfies_and nat F V x
    (Atom 0) (Box (Box (Atom 0))))).
  split.
  - exact (Hbox x (Hrefl x)).
  - intros y Rxy z Ryz. apply Hbox.
    eapply Htrans; eauto.
Qed.

Lemma valid_T_of_valid_Grz_atom :
  forall F : frame,
    valid F (Grz (Atom 0)) -> valid F (T (Atom 0)).
Proof.
  intros F Hgrz.
  apply valid_T_of_reflexive.
  now apply reflexive_of_valid_Grz_atom.
Qed.

Lemma valid_Four_of_valid_Grz_atom :
  forall F : frame,
    valid F (Grz (Atom 0)) -> valid F (Four (Atom 0)).
Proof.
  intros F Hgrz.
  apply valid_Four_of_transitive.
  now apply transitive_of_valid_Grz_atom.
Qed.

Lemma antisymmetric_of_valid_Grz_atom :
  forall F : frame,
    valid F (Grz (Atom 0)) -> frame_antisymmetric F.
Proof.
  intros F Hvalid x y Rxy Ryx.
  apply NNPP. intro Hxy.
  pose (V := (fun _ u => u <> x) : valuation nat F).
  assert (Houter : satisfies F V x
      (Box (Imp (Box (Imp (Atom 0) (Box (Atom 0)))) (Atom 0)))).
  {
    intros u Rxu Hbox Hux. subst u.
    assert (Hy : V 0 y) by (intro Hyx; apply Hxy; now symmetry).
    pose proof (Hbox y Rxy Hy x Ryx) as Hx.
    exact (Hx eq_refl).
  }
  pose proof (Hvalid V x Houter) as Hx.
  exact (Hx eq_refl).
Qed.

Lemma weak_cwf_of_valid_Grz_atom :
  forall F : frame,
    valid F (Grz (Atom 0)) ->
    frame_weak_converse_well_founded F.
Proof.
  intros F Hvalid X [x0 Hx0].
  destruct (classic (exists m, X m /\
      forall y, X y -> Rel F m y -> m = y))
    as [Hmax | Hno_max]; [exact Hmax |].
  exfalso.
  assert (Hsuccessor : forall a, X a ->
      exists b, X b /\ Rel F a b /\ a <> b).
  {
    intros a Ha. apply NNPP. intro Hnone.
    apply Hno_max. exists a; split; [exact Ha |].
    intros b Hb Rab. apply NNPP. intro Hab.
    apply Hnone. exists b; auto.
  }
  assert (Htotal : forall a : World F,
      exists b : World F,
        X a -> X b /\ Rel F a b /\ a <> b).
  {
    intro a. destruct (classic (X a)) as [Ha | Hna].
    - destruct (Hsuccessor a Ha) as [b Hb]. exists b. tauto.
    - exists x0. tauto.
  }
  destruct (@choice (World F) (World F)
    (fun a b => X a -> X b /\ Rel F a b /\ a <> b) Htotal)
    as [next Hnext].
  pose (f := fun n : nat => Nat.iter n next x0).
  assert (HfX : forall n, X (f n)).
  {
    intro n; induction n as [|n IH].
    - exact Hx0.
    - change (X (next (f n))).
      exact (proj1 (Hnext (f n) IH)).
  }
  assert (Hfstep : forall n,
      Rel F (f n) (f (S n)) /\ f n <> f (S n)).
  {
    intro n. change (Rel F (f n) (next (f n)) /\ f n <> next (f n)).
    exact (proj2 (Hnext (f n) (HfX n))).
  }
  pose proof (transitive_of_valid_Grz_atom Hvalid) as Htrans.
  pose proof (antisymmetric_of_valid_Grz_atom Hvalid) as Hanti.
  assert (Hchain : forall j i, i < j -> Rel F (f i) (f j)).
  {
    intro j; induction j as [|j IH]; intros i Hij; [lia |].
    destruct (Nat.eq_dec i j) as [-> | Hneq].
    - exact (proj1 (Hfstep j)).
    - eapply Htrans.
      + apply IH. lia.
      + exact (proj1 (Hfstep j)).
  }
  assert (Hdistinct : forall i j, i < j -> f i <> f j).
  {
    intros i j Hij Heq.
    destruct (Nat.eq_dec (S i) j) as [Hsucc | Hsucc].
    - subst j. exact ((proj2 (Hfstep i)) Heq).
    - assert (Hisj : S i < j) by lia.
      pose proof (Hchain j (S i) Hisj) as Rsi_j.
      rewrite <- Heq in Rsi_j.
      pose proof (Hanti (f i) (f (S i))
        (proj1 (Hfstep i)) Rsi_j) as Heq_step.
      exact ((proj2 (Hfstep i)) Heq_step).
  }
  pose (V := (fun _ u => forall i, u <> f (2 * i)) : valuation nat F).
  assert (Houter : satisfies F V (f 0)
      (Box (Imp (Box (Imp (Atom 0) (Box (Atom 0)))) (Atom 0)))).
  {
    intros u R0u Hbox i Hui. subst u.
    assert (Hodd : V 0 (f (2 * i + 1))).
    {
      intros j Heq.
      destruct (Nat.lt_trichotomy (2 * i + 1) (2 * j))
        as [Hlt | [Heven | Hgt]].
      - exact (Hdistinct _ _ Hlt Heq).
      - lia.
      - apply (Hdistinct _ _ Hgt). now symmetry.
    }
    assert (Reven_odd : Rel F (f (2 * i)) (f (2 * i + 1))).
    {
      replace (2 * i + 1) with (S (2 * i)) by lia.
      exact (proj1 (Hfstep (2 * i))).
    }
    pose proof (Hbox (f (2 * i + 1)) Reven_odd Hodd) as Hboxodd.
    assert (Rodd_even :
      Rel F (f (2 * i + 1)) (f (2 * (i + 1)))).
    {
      replace (2 * (i + 1)) with (S (2 * i + 1)) by lia.
      exact (proj1 (Hfstep (2 * i + 1))).
    }
    pose proof (Hboxodd (f (2 * (i + 1))) Rodd_even) as Heven.
    exact (Heven (i + 1) eq_refl).
  }
  pose proof (Hvalid V (f 0) Houter) as Hzero.
  exact (Hzero 0 eq_refl).
Qed.

Theorem valid_Grz_atom_iff_reflexive_transitive_weak_cwf :
  forall F : frame,
    valid F (Grz (Atom 0)) <->
    frame_reflexive F /\ frame_transitive F /\
    frame_weak_converse_well_founded F.
Proof.
  intro F; split.
  - intro H; split.
    + now apply reflexive_of_valid_Grz_atom.
    + split.
      * now apply transitive_of_valid_Grz_atom.
      * now apply weak_cwf_of_valid_Grz_atom.
  - intros [Hrefl [Htrans Hwcwf]].
    exact (@valid_Grz_of_reflexive_transitive_weak_cwf
      nat F (Atom 0) Hrefl Htrans Hwcwf).
Qed.
