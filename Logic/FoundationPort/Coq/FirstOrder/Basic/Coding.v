(**
  Structural Gödel numbering for first-order syntax.

  This ports the injective coding and closed-syntax embedding core of
  [Foundation/FirstOrder/Basic/Coding.lean].  Codes are assembled from the
  standard library's Cantor pairing function.  Unlike the source interface,
  injectivity is exposed directly, independently of typeclass search; the
  only data required are verified encodings of free variables and language
  symbols.
*)

From Stdlib Require Import Arith.PeanoNat Cantor Vectors.Fin.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition encoding_injective {A} (E : encoding A) :
  forall x y, encode E x = encode E y -> x = y.
Proof.
  intros x y H.
  pose proof (f_equal (decode E) H) as Hd.
  now rewrite !decode_encode in Hd; injection Hd.
Qed.

(** A length-indexed vector code.  Its shape records the vector length
    externally, so the empty vector needs no payload. *)
Fixpoint fin_nat_code (k : nat) : (Fin.t k -> nat) -> nat :=
  match k as j return (Fin.t j -> nat) -> nat with
  | 0 => fun _ => 0
  | S j => fun v => Cantor.to_nat
      (v Fin.F1, fin_nat_code (fun i => v (Fin.FS i)))
  end.

(** Keep pairing abstract while destructing syntax in the injectivity proofs. *)
Local Opaque Cantor.to_nat.

Lemma fin_nat_code_injective : forall k (v w : Fin.t k -> nat),
  fin_nat_code v = fin_nat_code w -> v = w.
Proof.
  induction k as [|k IH]; intros v w H.
  - apply functional_extensionality. intro i. inversion i.
  - change (Cantor.to_nat
      (v Fin.F1, fin_nat_code (fun i => v (Fin.FS i))) =
      Cantor.to_nat
      (w Fin.F1, fin_nat_code (fun i => w (Fin.FS i)))) in H.
    apply Cantor.to_nat_inj in H. injection H as Hhead Htail.
    apply IH in Htail.
    apply functional_extensionality. intro i.
    refine (@Fin.caseS' k i (fun j => v j = w j) Hhead _).
    intro j. exact (f_equal (fun h => h j) Htail).
Qed.

Fixpoint semiterm_code {L X n}
    (EL : language_encodable L) (EX : encoding X)
    (t : semiterm L X n) : nat :=
  match t with
  | Semiterm_bvar i => Cantor.to_nat (0, fin_value i)
  | Semiterm_fvar x => Cantor.to_nat (1, encode EX x)
  | @Semiterm_func _ _ _ k f v =>
      Cantor.to_nat (2,
        Cantor.to_nat (k,
          Cantor.to_nat
            (encode (language_func_encoding EL k) f,
             fin_nat_code (fun i => semiterm_code EL EX (v i)))))
  end.

Lemma semiterm_code_bvar : forall L X n EL EX (i : Fin.t n),
  @semiterm_code L X n EL EX (Semiterm_bvar i) =
  Cantor.to_nat (0, fin_value i).
Proof. reflexivity. Qed.

Lemma semiterm_code_fvar : forall L X n EL EX (x : X),
  @semiterm_code L X n EL EX (Semiterm_fvar x) =
  Cantor.to_nat (1, encode EX x).
Proof. reflexivity. Qed.

Lemma semiterm_code_func : forall L X n EL EX k
    (f : language_func L k) (v : Fin.t k -> semiterm L X n),
  semiterm_code EL EX (Semiterm_func f v) =
  Cantor.to_nat (2,
    Cantor.to_nat (k,
      Cantor.to_nat
        (encode (language_func_encoding EL k) f,
         fin_nat_code (fun i => semiterm_code EL EX (v i))))).
Proof. reflexivity. Qed.

Theorem semiterm_code_injective : forall L X n EL EX
    (t u : semiterm L X n),
  semiterm_code EL EX t = semiterm_code EL EX u -> t = u.
Proof.
  intros L X n EL EX t. revert t.
  refine (@semiterm_rect L X n
    (fun t => forall u, semiterm_code EL EX t = semiterm_code EL EX u -> t = u)
    _ _ _).
  - intros i u H; destruct u as [j | y | k f v];
      cbn [semiterm_code] in H.
    + apply Cantor.to_nat_inj in H. injection H as Hij.
      f_equal. apply Fin.to_nat_inj. exact Hij.
    + apply Cantor.to_nat_inj in H. discriminate H.
    + apply Cantor.to_nat_inj in H. discriminate H.
  - intros x u H; destruct u as [j | y | k f v];
      cbn [semiterm_code] in H.
    + apply Cantor.to_nat_inj in H. discriminate H.
    + apply Cantor.to_nat_inj in H. injection H as Hxy.
      f_equal. exact (@encoding_injective X EX x y Hxy).
    + apply Cantor.to_nat_inj in H. discriminate H.
  - intros k f v IH u H; destruct u as [j | y | l g w];
      cbn [semiterm_code] in H.
    + apply Cantor.to_nat_inj in H. discriminate H.
    + apply Cantor.to_nat_inj in H. discriminate H.
    + apply Cantor.to_nat_inj in H. injection H as Hpayload.
      apply Cantor.to_nat_inj in Hpayload. injection Hpayload as Hkl Hrest.
      subst l.
      apply Cantor.to_nat_inj in Hrest. injection Hrest as Hfg Hvw.
      assert (Hf : f = g).
      { exact (@encoding_injective (language_func L k)
          (language_func_encoding EL k) f g Hfg). }
      assert (Hv : v = w).
      { apply fin_nat_code_injective in Hvw.
        apply functional_extensionality. intro i.
        apply IH. exact (f_equal (fun h => h i) Hvw). }
      now subst g; subst w.
Qed.

Fixpoint semiformula_code {L X n}
    (EL : language_encodable L) (EX : encoding X)
    (p : semiformula L X n) : nat :=
  match p with
  | Semiformula_verum _ => Cantor.to_nat (0, 0)
  | Semiformula_falsum _ => Cantor.to_nat (1, 0)
  | @Semiformula_rel _ _ _ k r v =>
      Cantor.to_nat (2,
        Cantor.to_nat (k,
          Cantor.to_nat
            (encode (language_rel_encoding EL k) r,
             fin_nat_code (fun i => semiterm_code EL EX (v i)))))
  | @Semiformula_nrel _ _ _ k r v =>
      Cantor.to_nat (3,
        Cantor.to_nat (k,
          Cantor.to_nat
            (encode (language_rel_encoding EL k) r,
             fin_nat_code (fun i => semiterm_code EL EX (v i)))))
  | Semiformula_and p q => Cantor.to_nat (4,
      Cantor.to_nat (semiformula_code EL EX p, semiformula_code EL EX q))
  | Semiformula_or p q => Cantor.to_nat (5,
      Cantor.to_nat (semiformula_code EL EX p, semiformula_code EL EX q))
  | Semiformula_all p => Cantor.to_nat (6, semiformula_code EL EX p)
  | Semiformula_exists p => Cantor.to_nat (7, semiformula_code EL EX p)
  end.

Theorem semiformula_code_injective : forall L X n EL EX
    (p q : semiformula L X n),
  semiformula_code EL EX p = semiformula_code EL EX q -> p = q.
Proof.
  intros L X n EL EX p. revert p.
  refine (@semiformula_rect L X
    (fun n p => forall q, semiformula_code EL EX p = semiformula_code EL EX q -> p = q)
    _ _ _ _ _ _ _ _ n).
  - intros j q H; destruct q; cbn [semiformula_code] in H;
      apply Cantor.to_nat_inj in H; try discriminate H; reflexivity.
  - intros j q H; destruct q; cbn [semiformula_code] in H;
      apply Cantor.to_nat_inj in H; try discriminate H; reflexivity.
  - intros j k r v q H; destruct q as [| |j' l s w| | | | |];
      cbn [semiformula_code] in H;
      apply Cantor.to_nat_inj in H; try discriminate H.
    injection H as Hp. apply Cantor.to_nat_inj in Hp.
    injection Hp as Hkl Hr. subst l.
    apply Cantor.to_nat_inj in Hr.
    injection Hr as Hrs Hvw.
    assert (Hsym : r = s) by
      exact (@encoding_injective (language_rel L k)
        (language_rel_encoding EL k) r s Hrs).
    assert (Hvec : v = w).
    { apply fin_nat_code_injective in Hvw.
      apply functional_extensionality. intro i.
      exact (@semiterm_code_injective L X _ EL EX (v i) (w i)
        (f_equal (fun h => h i) Hvw)). }
    now subst s; subst w.
  - intros j k r v q H; destruct q as [| | |j' l s w| | | |];
      cbn [semiformula_code] in H;
      apply Cantor.to_nat_inj in H; try discriminate H.
    injection H as Hp. apply Cantor.to_nat_inj in Hp.
    injection Hp as Hkl Hr. subst l.
    apply Cantor.to_nat_inj in Hr.
    injection Hr as Hrs Hvw.
    assert (Hsym : r = s) by
      exact (@encoding_injective (language_rel L k)
        (language_rel_encoding EL k) r s Hrs).
    assert (Hvec : v = w).
    { apply fin_nat_code_injective in Hvw.
      apply functional_extensionality. intro i.
      exact (@semiterm_code_injective L X _ EL EX (v i) (w i)
        (f_equal (fun h => h i) Hvw)). }
    now subst s; subst w.
  - intros j p IHp q IHq r H; destruct r;
      cbn [semiformula_code] in H;
      apply Cantor.to_nat_inj in H; try discriminate H.
    injection H as Hpq. apply Cantor.to_nat_inj in Hpq.
    injection Hpq as Hp Hq. f_equal; [apply IHp | apply IHq]; assumption.
  - intros j p IHp q IHq r H; destruct r;
      cbn [semiformula_code] in H;
      apply Cantor.to_nat_inj in H; try discriminate H.
    injection H as Hpq. apply Cantor.to_nat_inj in Hpq.
    injection Hpq as Hp Hq. f_equal; [apply IHp | apply IHq]; assumption.
  - intros j p IHp q H; destruct q;
      cbn [semiformula_code] in H;
      apply Cantor.to_nat_inj in H; try discriminate H.
    injection H as Hp. f_equal. now apply IHp.
  - intros j p IHp q H; destruct q;
      cbn [semiformula_code] in H;
      apply Cantor.to_nat_inj in H; try discriminate H.
    injection H as Hp. f_equal. now apply IHp.
Qed.

Lemma semiterm_code_emb : forall L n EL
    (t : closed_semiterm L n) X (EX : encoding X),
  semiterm_code EL EX
    (rew_apply (@rew_emb L Empty_set X n (fun x => match x with end)) t) =
  semiterm_code EL empty_encoding t.
Proof.
  intros L n EL t. induction t as [i | x | k f v IH]; intros X EX.
  - reflexivity.
  - destruct x.
  - rewrite rew_apply_func, !semiterm_code_func.
    apply f_equal. apply f_equal. apply f_equal. apply f_equal.
    apply f_equal. apply f_equal. apply f_equal.
    apply functional_extensionality. intro i. apply IH.
Qed.

Lemma semiformula_code_emb : forall L n EL
    (p : semisentence L n) X (EX : encoding X),
  semiformula_code EL EX
    (semiformula_rewrite
      (@rew_emb L Empty_set X n (fun x => match x with end)) p) =
  semiformula_code EL empty_encoding p.
Proof.
  intros L n EL p. induction p; intros X EX;
    cbn [semiformula_rewrite semiformula_code].
  - reflexivity.
  - reflexivity.
  - apply f_equal. apply f_equal. apply f_equal. apply f_equal.
    apply f_equal. apply f_equal. apply f_equal.
    apply functional_extensionality. intro i. apply semiterm_code_emb.
  - apply f_equal. apply f_equal. apply f_equal. apply f_equal.
    apply f_equal. apply f_equal. apply f_equal.
    apply functional_extensionality. intro i. apply semiterm_code_emb.
  - now rewrite IHp1, IHp2.
  - now rewrite IHp1, IHp2.
  - assert (Hr :
      semiformula_rewrite
        (rew_q (@rew_emb L Empty_set X n (fun x => match x with end))) p =
      semiformula_rewrite
        (@rew_emb L Empty_set X (S n) (fun x => match x with end)) p).
    { apply semiformula_rewrite_ext. apply rew_q_emb. }
    rewrite Hr. now rewrite IHp.
  - assert (Hr :
      semiformula_rewrite
        (rew_q (@rew_emb L Empty_set X n (fun x => match x with end))) p =
      semiformula_rewrite
        (@rew_emb L Empty_set X (S n) (fun x => match x with end)) p).
    { apply semiformula_rewrite_ext. apply rew_q_emb. }
    rewrite Hr. now rewrite IHp.
Qed.

Corollary semiformula_code_closed_injection : forall L n EL
    (p : semiformula L Empty_set n) X (EX : encoding X)
    (q : semiformula L X n),
  semiformula_code EL EX q = semiformula_code EL empty_encoding p <->
  q = semiformula_rewrite
    (@rew_emb L Empty_set X n (fun x => match x with end)) p.
Proof.
  intros L n EL p X EX q. split.
  - intro H. apply (@semiformula_code_injective L X n EL EX).
    now rewrite semiformula_code_emb.
  - intros ->. apply semiformula_code_emb.
Qed.

Corollary semiformula_code_closed_injection_rev : forall L n EL
    (p : semiformula L Empty_set n) X (EX : encoding X)
    (q : semiformula L X n),
  semiformula_code EL empty_encoding p = semiformula_code EL EX q <->
  q = semiformula_rewrite
    (@rew_emb L Empty_set X n (fun x => match x with end)) p.
Proof.
  intros L n EL p X EX q. split; intro H.
  - apply (proj1 (@semiformula_code_closed_injection
      L n EL p X EX q)). now symmetry.
  - symmetry. now apply (proj2 (@semiformula_code_closed_injection
      L n EL p X EX q)).
Qed.
