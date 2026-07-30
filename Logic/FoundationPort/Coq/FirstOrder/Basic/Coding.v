(**
  Executable structural Gödel numbering for first-order syntax.

  This ports [Foundation/FirstOrder/Basic/Coding.lean].  Codes are assembled
  from the standard library's Cantor pairing function and decoded by bounded
  structural search.  Unlike the source interface, injectivity is also
  exposed directly, independently of typeclass search; the only data required
  are verified encodings of free variables and language symbols.
*)

From Stdlib Require Import Arith.Compare_dec Arith.PeanoNat Cantor Lia Vectors.Fin.
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

Definition fin_coding_cons {A} {k}
    (x : A) (v : Fin.t k -> A) : Fin.t (S k) -> A :=
  fun i => @Fin.caseS' k i (fun _ => A) x v.

Fixpoint fin_nat_decode (k : nat) : nat -> Fin.t k -> nat :=
  match k as j return nat -> Fin.t j -> nat with
  | 0 => fun _ i => match i with end
  | S j => fun code =>
      let '(head, tail) := Cantor.of_nat code in
      fin_coding_cons head (@fin_nat_decode j tail)
  end.

Lemma fin_nat_decode_code : forall k (v : Fin.t k -> nat),
  @fin_nat_decode k (fin_nat_code v) = v.
Proof.
  induction k as [|k IH]; intro v.
  - apply functional_extensionality. intro i. inversion i.
  - cbn [fin_nat_code fin_nat_decode]. rewrite Cantor.cancel_of_to.
    apply functional_extensionality. intro i.
    refine (@Fin.caseS' k i
      (fun j => fin_coding_cons (v Fin.F1)
        (@fin_nat_decode k (fin_nat_code (fun u => v (Fin.FS u)))) j = v j)
      eq_refl _).
    intro j. cbn [fin_coding_cons].
    exact (f_equal (fun h => h j) (IH (fun u => v (Fin.FS u)))).
Qed.

Lemma fin_nat_code_component_le : forall k (v : Fin.t k -> nat) i,
  v i <= fin_nat_code v.
Proof.
  induction k as [|k IH]; intros v i; [inversion i|].
  change (v i <= Cantor.to_nat
    (v Fin.F1, fin_nat_code (fun j => v (Fin.FS j)))).
  pose proof (Cantor.to_nat_non_decreasing
    (v Fin.F1) (fin_nat_code (fun j => v (Fin.FS j)))) as Hpair.
  refine (@Fin.caseS' k i
    (fun j => v j <= Cantor.to_nat
      (v Fin.F1, fin_nat_code (fun u => v (Fin.FS u)))) _ _).
  - lia.
  - intro j.
    pose proof (IH (fun u => v (Fin.FS u)) j). lia.
Qed.

Fixpoint fin_option_sequence (k : nat) {A : Type} :
    (Fin.t k -> option A) -> option (Fin.t k -> A) :=
  match k as j return
      (Fin.t j -> option A) -> option (Fin.t j -> A) with
  | 0 => fun _ => Some (fun i : Fin.t 0 => match i with end)
  | S j => fun v =>
      match v Fin.F1,
            @fin_option_sequence j A (fun i => v (Fin.FS i)) with
      | Some x, Some xs => Some (fin_coding_cons x xs)
      | _, _ => None
      end
  end.

Lemma fin_option_sequence_some : forall k A
    (v : Fin.t k -> option A) (w : Fin.t k -> A),
  (forall i, v i = Some (w i)) -> @fin_option_sequence k A v = Some w.
Proof.
  induction k as [|k IH]; intros A v w H.
  - cbn [fin_option_sequence]. f_equal.
    apply functional_extensionality. intro i. inversion i.
  - cbn [fin_option_sequence]. rewrite H.
    rewrite (IH A (fun i => v (Fin.FS i))
      (fun i => w (Fin.FS i)) (fun i => H (Fin.FS i))).
    f_equal. apply functional_extensionality. intro i.
    refine (@Fin.caseS' k i
      (fun j => fin_coding_cons (w Fin.F1)
        (fun u => w (Fin.FS u)) j = w j) eq_refl _).
    reflexivity.
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

Fixpoint semiterm_decode_fuel {L X}
    (EL : language_encodable L) (EX : encoding X)
    (fuel n code : nat) : option (semiterm L X n) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      let '(tag, payload) := Cantor.of_nat code in
      match tag with
      | 0 =>
          match lt_dec payload n with
          | left H => Some (Semiterm_bvar (Fin.of_nat_lt H))
          | right _ => None
          end
      | 1 => option_map Semiterm_fvar (decode EX payload)
      | 2 =>
          let '(k, rest) := Cantor.of_nat payload in
          let '(ef, ev) := Cantor.of_nat rest in
          match decode (language_func_encoding EL k) ef with
          | None => None
          | Some f =>
              match @fin_option_sequence k (semiterm L X n)
                (fun i => semiterm_decode_fuel EL EX fuel' n
                  (@fin_nat_decode k ev i)) with
              | None => None
              | Some v => Some (Semiterm_func f v)
              end
          end
      | _ => None
      end
  end.

Definition semiterm_decode {L X} (EL : language_encodable L)
    (EX : encoding X) (n code : nat) : option (semiterm L X n) :=
  semiterm_decode_fuel EL EX (S code) n code.

Theorem semiterm_decode_fuel_code : forall L X n EL EX
    (t : semiterm L X n) fuel,
  semiterm_code EL EX t < fuel ->
  semiterm_decode_fuel EL EX fuel n (semiterm_code EL EX t) = Some t.
Proof.
  intros L X n EL EX t.
  induction t as [i | x | k f v IH].
  - intros fuel Hfuel. destruct fuel as [|fuel']; [lia|].
    cbn [semiterm_code semiterm_decode_fuel].
    rewrite Cantor.cancel_of_to. cbn [fst snd].
    destruct (lt_dec (fin_value i) n) as [Hi | Hi].
    + f_equal. f_equal. apply Fin.to_nat_inj.
      rewrite Fin.to_nat_of_nat. reflexivity.
    + exfalso. apply Hi. exact (proj2_sig (Fin.to_nat i)).
  - intros fuel Hfuel. destruct fuel as [|fuel']; [lia|].
    cbn [semiterm_code semiterm_decode_fuel].
    rewrite Cantor.cancel_of_to. cbn [fst snd].
    now rewrite decode_encode.
  - intros fuel Hfuel. destruct fuel as [|fuel']; [lia|].
    cbn [semiterm_code semiterm_decode_fuel].
    rewrite !Cantor.cancel_of_to. cbn [fst snd].
    rewrite decode_encode, fin_nat_decode_code.
    rewrite (fin_option_sequence_some
      (v := fun i => semiterm_decode_fuel EL EX fuel' n
        (semiterm_code EL EX (v i))) (w := v)).
    + reflexivity.
    + intro i. apply IH.
      cbn [semiterm_code] in Hfuel.
      pose proof (fin_nat_code_component_le
        (fun j => semiterm_code EL EX (v j)) i) as Hcomponent.
      pose proof (Cantor.to_nat_non_decreasing
        (encode (language_func_encoding EL k) f)
        (fin_nat_code (fun j => semiterm_code EL EX (v j)))) as Hsymbol.
      pose proof (Cantor.to_nat_non_decreasing k
        (Cantor.to_nat
          (encode (language_func_encoding EL k) f,
           fin_nat_code (fun j => semiterm_code EL EX (v j))))) as Harity.
      pose proof (Cantor.to_nat_non_decreasing 2
        (Cantor.to_nat (k,
          Cantor.to_nat
            (encode (language_func_encoding EL k) f,
             fin_nat_code (fun j => semiterm_code EL EX (v j)))))) as Houter.
      lia.
Qed.

Theorem semiterm_decode_code : forall L X n EL EX
    (t : semiterm L X n),
  semiterm_decode EL EX n (semiterm_code EL EX t) = Some t.
Proof.
  intros. unfold semiterm_decode. apply semiterm_decode_fuel_code. lia.
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

Lemma semiformula_code_verum : forall L X n EL EX,
  @semiformula_code L X n EL EX (Semiformula_verum n) =
  Cantor.to_nat (0, 0).
Proof. reflexivity. Qed.

Lemma semiformula_code_falsum : forall L X n EL EX,
  @semiformula_code L X n EL EX (Semiformula_falsum n) =
  Cantor.to_nat (1, 0).
Proof. reflexivity. Qed.

Lemma semiformula_code_rel : forall L X n EL EX k
    (r : language_rel L k) (v : Fin.t k -> semiterm L X n),
  semiformula_code EL EX (Semiformula_rel r v) =
  Cantor.to_nat (2,
    Cantor.to_nat (k,
      Cantor.to_nat
        (encode (language_rel_encoding EL k) r,
         fin_nat_code (fun i => semiterm_code EL EX (v i))))).
Proof. reflexivity. Qed.

Lemma semiformula_code_nrel : forall L X n EL EX k
    (r : language_rel L k) (v : Fin.t k -> semiterm L X n),
  semiformula_code EL EX (Semiformula_nrel r v) =
  Cantor.to_nat (3,
    Cantor.to_nat (k,
      Cantor.to_nat
        (encode (language_rel_encoding EL k) r,
         fin_nat_code (fun i => semiterm_code EL EX (v i))))).
Proof. reflexivity. Qed.

Lemma semiformula_code_and : forall L X n EL EX
    (p q : semiformula L X n),
  semiformula_code EL EX (Semiformula_and p q) =
  Cantor.to_nat (4,
    Cantor.to_nat (semiformula_code EL EX p, semiformula_code EL EX q)).
Proof. reflexivity. Qed.

Lemma semiformula_code_or : forall L X n EL EX
    (p q : semiformula L X n),
  semiformula_code EL EX (Semiformula_or p q) =
  Cantor.to_nat (5,
    Cantor.to_nat (semiformula_code EL EX p, semiformula_code EL EX q)).
Proof. reflexivity. Qed.

Lemma semiformula_code_all : forall L X n EL EX
    (p : semiformula L X (S n)),
  semiformula_code EL EX (Semiformula_all p) =
  Cantor.to_nat (6, semiformula_code EL EX p).
Proof. reflexivity. Qed.

Lemma semiformula_code_exists : forall L X n EL EX
    (p : semiformula L X (S n)),
  semiformula_code EL EX (Semiformula_exists p) =
  Cantor.to_nat (7, semiformula_code EL EX p).
Proof. reflexivity. Qed.

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

Fixpoint semiformula_decode_fuel {L X}
    (EL : language_encodable L) (EX : encoding X)
    (fuel n code : nat) : option (semiformula L X n) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      let '(tag, payload) := Cantor.of_nat code in
      match tag with
      | 0 => Some (Semiformula_verum n)
      | 1 => Some (Semiformula_falsum n)
      | 2 =>
          let '(k, rest) := Cantor.of_nat payload in
          let '(er, ev) := Cantor.of_nat rest in
          match decode (language_rel_encoding EL k) er with
          | None => None
          | Some r =>
              match @fin_option_sequence k (semiterm L X n)
                (fun i => semiterm_decode EL EX n (@fin_nat_decode k ev i)) with
              | None => None
              | Some v => Some (Semiformula_rel r v)
              end
          end
      | 3 =>
          let '(k, rest) := Cantor.of_nat payload in
          let '(er, ev) := Cantor.of_nat rest in
          match decode (language_rel_encoding EL k) er with
          | None => None
          | Some r =>
              match @fin_option_sequence k (semiterm L X n)
                (fun i => semiterm_decode EL EX n (@fin_nat_decode k ev i)) with
              | None => None
              | Some v => Some (Semiformula_nrel r v)
              end
          end
      | 4 =>
          let '(ep, eq) := Cantor.of_nat payload in
          match semiformula_decode_fuel EL EX fuel' n ep,
                semiformula_decode_fuel EL EX fuel' n eq with
          | Some p, Some q => Some (Semiformula_and p q)
          | _, _ => None
          end
      | 5 =>
          let '(ep, eq) := Cantor.of_nat payload in
          match semiformula_decode_fuel EL EX fuel' n ep,
                semiformula_decode_fuel EL EX fuel' n eq with
          | Some p, Some q => Some (Semiformula_or p q)
          | _, _ => None
          end
      | 6 =>
          option_map Semiformula_all
            (semiformula_decode_fuel EL EX fuel' (S n) payload)
      | 7 =>
          option_map Semiformula_exists
            (semiformula_decode_fuel EL EX fuel' (S n) payload)
      | _ => None
      end
  end.

Definition semiformula_decode {L X} (EL : language_encodable L)
    (EX : encoding X) (n code : nat) : option (semiformula L X n) :=
  semiformula_decode_fuel EL EX (S code) n code.

Lemma cantor_payload_lt_fuel : forall tag payload fuel,
  0 < tag -> Cantor.to_nat (tag, payload) < S fuel -> payload < fuel.
Proof.
  intros tag payload fuel Htag Hcode.
  pose proof (Cantor.to_nat_non_decreasing tag payload). lia.
Qed.

Lemma cantor_pair_components_lt_fuel : forall tag left right fuel,
  0 < tag ->
  Cantor.to_nat (tag, Cantor.to_nat (left, right)) < S fuel ->
  left < fuel /\ right < fuel.
Proof.
  intros tag left right fuel Htag Hcode.
  pose proof (Cantor.to_nat_non_decreasing left right) as Hinner.
  pose proof (Cantor.to_nat_non_decreasing tag
    (Cantor.to_nat (left, right))) as Houter.
  lia.
Qed.

Theorem semiformula_decode_fuel_code : forall L X n EL EX
    (p : semiformula L X n) fuel,
  semiformula_code EL EX p < fuel ->
  semiformula_decode_fuel EL EX fuel n (semiformula_code EL EX p) = Some p.
Proof.
  intros L X n EL EX p. induction p.
  - intros fuel Hfuel. destruct fuel as [|fuel']; [lia|].
    cbn [semiformula_code semiformula_decode_fuel].
    now rewrite Cantor.cancel_of_to.
  - intros fuel Hfuel. destruct fuel as [|fuel']; [lia|].
    cbn [semiformula_code semiformula_decode_fuel].
    now rewrite Cantor.cancel_of_to.
  - intros fuel Hfuel. destruct fuel as [|fuel']; [lia|].
    cbn [semiformula_code semiformula_decode_fuel].
    rewrite !Cantor.cancel_of_to. cbn [fst snd].
    rewrite decode_encode, fin_nat_decode_code.
    rewrite (fin_option_sequence_some
      (v := fun i => semiterm_decode EL EX n (semiterm_code EL EX (s i)))
      (w := s)).
    + reflexivity.
    + intro i. apply semiterm_decode_code.
  - intros fuel Hfuel. destruct fuel as [|fuel']; [lia|].
    cbn [semiformula_code semiformula_decode_fuel].
    rewrite !Cantor.cancel_of_to. cbn [fst snd].
    rewrite decode_encode, fin_nat_decode_code.
    rewrite (fin_option_sequence_some
      (v := fun i => semiterm_decode EL EX n (semiterm_code EL EX (s i)))
      (w := s)).
    + reflexivity.
    + intro i. apply semiterm_decode_code.
  - intros fuel Hfuel. destruct fuel as [|fuel']; [lia|].
    cbn [semiformula_code] in Hfuel.
    pose proof (@cantor_pair_components_lt_fuel 4
      (semiformula_code EL EX p1) (semiformula_code EL EX p2)
      fuel' ltac:(lia) Hfuel) as [Hp Hq].
    cbn [semiformula_code semiformula_decode_fuel].
    rewrite !Cantor.cancel_of_to. cbn [fst snd].
    now rewrite (IHp1 fuel' Hp), (IHp2 fuel' Hq).
  - intros fuel Hfuel. destruct fuel as [|fuel']; [lia|].
    cbn [semiformula_code] in Hfuel.
    pose proof (@cantor_pair_components_lt_fuel 5
      (semiformula_code EL EX p1) (semiformula_code EL EX p2)
      fuel' ltac:(lia) Hfuel) as [Hp Hq].
    cbn [semiformula_code semiformula_decode_fuel].
    rewrite !Cantor.cancel_of_to. cbn [fst snd].
    now rewrite (IHp1 fuel' Hp), (IHp2 fuel' Hq).
  - intros fuel Hfuel. destruct fuel as [|fuel']; [lia|].
    cbn [semiformula_code] in Hfuel.
    pose proof (@cantor_payload_lt_fuel 6
      (semiformula_code EL EX p) fuel' ltac:(lia) Hfuel) as Hp.
    cbn [semiformula_code semiformula_decode_fuel].
    rewrite Cantor.cancel_of_to. cbn [fst snd].
    now rewrite (IHp fuel' Hp).
  - intros fuel Hfuel. destruct fuel as [|fuel']; [lia|].
    cbn [semiformula_code] in Hfuel.
    pose proof (@cantor_payload_lt_fuel 7
      (semiformula_code EL EX p) fuel' ltac:(lia) Hfuel) as Hp.
    cbn [semiformula_code semiformula_decode_fuel].
    rewrite Cantor.cancel_of_to. cbn [fst snd].
    now rewrite (IHp fuel' Hp).
Qed.

Theorem semiformula_decode_code : forall L X n EL EX
    (p : semiformula L X n),
  semiformula_decode EL EX n (semiformula_code EL EX p) = Some p.
Proof.
  intros. unfold semiformula_decode. apply semiformula_decode_fuel_code. lia.
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

Definition semiterm_encoding (L : language) (X : Type) (n : nat)
    (EL : language_encodable L) (EX : encoding X) :
    encoding (semiterm L X n) :=
  {| encode := semiterm_code EL EX;
     decode := semiterm_decode EL EX n;
     decode_encode := @semiterm_decode_code L X n EL EX |}.

Definition semiformula_encoding (L : language) (X : Type) (n : nat)
    (EL : language_encodable L) (EX : encoding X) :
    encoding (semiformula L X n) :=
  {| encode := semiformula_code EL EX;
     decode := semiformula_decode EL EX n;
     decode_encode := @semiformula_decode_code L X n EL EX |}.

Lemma semiterm_encoding_encode : forall L X n EL EX
    (t : semiterm L X n),
  encode (semiterm_encoding n EL EX) t = semiterm_code EL EX t.
Proof. reflexivity. Qed.

Lemma semiformula_encoding_encode : forall L X n EL EX
    (p : semiformula L X n),
  encode (semiformula_encoding n EL EX) p = semiformula_code EL EX p.
Proof. reflexivity. Qed.
