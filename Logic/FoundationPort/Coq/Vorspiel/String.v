(** Rendering finite vectors of strings. *)

From Stdlib Require Import Strings.String Vectors.Fin.

Open Scope string_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Fixpoint fin_string_join (separator : string) (n : nat) :
    (Fin.t n -> string) -> string :=
  match n as k return (Fin.t k -> string) -> string with
  | 0 => fun _ => EmptyString
  | S k => fun values =>
      match k with
      | 0 => values Fin.F1
      | S _ => values Fin.F1 ++ separator ++
          @fin_string_join separator k (fun i => values (Fin.FS i))
      end
  end.

Definition fin_vec_to_string n (values : Fin.t n -> string) : string :=
  @fin_string_join ", " n values.

Lemma fin_string_join_zero : forall separator (values : Fin.t 0 -> string),
  @fin_string_join separator 0 values = EmptyString.
Proof. reflexivity. Qed.

Lemma fin_string_join_one : forall separator (values : Fin.t 1 -> string),
  @fin_string_join separator 1 values = values Fin.F1.
Proof. reflexivity. Qed.

Lemma fin_string_join_many : forall separator n
    (values : Fin.t (S (S n)) -> string),
  @fin_string_join separator (S (S n)) values =
  values Fin.F1 ++ separator ++
    @fin_string_join separator (S n) (fun i => values (Fin.FS i)).
Proof. reflexivity. Qed.

Lemma fin_vec_to_string_zero : forall values : Fin.t 0 -> string,
  fin_vec_to_string values = EmptyString.
Proof. reflexivity. Qed.

Lemma fin_vec_to_string_one : forall values : Fin.t 1 -> string,
  fin_vec_to_string values = values Fin.F1.
Proof. reflexivity. Qed.

Lemma fin_vec_to_string_many : forall n
    (values : Fin.t (S (S n)) -> string),
  fin_vec_to_string values =
  values Fin.F1 ++ ", " ++
    fin_vec_to_string (fun i => values (Fin.FS i)).
Proof. reflexivity. Qed.
