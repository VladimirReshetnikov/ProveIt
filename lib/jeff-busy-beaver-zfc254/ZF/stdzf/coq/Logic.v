(** * Logic: the formal system searched by the ZF machine (O'Rear's zf2.nql, Wade's zf2.py).

    Tarski's system S2 for first-order logic with equality and one binary predicate "e."
    (membership), modified as described in the header of O'Rear's zf2.nql
    (https://github.com/sorear/metamath-turing-machines/blob/master/machines/2017-zf-sorear-748/zf2.nql),
    plus the axioms EXT, REP (scheme), POW, UNI, INF of ZF without regularity and choice.
    Set variables are natural numbers; v_0 .. v_3 are 0 .. 3.

    THIS FILE IS PART OF THE TRUST SURFACE: a reviewer should compare [prov] with the axiom list
    in zf2.nql.  Everything else is proved. *)

From Coq Require Import Arith.Arith Lia Lists.List Bool.Bool.
Import ListNotations.

(** ** Wffs *)
Inductive wff : Type :=
  | Weq (x y : nat)          (* x = y *)
  | Wel (x y : nat)          (* x e. y *)
  | Wim (a b : wff)          (* ( a -> b ) *)
  | Wn (a : wff)             (* -. a *)
  | Wal (x : nat) (a : wff). (* A. x a *)

Definition Wex (x : nat) (a : wff) : wff := Wn (Wal x (Wn a)).   (* E. x a  :=  -. A. x -. a *)
Definition Wa (a b : wff) : wff := Wn (Wim a (Wn b)).            (* a /\ b  :=  -. ( a -> -. b ) *)

Definition v0 := 0. Definition v1 := 1. Definition v2 := 2. Definition v3 := 3.

(** ** The ZF axioms, exactly as built by the machine (clause programs of zf2.py, see gen_enum.py). *)
Definition EXT : wff :=
  Wim (Wal v2 (Wa (Wim (Wel v2 v0) (Wel v2 v1)) (Wim (Wel v2 v1) (Wel v2 v0)))) (Weq v0 v1).
Definition REP (ph : wff) : wff :=
  Wim (Wal v3 (Wex v1 (Wal v2 (Wim (Wal v1 ph) (Weq v2 v1)))))
      (Wex v1 (Wal v2 (Wa (Wim (Wel v2 v1) (Wex v3 (Wa (Wel v3 v0) (Wal v1 ph))))
                          (Wim (Wex v3 (Wa (Wel v3 v0) (Wal v1 ph))) (Wel v2 v1))))).
Definition POW : wff :=
  Wex v1 (Wal v2 (Wim (Wal v3 (Wim (Wel v3 v2) (Wel v3 v0))) (Wel v2 v1))).
Definition UNI : wff :=
  Wex v1 (Wal v2 (Wim (Wex v3 (Wa (Wel v2 v3) (Wel v3 v0))) (Wel v2 v1))).
Definition INF : wff :=
  Wex v1 (Wa (Wel v0 v1)
             (Wal v0 (Wim (Wel v0 v1)
                          (Wex v2 (Wa (Wel v2 v1)
                                      (Wal v1 (Wa (Wim (Wel v1 v2) (Weq v1 v0))
                                                  (Wim (Weq v1 v0) (Wel v1 v2))))))))).

(** ** Provability.  Metavariables a b c range over wffs, x y z over variables (nat). *)
Inductive prov : wff -> Prop :=
  | DET a b : prov (Wim a b) -> prov a -> prov b
  | GEN x a : prov a -> prov (Wal x a)
  | B1 a b c : prov (Wim (Wim a b) (Wim (Wim b c) (Wim a c)))
  | B2 a : prov (Wim (Wim (Wn a) a) a)
  | B3 a b : prov (Wim a (Wim (Wn a) b))
  | B4 x a b : prov (Wim (Wal x (Wim a b)) (Wim (Wal x a) (Wal x b)))
  | B6a x y z : x <> z -> y <> z ->
      prov (Wa (Wim (Weq x y) (Wal z (Weq x y))) (Wim (Wel x y) (Wal z (Wel x y))))
  | B6b x y a : prov (Wim (Wal x (Wal y a)) (Wal y (Wal x a)))
  | B6c x a : prov (Wim (Wex x (Wal x a)) a)
  | B7 x y : prov (Wex x (Weq x y))
  | B8a x y z : prov (Wim (Weq x y) (Wim (Weq x z) (Weq y z)))
  | B8b x y z : prov (Wim (Weq x y) (Wim (Wel x z) (Wel y z)))
  | B8c x y z : prov (Wim (Weq x y) (Wim (Wel z x) (Wel z y)))
  | AX_EXT : prov EXT
  | AX_REP a : prov (REP a)
  | AX_POW : prov POW
  | AX_UNI : prov UNI
  | AX_INF : prov INF.

(** The machine halts when it has proved [Wel v0 v0] ("v_0 e. v_0"), which is refutable in ZF,
    so [prov (Wel v0 v0)] iff the system is inconsistent (iff ZF is inconsistent, as ZF minus
    regularity and choice is equiconsistent with ZF).  The main theorem is stated with
    [prov (Wel v0 v0)]. *)

(** ** Numeric codes (Cantor pairing), as used by the machine. *)
Definition tri (s : nat) : nat := s * (s + 1) / 2.
Definition pair (x y : nat) : nat := x + tri (x + y).

(* Wade's unpair loop: walk the Cantor diagonals z steps from (0,0). *)
Definition unpair_step (o : nat * nat) : nat * nat :=
  match o with
  | (o1, S o2) => (S o1, o2)
  | (o1, 0) => (0, S o1)
  end.
Definition unpair (z : nat) : nat * nat := Nat.iter z unpair_step (0, 0).

Fixpoint code (a : wff) : nat :=
  match a with
  | Weq x y => pair (pair x y) 0
  | Wel x y => pair (pair x y) 1
  | Wim a b => pair (pair (code a) (code b)) 2
  | Wn a => pair (code a) 3
  | Wal x a => pair (pair x (code a)) 4
  end.

(* numeric constructors used by the enumerator *)
Definition weq (x y : nat) := pair (pair x y) 0.
Definition wel (x y : nat) := pair (pair x y) 1.
Definition wim (a b : nat) := pair (pair a b) 2.
Definition wn (a : nat) := pair a 3.
Definition wal (x a : nat) := pair (pair x a) 4.
Definition wex (x a : nat) := wn (wal x (wn a)).
Definition wa (a b : nat) := wn (wim a (wn b)).

Lemma code_Wel_v0_v0 : code (Wel v0 v0) = 1.
Proof. reflexivity. Qed.
