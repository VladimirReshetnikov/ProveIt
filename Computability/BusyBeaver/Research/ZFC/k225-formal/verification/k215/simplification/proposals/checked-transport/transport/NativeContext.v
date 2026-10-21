From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia.
Import ListNotations.

(** Exact native-label semantics: two infinite binary streams around the head.
    This representation gives definitional whole-tape equality, without
    functional extensionality or quotient axioms. *)
CoInductive stream : Type := Cons : bool -> stream -> stream.
Definition hd (s : stream) := match s with Cons b _ => b end.
Definition tl (s : stream) := match s with Cons _ t => t end.
Inductive dir := L | R.
Inductive action := A : bool -> dir -> nat -> action.
Inductive config := C : nat -> stream -> bool -> stream -> config.
Definition state (c : config) := match c with C q _ _ _ => q end.
Definition machine := nat -> bool -> option action.
Definition act (a : action) (c : config) : config :=
  match a, c with
  | A w L z, C _ (Cons b l) x r => C z l b (Cons w r)
  | A w R z, C _ l x (Cons b r) => C z (Cons w l) b r
  end.
Definition step (m : machine) (c : config) : config :=
  match c with C q l b r =>
    match m q b with Some a => act a c | None => c end
  end.
Fixpoint run (m : machine) (n : nat) (c : config) : config :=
  match n with 0 => c | S k => step m (run m k c) end.
Definition halts (m : machine) (c : config) :=
  exists n, state (run m n c) = 254.
Inductive entry := E : nat -> bool -> action -> entry.
Fixpoint lookup (q : nat) (b : bool) (es : list entry) : option action :=
  match es with
  | [] => None
  | E s x a :: rest =>
      if Nat.eqb q s && Bool.eqb b x then Some a else lookup q b rest
  end.

(* Literal old table inserted by generate_tables.py. *)
Definition old_rows : list entry := [
  E 0 false (A true R 94);
  E 0 true (A true R 0);
  E 1 false (A false L 1);
  E 1 true (A true L 2);
  E 2 false (A false L 3);
  E 2 true (A true L 2);
  E 3 false (A false L 5);
  E 3 true (A true L 2);
  E 4 false (A true R 6);
  E 4 true (A false L 4);
  E 5 false (A false L 9);
  E 5 true (A true L 2);
  E 6 false (A false R 6);
  E 6 true (A false R 10);
  E 7 false (A false R 86);
  E 7 true (A true R 205);
  E 8 false (A false R 14);
  E 8 true (A true R 13);
  E 9 false (A false L 15);
  E 9 true (A true L 2);
  E 10 false (A false L 16);
  E 10 true (A false R 10);
  E 11 false (A false L 26);
  E 11 true (A true R 115);
  E 12 false (A false R 19);
  E 12 true (A true R 20);
  E 13 false (A false L 91);
  E 13 true (A true L 31);
  E 14 false (A false L 11);
  E 14 true (A false R 22);
  E 15 false (A false L 23);
  E 15 true (A true L 2);
  E 16 false (A true L 1);
  E 16 true (A false L 1);
  E 17 false (A false R 24);
  E 17 true (A false R 32);
  E 18 false (A false R 218);
  E 18 true (A true R 217);
  E 19 false (A false R 28);
  E 19 true (A true R 29);
  E 20 false (A false R 30);
  E 20 true (A true R 31);
  E 21 false (A false R 24);
  E 21 true (A false R 60);
  E 22 false (A false R 33);
  E 22 true (A true R 22);
  E 23 false (A false L 34);
  E 23 true (A true L 2);
  E 24 false (A false L 35);
  E 24 true (A false R 0);
  E 25 false (A false R 36);
  E 25 true (A true R 25);
  E 26 false (A false R 37);
  E 26 true (A true R 38);
  E 27 false (A false R 39);
  E 27 true (A false L 40);
  E 28 false (A false R 41);
  E 28 true (A true R 42);
  E 29 false (A false R 43);
  E 29 true (A true R 44);
  E 30 false (A false R 45);
  E 30 true (A true R 46);
  E 31 false (A false R 21);
  E 31 true (A true R 47);
  E 32 false (A false R 48);
  E 32 true (A true R 32);
  E 33 false (A false R 32);
  E 33 true (A true R 33);
  E 34 false (A false L 50);
  E 34 true (A true L 2);
  E 35 false (A true R 35);
  E 35 true (A true L 1);
  E 36 false (A false R 51);
  E 36 true (A true R 36);
  E 37 false (A false R 17);
  E 37 true (A true R 117);
  E 38 false (A false R 13);
  E 38 true (A true R 53);
  E 39 false (A false L 11);
  E 39 true (A false R 36);
  E 40 false (A false L 4);
  E 40 true (A true L 54);
  E 41 false (A false R 24);
  E 41 true (A false R 25);
  E 42 false (A false R 13);
  E 42 true (A false L 16);
  E 43 false (A false R 56);
  E 43 true (A true R 57);
  E 44 false (A false R 58);
  E 44 true (A true R 59);
  E 45 false (A false R 24);
  E 45 true (A false R 55);
  E 46 false (A false R 61);
  E 46 true (A true R 62);
  E 47 false (A false R 63);
  E 47 true (A false L 16);
  E 48 false (A false R 25);
  E 48 true (A true R 48);
  E 49 false (A false L 35);
  E 49 true (A false R 64);
  E 50 false (A false L 75);
  E 50 true (A true L 2);
  E 51 false (A false R 16);
  E 51 true (A true R 51);
  E 52 false (A false R 154);
  E 52 true (A true R 150);
  E 53 false (A false R 68);
  E 53 true (A true R 69);
  E 54 false (A false L 40);
  E 54 true (A true L 54);
  E 55 false (A false R 22);
  E 55 true (A true R 55);
  E 56 false (A false L 11);
  E 56 true (A false R 51);
  E 57 false (A false R 61);
  E 57 true (A false L 16);
  E 58 false (A false R 70);
  E 58 true (A true R 71);
  E 59 false (A false R 62);
  E 59 true (A true R 72);
  E 60 false (A false R 55);
  E 60 true (A true R 60);
  E 61 false (A false R 49);
  E 61 true (A false R 25);
  E 62 false (A false L 28);
  E 62 true (A true L 73);
  E 63 false (A false L 123);
  E 63 true (A true L 30);
  E 64 false (A false R 74);
  E 64 true (A true R 64);
  E 65 false (A false R 99);
  E 65 true (A true R 157);
  E 66 false (A true R 198);
  E 66 true (A true L 54);
  E 67 false (A false R 151);
  E 67 true (A true R 152);
  E 68 false (A false R 77);
  E 68 true (A true R 254);
  E 69 false (A false L 213);
  E 69 true (A true R 31);
  E 70 false (A false R 41);
  E 70 true (A true R 63);
  E 71 false (A false L 91);
  E 71 true (A true R 80);
  E 72 false (A false R 56);
  E 72 true (A true L 81);
  E 73 false (A false R 82);
  E 73 true (A true R 83);
  E 74 false (A true R 0);
  E 74 true (A true R 64);
  E 75 false (A false R 75);
  E 75 true (A true R 84);
  E 76 false (A false L 152);
  E 76 true (A true L 148);
  E 77 false (A false R 87);
  E 77 true (A true R 88);
  E 78 false (A false R 100);
  E 78 true (A true R 225);
  E 80 false (A false R 91);
  E 80 true (A true L 138);
  E 81 false (A false L 111);
  E 81 true (A true R 57);
  E 82 false (A false R 49);
  E 82 true (A false R 33);
  E 83 false (A false R 93);
  E 83 true (A false L 42);
  E 84 false (A false R 95);
  E 84 true (A true R 214);
  E 85 false (A false R 98);
  E 85 true (A true R 12);
  E 86 false (A false R 90);
  E 86 true (A true R 99);
  E 87 false (A false R 301);
  E 87 true (A true R 21);
  E 88 false (A false R 122);
  E 88 true (A true R 103);
  E 89 false (A false R 157);
  E 89 true (A true R 116);
  E 90 false (A false R 105);
  E 90 true (A true R 106);
  E 91 false (A false R 82);
  E 91 true (A true R 81);
  E 92 false (A false R 104);
  E 92 true (A true R 212);
  E 93 false (A false R 108);
  E 93 true (A true R 109);
  E 94 false (A false R 66);
  E 94 true (A false R 0);
  E 95 false (A false R 27);
  E 95 true (A true R 110);
  E 96 false (A false R 196);
  E 96 true (A false L 302);
  E 97 false (A true L 113);
  E 97 true (A true L 97);
  E 98 false (A false R 19);
  E 98 true (A true R 114);
  E 99 false (A false R 61);
  E 99 true (A true R 61);
  E 100 false (A false R 69);
  E 100 true (A true R 142);
  E 101 false (A false R 67);
  E 101 true (A true R 204);
  E 103 false (A false R 108);
  E 103 true (A false L 302);
  E 104 false (A false R 123);
  E 104 true (A true R 124);
  E 105 false (A false R 72);
  E 105 true (A true R 59);
  E 106 false (A false R 58);
  E 106 true (A true R 125);
  E 107 false (A false R 21);
  E 107 true (A true R 126);
  E 108 false (A false R 21);
  E 108 true (A false L 10);
  E 109 false (A false R 62);
  E 109 true (A true R 42);
  E 110 false (A false R 127);
  E 110 true (A true R 8);
  E 111 false (A false R 104);
  E 111 true (A true R 128);
  E 112 false (A false R 157);
  E 112 true (A true R 200);
  E 113 false (A false L 302);
  E 113 true (A false L 97);
  E 114 false (A false R 130);
  E 114 true (A true R 107);
  E 115 false (A false R 76);
  E 115 true (A true R 185);
  E 116 false (A false R 172);
  E 116 true (A true R 194);
  E 117 false (A false R 134);
  E 117 true (A false L 302);
  E 118 false (A false R 155);
  E 118 true (A true R 153);
  E 119 false (A false R 167);
  E 119 true (A true R 217);
  E 122 false (A false L 137);
  E 122 true (A false L 1);
  E 123 false (A false R 39);
  E 123 true (A true R 73);
  E 124 false (A false R 62);
  E 124 true (A true R 138);
  E 125 false (A false R 62);
  E 125 true (A true R 139);
  E 126 false (A false R 71);
  E 126 true (A false L 16);
  E 127 false (A false R 14);
  E 127 true (A true R 138);
  E 128 false (A false R 21);
  E 128 true (A true R 141);
  E 129 false (A false R 154);
  E 129 true (A true R 189);
  E 130 false (A false R 144);
  E 130 true (A true L 20);
  E 131 false (A false R 136);
  E 131 true (A true R 193);
  E 132 false (A false R 222);
  E 132 true (A true R 180);
  E 133 false (A false R 76);
  E 133 true (A true R 187);
  E 134 false (A false R 163);
  E 134 true (A true R 12);
  E 135 false (A false R 221);
  E 135 true (A true R 164);
  E 136 false (A false R 12);
  E 136 true (A true R 148);
  E 137 false (A false R 30);
  E 137 true (A true R 70);
  E 138 false (A false R 39);
  E 138 true (A true L 130);
  E 139 false (A false R 160);
  E 139 true (A false L 16);
  E 141 false (A false R 161);
  E 141 true (A false L 16);
  E 142 false (A false R 90);
  E 142 true (A true R 143);
  E 143 false (A false R 213);
  E 143 true (A true R 147);
  E 144 false (A false R 24);
  E 144 true (A false R 48);
  E 145 false (A false R 147);
  E 145 true (A true R 193);
  E 146 false (A false R 78);
  E 146 true (A true R 96);
  E 147 false (A false R 98);
  E 147 true (A true R 166);
  E 148 false (A false R 186);
  E 148 true (A true R 173);
  E 149 false (A false R 12);
  E 149 true (A true R 166);
  E 150 false (A false R 90);
  E 150 true (A true L 173);
  E 151 false (A false R 90);
  E 151 true (A true R 165);
  E 152 false (A false L 159);
  E 152 true (A true L 170);
  E 153 false (A false R 86);
  E 153 true (A true R 90);
  E 154 false (A false R 166);
  E 154 true (A true R 12);
  E 155 false (A false R 85);
  E 155 true (A true R 150);
  E 156 false (A false R 171);
  E 156 true (A true R 176);
  E 157 false (A false L 67);
  E 157 true (A true L 148);
  E 158 false (A false R 155);
  E 158 true (A true R 220);
  E 159 false (A false R 166);
  E 159 true (A true R 118);
  E 160 false (A false R 99);
  E 160 true (A true R 99);
  E 161 false (A false R 49);
  E 161 true (A false R 32);
  E 162 false (A false R 174);
  E 162 true (A false L 302);
  E 163 false (A false R 17);
  E 163 true (A true R 162);
  E 164 false (A false L 201);
  E 164 true (A true R 98);
  E 165 false (A false R 176);
  E 165 true (A true R 190);
  E 166 false (A false R 19);
  E 166 true (A true R 179);
  E 167 false (A false R 184);
  E 167 true (A true R 172);
  E 168 false (A false R 166);
  E 168 true (A true R 98);
  E 169 false (A false R 131);
  E 169 true (A true R 171);
  E 170 false (A false R 99);
  E 170 true (A true R 169);
  E 171 false (A false L 7);
  E 171 true (A true R 149);
  E 172 false (A false L 112);
  E 172 true (A true R 184);
  E 173 false (A false R 153);
  E 173 true (A true R 182);
  E 174 false (A false R 11);
  E 174 true (A true R 135);
  E 176 false (A false R 168);
  E 176 true (A true R 150);
  E 177 false (A false R 203);
  E 177 true (A true R 172);
  E 178 false (A false R 189);
  E 178 true (A true R 189);
  E 179 false (A false R 194);
  E 179 true (A true R 128);
  E 180 false (A false R 152);
  E 180 true (A true R 172);
  E 181 false (A false R 177);
  E 181 true (A true R 89);
  E 182 false (A false R 76);
  E 182 true (A true R 61);
  E 184 false (A false R 152);
  E 184 true (A true R 90);
  E 185 false (A false R 168);
  E 185 true (A true R 146);
  E 186 false (A false R 147);
  E 186 true (A true R 86);
  E 187 false (A false R 186);
  E 187 true (A true R 76);
  E 188 false (A false R 151);
  E 188 true (A true R 181);
  E 189 false (A false R 149);
  E 189 true (A true L 156);
  E 190 false (A false R 99);
  E 190 true (A true R 52);
  E 193 false (A false R 176);
  E 193 true (A true R 52);
  E 194 false (A false R 17);
  E 194 true (A true L 137);
  E 195 false (A false R 150);
  E 195 true (A true R 188);
  E 196 false (A false R 77);
  E 196 true (A true R 122);
  E 197 false (A false R 109);
  E 197 true (A true R 130);
  E 198 false (A true L 40);
  E 198 true (A true L 113);
  E 199 false (A false R 180);
  E 199 true (A true R 166);
  E 200 false (A false R 157);
  E 200 true (A true R 119);
  E 201 false (A false R 195);
  E 201 true (A true R 196);
  E 203 false (A false R 207);
  E 203 true (A true R 101);
  E 204 false (A false R 153);
  E 204 true (A true R 215);
  E 205 false (A false R 164);
  E 205 true (A true R 206);
  E 206 false (A false R 186);
  E 206 true (A true R 199);
  E 207 false (A false R 65);
  E 207 true (A true R 7);
  E 209 false (A false R 157);
  E 209 true (A true R 133);
  E 210 false (A false R 171);
  E 210 true (A true R 201);
  E 211 false (A false R 159);
  E 211 true (A true R 129);
  E 212 false (A false R 107);
  E 212 true (A true R 98);
  E 213 false (A false R 92);
  E 213 true (A true R 90);
  E 214 false (A false R 111);
  E 214 true (A true R 26);
  E 215 false (A false R 223);
  E 215 true (A true R 112);
  E 216 false (A false R 157);
  E 216 true (A true R 178);
  E 217 false (A false R 216);
  E 217 true (A true R 167);
  E 218 false (A false R 147);
  E 218 true (A true R 145);
  E 220 false (A false R 211);
  E 220 true (A true R 18);
  E 221 false (A false R 213);
  E 221 true (A true R 28);
  E 222 false (A false R 170);
  E 222 true (A true R 209);
  E 223 false (A false R 132);
  E 223 true (A true R 158);
  E 225 false (A false R 210);
  E 225 true (A true R 197);
  E 301 false (A false R 45);
  E 301 true (A true R 103);
  E 302 false (A false L 4);
  E 302 true (A false L 302)].
Definition old : machine := fun q b => lookup q b old_rows.
Definition patch (q : nat) (b : bool) (a : action) :=
 if Nat.eqb q 13 && b then A true L 81 else
 if Nat.eqb q 27 && b then A false L 302 else
 if Nat.eqb q 83 && b then A false L 57 else
 if Nat.eqb q 156 && b then A true R 52 else
 if Nat.eqb q 198 && negb b then A true L 54 else a.
Definition new : machine := fun q b => option_map (patch q b) (old q b).

Lemma lookup_in q b es a : lookup q b es = Some a -> In (E q b a) es.
Proof.
 induction es as [|[s x z] es IH]; cbn; [discriminate|].
 destruct (Nat.eqb q s && Bool.eqb b x) eqn:H.
 - apply andb_true_iff in H as [Hs Hx].
   apply Nat.eqb_eq in Hs. apply Bool.eqb_prop in Hx.
   subst s x. intros Hz; inversion Hz; subst. left; reflexivity.
 - intros Hlookup; right; apply IH; exact Hlookup.
Qed.

(** A seven-state invariant replaces the two-edge history enumeration.
    Only states 38 and 42 are auxiliary; the other five are patch entries. *)
Definition inv (c : config) : Prop :=
 match c with C q l b r =>
 if Nat.eqb q 13 then hd l = true \/ (hd l = false /\ (hd (tl l) = true \/ b = false)) else
 if Nat.eqb q 27 then hd l = false else
 if Nat.eqb q 38 then hd l = true else
 if Nat.eqb q 42 then hd l = true \/ hd r = false else
 if Nat.eqb q 83 then hd l = true else
 if Nat.eqb q 156 then hd r = true else
 if Nat.eqb q 198 then hd l = true else True end.
Definition row_preserves (e : entry) : Prop :=
 match e with E q b a => forall l r,
 inv (C q l b r) -> inv (act a (C q l b r)) end.
Definition critical (e : entry) : bool :=
 match e with E _ _ (A _ _ q) =>
 (q =? 13) || (q =? 27) || (q =? 38) || (q =? 42) ||
 (q =? 83) || (q =? 156) || (q =? 198) end.
Lemma noncritical_preserves e : critical e = false -> row_preserves e.
Proof.
 destruct e as [q b [w d t]]. unfold critical.
 repeat rewrite orb_false_iff.
 intros [[[[[[H13 H27] H38] H42] H83] H156] H198].
 unfold row_preserves; intros l r H.
 destruct l as [x ll]; destruct r as [y rr]; destruct d;
 cbn [act inv]; rewrite H13,H27,H38,H42,H83,H156,H198; exact I.
Qed.
Definition critical_rows : list entry := [
 E 8 true (A true R 13);
 E 26 true (A true R 38);
 E 28 true (A true R 42);
 E 38 false (A false R 13);
 E 42 false (A false R 13);
 E 66 false (A true R 198);
 E 73 true (A true R 83);
 E 83 true (A false L 42);
 E 95 false (A false R 27);
 E 109 true (A true R 42);
 E 189 true (A true L 156)
].
Lemma critical_selection : filter critical old_rows = critical_rows.
Proof. vm_compute. reflexivity. Qed.
Lemma critical_rows_preserve : Forall row_preserves critical_rows.
Proof.
 unfold critical_rows.
 repeat (apply Forall_cons;
   [unfold row_preserves; intros l r H;
    destruct l as [a [b ll]]; destruct r as [c rr];
    cbn [inv act hd tl Nat.eqb] in *; intuition congruence|]).
 constructor.
Qed.
Lemma all_old_rows_preserve : Forall row_preserves old_rows.
Proof.
 rewrite Forall_forall. intros e He.
 destruct (critical e) eqn:Hcrit.
 - pose proof critical_rows_preserve as H.
   rewrite <- critical_selection, Forall_forall in H.
   apply H. apply filter_In. split; assumption.
 - apply noncritical_preserves; assumption.
Qed.
Lemma inv_step c : inv c -> inv (step old c).
Proof.
 destruct c as [q l b r]; intro H.
 unfold step. destruct (old q b) as [a|] eqn:Ha; [|exact H].
 pose proof all_old_rows_preserve as Hall.
 rewrite Forall_forall in Hall.
 apply (Hall (E q b a)); [apply lookup_in; exact Ha|exact H].
Qed.
Lemma inv_run n l b r : inv (run old n (C 0 l b r)).
Proof. induction n; [exact I|cbn; apply inv_step; exact IHn]. Qed.

(** Related configurations have the exact same tape and head. Seven transient
    cases account for all return rewrites; only zero31 needs three new steps. *)
Inductive related : config -> config -> Prop :=
 | same : forall c, related c c
 | zero31 : forall l r, related (C 31 (Cons true l) false r)
                                 (C 81 (Cons true l) false r)
 | one31 : forall l r, related (C 31 l true (Cons true r))
                                (C 81 l true (Cons true r))
 | one47 : forall l r, related (C 47 l true r) (C 57 l true r)
 | zero40 : forall l r, related (C 40 l false r) (C 302 l false r)
 | one42 : forall l r, related (C 42 l true r) (C 57 l true r)
 | one176 : forall l r, related (C 176 l true r) (C 52 l true r)
 | one40 : forall l r, related (C 40 l true r) (C 54 l true r).

Lemma patch_other q b : q <> 13 -> q <> 27 -> q <> 83 ->
 q <> 156 -> q <> 198 -> new q b = old q b.
Proof.
 intros H13 H27 H83 H156 H198.
 apply Nat.eqb_neq in H13. apply Nat.eqb_neq in H27.
 apply Nat.eqb_neq in H83. apply Nat.eqb_neq in H156.
 apply Nat.eqb_neq in H198.
 unfold new. destruct (old q b) as [a|]; [|reflexivity].
 change (Some (patch q b a) = Some a).
 unfold patch. rewrite H13,H27,H83,H156,H198. reflexivity.
Qed.

Lemma synchronized_step c : inv c -> related (step old c) (step new c).
Proof.
 destruct c as [q l b r]; intro H.
 destruct (Nat.eq_dec q 13) as [->|H13].
 { destruct b.
   + destruct l as [a [y ll]]. destruct a.
     * change (related (C 31 (Cons y ll) true (Cons true r))
                       (C 81 (Cons y ll) true (Cons true r))). apply one31.
     * cbn [inv hd tl Nat.eqb] in H.
       assert (y = true) by (intuition congruence). subst y.
       change (related (C 31 (Cons true ll) false (Cons true r))
                       (C 81 (Cons true ll) false (Cons true r))). apply zero31.
   + change (related (act (A false L 91) (C 13 l false r))
                     (act (A false L 91) (C 13 l false r))). apply same.
 }
 destruct (Nat.eq_dec q 27) as [->|H27].
 { destruct b.
   + destruct l as [a ll]. cbn [inv hd Nat.eqb] in H. subst a.
     change (related (C 40 ll false (Cons false r))
                     (C 302 ll false (Cons false r))). apply zero40.
   + change (related (act (A false R 39) (C 27 l false r))
                     (act (A false R 39) (C 27 l false r))). apply same.
 }
 destruct (Nat.eq_dec q 83) as [->|H83].
 { destruct b.
   + destruct l as [a ll]. cbn [inv hd Nat.eqb] in H. subst a.
     change (related (C 42 ll true (Cons false r))
                     (C 57 ll true (Cons false r))). apply one42.
   + change (related (act (A false R 93) (C 83 l false r))
                     (act (A false R 93) (C 83 l false r))). apply same.
 }
 destruct (Nat.eq_dec q 156) as [->|H156].
 { destruct b.
   + destruct r as [a rr]. cbn [inv hd Nat.eqb] in H. subst a.
     change (related (C 176 (Cons true l) true rr)
                     (C 52 (Cons true l) true rr)). apply one176.
   + change (related (act (A false R 171) (C 156 l false r))
                     (act (A false R 171) (C 156 l false r))). apply same.
 }
 destruct (Nat.eq_dec q 198) as [->|H198].
 { destruct b.
   + change (related (act (A true L 113) (C 198 l true r))
                     (act (A true L 113) (C 198 l true r))). apply same.
   + destruct l as [a ll]. cbn [inv hd Nat.eqb] in H. subst a.
     change (related (C 40 ll true (Cons true r))
                     (C 54 ll true (Cons true r))). apply one40.
 }
 unfold step. rewrite (patch_other q b H13 H27 H83 H156 H198).
   apply same.
Qed.

Lemma related_step c d : inv c -> related c d ->
 exists k, 1 <= k /\ k <= 3 /\ related (step old c) (run new k d).
Proof.
 intros Hinv Hr; destruct Hr.
 - exists 1; split; [lia|split; [lia|]]. apply synchronized_step; exact Hinv.
 - exists 3; split; [lia|split; [lia|]].
   change (related (act (A false R 21) (C 31 (Cons true l) false r))
                   (act (A false R 21) (C 31 (Cons true l) false r))). apply same.
 - exists 1; split; [lia|split; [lia|]].
   change (related (C 47 (Cons true l) true r) (C 57 (Cons true l) true r)).
   apply one47.
 - exists 1; split; [lia|split; [lia|]].
   change (related (act (A false L 16) (C 47 l true r))
                   (act (A false L 16) (C 47 l true r))). apply same.
 - exists 1; split; [lia|split; [lia|]].
   change (related (act (A false L 4) (C 40 l false r))
                   (act (A false L 4) (C 40 l false r))). apply same.
 - exists 1; split; [lia|split; [lia|]].
   change (related (act (A false L 16) (C 42 l true r))
                   (act (A false L 16) (C 42 l true r))). apply same.
 - exists 1; split; [lia|split; [lia|]].
   change (related (act (A true R 150) (C 176 l true r))
                   (act (A true R 150) (C 176 l true r))). apply same.
 - exists 1; split; [lia|split; [lia|]].
   change (related (act (A true L 54) (C 40 l true r))
                   (act (A true L 54) (C 40 l true r))). apply same.
Qed.

Lemma related_halt c d : related c d -> (state c = 254 <-> state d = 254).
Proof. intros H; destruct H; cbn [state]; try tauto; split; discriminate. Qed.
Lemma run_add m a b c : run m (a+b) c = run m b (run m a c).
Proof.
 induction b; [rewrite Nat.add_0_r; reflexivity|].
 rewrite Nat.add_succ_r. cbn. rewrite IHb. reflexivity.
Qed.
Lemma halt_step c : state c = 254 -> step new c = c.
Proof. destruct c as [q l b r]; cbn [state]; intros ->. destruct b; reflexivity. Qed.
Lemma halt_persists n k c : n <= k -> state (run new n c) = 254 ->
 state (run new k c) = 254.
Proof.
 intros Hnk H. assert (k = n + (k-n)) by lia. rewrite H0, run_add.
 generalize (k-n); intro j. induction j; [exact H|].
 cbn. rewrite halt_step by exact IHj. exact IHj.
Qed.
Theorem simulate l b r n : exists m,
 n <= m /\ m <= 3*n /\ related (run old n (C 0 l b r)) (run new m (C 0 l b r)).
Proof.
 induction n as [|n [m [Hlo [Hhi HR]]]].
 - exists 0. split; [lia|split; [lia|apply same]].
 - destruct (related_step _ _ (inv_run n l b r) HR) as [k [Hk [Hkk Hrel]]].
   exists (m+k). split; [lia|split; [lia|]].
   rewrite run_add. exact Hrel.
Qed.
Theorem context_halts_iff l b r :
 halts old (C 0 l b r) <-> halts new (C 0 l b r).
Proof.
 split; intros [n H]; destruct (simulate l b r n) as [m [Hlo [Hhi HR]]].
 - exists m. apply (proj1 (related_halt _ _ HR)); exact H.
 - exists n. apply (proj2 (related_halt _ _ HR)).
   apply (halt_persists n m); assumption.
Qed.
CoFixpoint zeros : stream := Cons false zeros.
Definition blank := C 0 zeros false zeros.
Corollary context_blank_halts_iff : halts old blank <-> halts new blank.
Proof. apply context_halts_iff. Qed.
Corollary context_blank_nonhalts_iff : (~ halts old blank) <-> (~ halts new blank).
Proof. rewrite context_blank_halts_iff. tauto. Qed.
Print Assumptions context_halts_iff.
Print Assumptions context_blank_nonhalts_iff.
