(** Generated exact-table replay checks for the new 20-template q1/q2 family.
    These are symbolic local equations; the full endpoint is not rebuilt. *)
From Coq Require Import Lists.List Bool.Bool Arith.PeanoNat.
Require Import K215FrameStandalone.
Import ListNotations ExtractedK215Frame.
Module ConcreteK215Frames.
Definition table230 : list (bool * dir * nat * bool * dir * nat) := [
  (true, R, 94, true, R, 0);
  (false, L, 1, true, L, 2);
  (false, L, 3, true, L, 2);
  (false, L, 5, true, L, 2);
  (true, R, 6, false, L, 4);
  (false, L, 9, true, L, 2);
  (false, R, 6, false, R, 10);
  (false, R, 86, true, R, 205);
  (false, R, 14, true, R, 13);
  (false, L, 15, true, L, 2);
  (false, L, 16, false, R, 10);
  (false, L, 26, true, R, 115);
  (false, R, 19, true, R, 20);
  (false, L, 91, true, L, 31);
  (false, L, 11, false, R, 22);
  (false, L, 23, true, L, 2);
  (true, L, 1, false, L, 1);
  (false, R, 24, false, R, 32);
  (false, R, 218, true, R, 217);
  (false, R, 28, true, R, 29);
  (false, R, 30, true, R, 31);
  (false, R, 24, false, R, 60);
  (false, R, 33, true, R, 22);
  (false, L, 34, true, L, 2);
  (false, L, 35, false, R, 0);
  (false, R, 36, true, R, 25);
  (false, R, 37, true, R, 38);
  (false, R, 39, false, L, 40);
  (false, R, 41, true, R, 42);
  (false, R, 43, true, R, 44);
  (false, R, 45, true, R, 46);
  (false, R, 21, true, R, 47);
  (false, R, 48, true, R, 32);
  (false, R, 32, true, R, 33);
  (false, L, 50, true, L, 2);
  (true, R, 35, true, L, 1);
  (false, R, 51, true, R, 36);
  (false, R, 17, true, R, 117);
  (false, R, 13, true, R, 53);
  (false, L, 11, false, R, 36);
  (false, L, 4, true, L, 54);
  (false, R, 24, false, R, 25);
  (false, R, 13, false, L, 16);
  (false, R, 56, true, R, 57);
  (false, R, 58, true, R, 59);
  (false, R, 24, false, R, 55);
  (false, R, 61, true, R, 62);
  (false, R, 63, false, L, 16);
  (false, R, 25, true, R, 48);
  (false, L, 35, false, R, 64);
  (false, L, 75, true, L, 2);
  (false, R, 16, true, R, 51);
  (false, R, 154, true, R, 150);
  (false, R, 68, true, R, 69);
  (false, L, 40, true, L, 54);
  (false, R, 22, true, R, 55);
  (false, L, 11, false, R, 51);
  (false, R, 61, false, L, 16);
  (false, R, 70, true, R, 71);
  (false, R, 62, true, R, 72);
  (false, R, 55, true, R, 60);
  (false, R, 49, false, R, 25);
  (false, L, 28, true, L, 73);
  (false, L, 123, true, L, 30);
  (false, R, 74, true, R, 64);
  (false, R, 99, true, R, 157);
  (true, R, 198, true, L, 54);
  (false, R, 151, true, R, 152);
  (false, R, 77, true, R, 230);
  (false, L, 213, true, R, 31);
  (false, R, 41, true, R, 63);
  (false, L, 91, true, R, 80);
  (false, R, 56, true, L, 81);
  (false, R, 82, true, R, 83);
  (true, R, 0, true, R, 64);
  (false, R, 75, true, R, 84);
  (false, L, 152, true, L, 148);
  (false, R, 87, true, R, 88);
  (false, R, 100, true, R, 225);
  (false, R, 82, true, R, 62);
  (false, R, 91, true, L, 138);
  (false, L, 111, true, R, 57);
  (false, R, 49, false, R, 33);
  (false, R, 93, false, L, 42);
  (false, R, 95, true, R, 214);
  (false, R, 98, true, R, 12);
  (false, R, 90, true, R, 99);
  (false, R, 102, true, R, 21);
  (false, R, 122, true, R, 103);
  (false, R, 157, true, R, 116);
  (false, R, 105, true, R, 106);
  (false, R, 82, true, R, 81);
  (false, R, 104, true, R, 212);
  (false, R, 108, true, R, 109);
  (false, R, 66, false, R, 0);
  (false, R, 27, true, R, 110);
  (false, R, 196, false, L, 120);
  (true, L, 113, true, L, 97);
  (false, R, 19, true, R, 114);
  (false, R, 61, true, R, 61);
  (false, R, 69, true, R, 142);
  (false, R, 67, true, R, 204);
  (false, R, 45, true, R, 103);
  (false, R, 108, false, L, 120);
  (false, R, 123, true, R, 124);
  (false, R, 72, true, R, 59);
  (false, R, 58, true, R, 125);
  (false, R, 21, true, R, 126);
  (false, R, 21, false, L, 10);
  (false, R, 62, true, R, 42);
  (false, R, 127, true, R, 8);
  (false, R, 104, true, R, 128);
  (false, R, 157, true, R, 200);
  (false, L, 120, false, L, 97);
  (false, R, 130, true, R, 107);
  (false, R, 76, true, R, 185);
  (false, R, 172, true, R, 194);
  (false, R, 134, false, L, 120);
  (false, R, 155, true, R, 153);
  (false, R, 167, true, R, 217);
  (false, L, 4, false, L, 120);
  (false, R, 31, true, R, 63);
  (false, L, 137, false, L, 1);
  (false, R, 39, true, R, 73);
  (false, R, 62, true, R, 138);
  (false, R, 62, true, R, 139);
  (false, R, 71, false, L, 16);
  (false, R, 14, true, R, 138);
  (false, R, 21, true, R, 141);
  (false, R, 154, true, R, 189);
  (false, R, 144, true, L, 20);
  (false, R, 136, true, R, 193);
  (false, R, 222, true, R, 180);
  (false, R, 76, true, R, 187);
  (false, R, 163, true, R, 12);
  (false, R, 221, true, R, 164);
  (false, R, 12, true, R, 148);
  (false, R, 30, true, R, 70);
  (false, R, 39, true, L, 130);
  (false, R, 160, false, L, 16);
  (false, R, 49, false, R, 48);
  (false, R, 161, false, L, 16);
  (false, R, 90, true, R, 143);
  (false, R, 213, true, R, 147);
  (false, R, 24, false, R, 48);
  (false, R, 147, true, R, 193);
  (false, R, 78, true, R, 96);
  (false, R, 98, true, R, 166);
  (false, R, 186, true, R, 173);
  (false, R, 12, true, R, 166);
  (false, R, 90, true, L, 173);
  (false, R, 90, true, R, 165);
  (false, L, 159, true, L, 170);
  (false, R, 86, true, R, 90);
  (false, R, 166, true, R, 12);
  (false, R, 85, true, R, 150);
  (false, R, 171, true, R, 176);
  (false, L, 67, true, L, 148);
  (false, R, 155, true, R, 220);
  (false, R, 166, true, R, 118);
  (false, R, 99, true, R, 99);
  (false, R, 49, false, R, 32);
  (false, R, 174, false, L, 120);
  (false, R, 17, true, R, 162);
  (false, L, 201, true, R, 98);
  (false, R, 176, true, R, 190);
  (false, R, 19, true, R, 179);
  (false, R, 184, true, R, 172);
  (false, R, 166, true, R, 98);
  (false, R, 131, true, R, 171);
  (false, R, 99, true, R, 169);
  (false, L, 7, true, R, 149);
  (false, L, 112, true, R, 184);
  (false, R, 153, true, R, 182);
  (false, R, 11, true, R, 135);
  (false, L, 76, true, R, 61);
  (false, R, 168, true, R, 150);
  (false, R, 203, true, R, 172);
  (false, R, 189, true, R, 189);
  (false, R, 194, true, R, 128);
  (false, R, 152, true, R, 172);
  (false, R, 177, true, R, 89);
  (false, R, 76, true, R, 61);
  (false, R, 150, true, R, 98);
  (false, R, 152, true, R, 90);
  (false, R, 168, true, R, 146);
  (false, R, 147, true, R, 86);
  (false, R, 186, true, R, 76);
  (false, R, 151, true, R, 181);
  (false, R, 149, true, L, 156);
  (false, R, 99, true, R, 52);
  (false, R, 166, true, R, 182);
  (false, R, 172, true, R, 194);
  (false, R, 176, true, R, 52);
  (false, R, 17, true, L, 137);
  (false, R, 150, true, R, 188);
  (false, R, 77, true, R, 122);
  (false, R, 109, true, R, 130);
  (true, L, 40, true, L, 113);
  (false, R, 180, true, R, 166);
  (false, R, 157, true, R, 119);
  (false, R, 195, true, R, 196);
  (false, R, 201, true, R, 151);
  (false, R, 207, true, R, 101);
  (false, R, 153, true, R, 215);
  (false, R, 164, true, R, 206);
  (false, R, 186, true, R, 199);
  (false, R, 65, true, R, 7);
  (false, R, 182, true, R, 199);
  (false, R, 157, true, R, 133);
  (false, R, 171, true, R, 201);
  (false, R, 159, true, R, 129);
  (false, R, 107, true, R, 98);
  (false, R, 92, true, R, 90);
  (false, R, 111, true, R, 26);
  (false, R, 223, true, R, 112);
  (false, R, 157, true, R, 178);
  (false, R, 216, true, R, 167);
  (false, R, 147, true, R, 145);
  (false, R, 214, true, R, 218);
  (false, R, 211, true, R, 18);
  (false, R, 213, true, R, 28);
  (false, R, 170, true, R, 209);
  (false, R, 132, true, R, 158);
  (false, R, 155, true, R, 159);
  (false, R, 210, true, R, 197);
  (false, R, 224, true, R, 225);
  (false, R, 223, true, R, 226);
  (false, R, 211, true, R, 227);
  (false, R, 204, true, R, 228)
].

Definition tmn (q : nat) (s : bool) : option (bool * dir * nat) :=
  if (Nat.eqb q 79 || Nat.eqb q 121 || Nat.eqb q 140 || Nat.eqb q 175 || Nat.eqb q 183 || Nat.eqb q 191 || Nat.eqb q 192 || Nat.eqb q 202 || Nat.eqb q 208 || Nat.eqb q 219 || Nat.eqb q 224 || Nat.eqb q 226 || Nat.eqb q 227 || Nat.eqb q 228 || Nat.eqb q 229)%bool then None else
  match nth_error table230 q with
  | None => None
  | Some (w0, d0, n0, w1, d1, n1) => if s then Some (w1, d1, n1) else Some (w0, d0, n0)
  end.


Definition start0 : sconf := (62, false, [(SB true); (SB true)], [(SB true); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Definition finish0 : sconf := (1, true, [], [(SB false); (SB false); (SB false); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Lemma local0 : run_local tmn 8 None start0 = Some (finish0, true).
Proof. vm_compute. reflexivity. Qed.
Lemma framed0 : forall frame,
  run_local tmn 8 None (add_left frame start0) =
    Some (add_left frame finish0, true).
Proof. intro frame. apply run_local_add_left. exact local0. Qed.
Definition start1 : sconf := (13, false, [(SB true)], [(SB true); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Definition finish1 : sconf := (1, true, [], [(SB false); (SB false); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Lemma local1 : run_local tmn 6 None start1 = Some (finish1, true).
Proof. vm_compute. reflexivity. Qed.
Lemma framed1 : forall frame,
  run_local tmn 6 None (add_left frame start1) =
    Some (add_left frame finish1, true).
Proof. intro frame. apply run_local_add_left. exact local1. Qed.
Definition start2 : sconf := (108, false, [(SB false); (SB false)], [(SB true); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Definition finish2 : sconf := (1, true, [], [(SB true); (SB false); (SB false); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Lemma local2 : run_local tmn 5 None start2 = Some (finish2, true).
Proof. vm_compute. reflexivity. Qed.
Lemma framed2 : forall frame,
  run_local tmn 5 None (add_left frame start2) =
    Some (add_left frame finish2, true).
Proof. intro frame. apply run_local_add_left. exact local2. Qed.
Definition start3 : sconf := (42, false, [(SB true)], [(SB true); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Definition finish3 : sconf := (1, true, [], [(SB false); (SB false); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Lemma local3 : run_local tmn 3 None start3 = Some (finish3, true).
Proof. vm_compute. reflexivity. Qed.
Lemma framed3 : forall frame,
  run_local tmn 3 None (add_left frame start3) =
    Some (add_left frame finish3, true).
Proof. intro frame. apply run_local_add_left. exact local3. Qed.
Definition start4 : sconf := (83, false, [(SB true); (SB true)], [(SB true); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Definition finish4 : sconf := (1, true, [], [(SB false); (SB false); (SB false); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Lemma local4 : run_local tmn 5 None start4 = Some (finish4, true).
Proof. vm_compute. reflexivity. Qed.
Lemma framed4 : forall frame,
  run_local tmn 5 None (add_left frame start4) =
    Some (add_left frame finish4, true).
Proof. intro frame. apply run_local_add_left. exact local4. Qed.
Definition start5 : sconf := (138, false, [(SB true); (SB true)], [(SB true); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Definition finish5 : sconf := (2, true, [], [(SB true); (SB false); (SB false); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Lemma local5 : run_local tmn 11 None start5 = Some (finish5, true).
Proof. vm_compute. reflexivity. Qed.
Lemma framed5 : forall frame,
  run_local tmn 11 None (add_left frame start5) =
    Some (add_left frame finish5, true).
Proof. intro frame. apply run_local_add_left. exact local5. Qed.
Definition start6 : sconf := (141, false, [(SB true)], [(SB true); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Definition finish6 : sconf := (1, true, [], [(SB false); (SB false); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Lemma local6 : run_local tmn 3 None start6 = Some (finish6, true).
Proof. vm_compute. reflexivity. Qed.
Lemma framed6 : forall frame,
  run_local tmn 3 None (add_left frame start6) =
    Some (add_left frame finish6, true).
Proof. intro frame. apply run_local_add_left. exact local6. Qed.
Definition start7 : sconf := (57, false, [(SB true)], [(SB true); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Definition finish7 : sconf := (1, true, [], [(SB false); (SB false); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Lemma local7 : run_local tmn 3 None start7 = Some (finish7, true).
Proof. vm_compute. reflexivity. Qed.
Lemma framed7 : forall frame,
  run_local tmn 3 None (add_left frame start7) =
    Some (add_left frame finish7, true).
Proof. intro frame. apply run_local_add_left. exact local7. Qed.
Definition start8 : sconf := (80, false, [(SB true); (SB true); (SB false)], [(SB true); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Definition finish8 : sconf := (1, true, [], [(SB false); (SB false); (SB false); (SB false); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Lemma local8 : run_local tmn 19 None start8 = Some (finish8, true).
Proof. vm_compute. reflexivity. Qed.
Lemma framed8 : forall frame,
  run_local tmn 19 None (add_left frame start8) =
    Some (add_left frame finish8, true).
Proof. intro frame. apply run_local_add_left. exact local8. Qed.
Definition start9 : sconf := (72, false, [(SB true)], [(SB true); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Definition finish9 : sconf := (1, true, [], [(SB false); (SB false); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Lemma local9 : run_local tmn 6 None start9 = Some (finish9, true).
Proof. vm_compute. reflexivity. Qed.
Lemma framed9 : forall frame,
  run_local tmn 6 None (add_left frame start9) =
    Some (add_left frame finish9, true).
Proof. intro frame. apply run_local_add_left. exact local9. Qed.
Definition start10 : sconf := (126, false, [(SB true)], [(SB true); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Definition finish10 : sconf := (1, true, [], [(SB false); (SB false); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Lemma local10 : run_local tmn 3 None start10 = Some (finish10, true).
Proof. vm_compute. reflexivity. Qed.
Lemma framed10 : forall frame,
  run_local tmn 3 None (add_left frame start10) =
    Some (add_left frame finish10, true).
Proof. intro frame. apply run_local_add_left. exact local10. Qed.
Definition start11 : sconf := (47, false, [(SB true)], [(SB true); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Definition finish11 : sconf := (1, true, [], [(SB false); (SB false); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Lemma local11 : run_local tmn 3 None start11 = Some (finish11, true).
Proof. vm_compute. reflexivity. Qed.
Lemma framed11 : forall frame,
  run_local tmn 3 None (add_left frame start11) =
    Some (add_left frame finish11, true).
Proof. intro frame. apply run_local_add_left. exact local11. Qed.
Definition start12 : sconf := (139, false, [(SB true)], [(SB true); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Definition finish12 : sconf := (1, true, [], [(SB false); (SB false); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Lemma local12 : run_local tmn 3 None start12 = Some (finish12, true).
Proof. vm_compute. reflexivity. Qed.
Lemma framed12 : forall frame,
  run_local tmn 3 None (add_left frame start12) =
    Some (add_left frame finish12, true).
Proof. intro frame. apply run_local_add_left. exact local12. Qed.
Definition start13 : sconf := (108, false, [(SB false); (SB true)], [(SB true); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Definition finish13 : sconf := (1, true, [], [(SB false); (SB false); (SB false); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Lemma local13 : run_local tmn 5 None start13 = Some (finish13, true).
Proof. vm_compute. reflexivity. Qed.
Lemma framed13 : forall frame,
  run_local tmn 5 None (add_left frame start13) =
    Some (add_left frame finish13, true).
Proof. intro frame. apply run_local_add_left. exact local13. Qed.
Definition start14 : sconf := (103, false, [(SB true); (SB false); (SB false)], [(SB true); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Definition finish14 : sconf := (2, true, [], [(SB true); (SB false); (SB false); (SB false); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Lemma local14 : run_local tmn 24 None start14 = Some (finish14, true).
Proof. vm_compute. reflexivity. Qed.
Lemma framed14 : forall frame,
  run_local tmn 24 None (add_left frame start14) =
    Some (add_left frame finish14, true).
Proof. intro frame. apply run_local_add_left. exact local14. Qed.
Definition start15 : sconf := (122, false, [], [(SB true); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Definition finish15 : sconf := (1, true, [], [(SB false); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Lemma local15 : run_local tmn 1 None start15 = Some (finish15, true).
Proof. vm_compute. reflexivity. Qed.
Lemma framed15 : forall frame,
  run_local tmn 1 None (add_left frame start15) =
    Some (add_left frame finish15, true).
Proof. intro frame. apply run_local_add_left. exact local15. Qed.
Definition start16 : sconf := (103, false, [(SB true); (SB true); (SB false); (SB true); (SB true); (SB false)], [(SB true); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Definition finish16 : sconf := (2, true, [], [(SB true); (SB false); (SB false); (SB false); (SB false); (SB false); (SB false); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Lemma local16 : run_local tmn 39 None start16 = Some (finish16, true).
Proof. vm_compute. reflexivity. Qed.
Lemma framed16 : forall frame,
  run_local tmn 39 None (add_left frame start16) =
    Some (add_left frame finish16, true).
Proof. intro frame. apply run_local_add_left. exact local16. Qed.
Definition start17 : sconf := (103, false, [(SB true); (SB true); (SB false); (SB false)], [(SB true); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Definition finish17 : sconf := (2, true, [], [(SB true); (SB false); (SB false); (SB false); (SB false); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Lemma local17 : run_local tmn 29 None start17 = Some (finish17, true).
Proof. vm_compute. reflexivity. Qed.
Lemma framed17 : forall frame,
  run_local tmn 29 None (add_left frame start17) =
    Some (add_left frame finish17, true).
Proof. intro frame. apply run_local_add_left. exact local17. Qed.
Definition start18 : sconf := (96, false, [(SB true); (SB true); (SB true); (SB true); (SB false); (SB false)], [(SB true); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Definition finish18 : sconf := (2, true, [], [(SB true); (SB false); (SB false); (SB false); (SB false); (SB false); (SB false); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Lemma local18 : run_local tmn 39 None start18 = Some (finish18, true).
Proof. vm_compute. reflexivity. Qed.
Lemma framed18 : forall frame,
  run_local tmn 39 None (add_left frame start18) =
    Some (add_left frame finish18, true).
Proof. intro frame. apply run_local_add_left. exact local18. Qed.
Definition start19 : sconf := (162, false, [(SB true); (SB false); (SB false)], [(SB true); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Definition finish19 : sconf := (2, true, [], [(SB true); (SB false); (SB false); (SB false); (SR false 1 16); (SB true); (SBox (BPlain FNone))]).
Lemma local19 : run_local tmn 24 None start19 = Some (finish19, true).
Proof. vm_compute. reflexivity. Qed.
Lemma framed19 : forall frame,
  run_local tmn 24 None (add_left frame start19) =
    Some (add_left frame finish19, true).
Proof. intro frame. apply run_local_add_left. exact local19. Qed.

Print Assumptions framed0.
Print Assumptions framed1.
Print Assumptions framed2.
Print Assumptions framed3.
Print Assumptions framed4.
Print Assumptions framed5.
Print Assumptions framed6.
Print Assumptions framed7.
Print Assumptions framed8.
Print Assumptions framed9.
Print Assumptions framed10.
Print Assumptions framed11.
Print Assumptions framed12.
Print Assumptions framed13.
Print Assumptions framed14.
Print Assumptions framed15.
Print Assumptions framed16.
Print Assumptions framed17.
Print Assumptions framed18.
Print Assumptions framed19.
End ConcreteK215Frames.
