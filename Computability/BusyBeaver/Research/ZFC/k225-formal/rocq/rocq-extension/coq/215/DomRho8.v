(** Compact replay of Source 149's dominated-rho8 certificate.
    Certificate SHA256: 3cf18a5fe9f187b50b79d97b84535ce9bf776305728b0cdfe17285e94f028452.
    Retained original nodes: 674; instructions: 780;
    symbolic DAG entries: 297. The generator is untrusted. *)

(** Generic, purely syntactic certificate soundness for dominated implication. *)
From Stdlib Require Import Arith Lia List Bool NArith.
From K230L Require Import Codes230.
Import ListNotations.

Record DomImp (T : nat -> Prop) : Prop := {
  dtruth : T 0;
  dmp : forall a b, T (wim a b) -> T a -> T b;
  drho8 : forall a b c u, u <= a -> T (rho8 a b c u) }.
Arguments dtruth {T} _.
Arguments dmp {T} _ _ _ _ _.
Arguments drho8 {T} _ _ _ _ _ _.

(** Implementation details stay qualified; the public interface is DomImp and rho8_all. *)
Module Certificate.

Inductive expr := Z | V (i : nat) | I (a b : expr).
(** This is the only normalization used by the certificate. Its semantic law
    below proves that the native alias wim 0 0 = 0 is respected. *)
Definition imp a b := match a,b with Z,Z => Z | _,_ => I a b end.
Fixpoint eval (v : nat -> nat) (a : expr) : nat :=
  match a with Z => 0 | V i => v i | I b c => wim (eval v b) (eval v c) end.
Lemma eval_imp v a b : eval v (imp a b) = wim (eval v a) (eval v b).
Proof. destruct a,b; reflexivity. Qed.

Fixpoint eqb (a b : expr) : bool :=
  match a,b with
  | Z,Z => true | V i,V j => Nat.eqb i j
  | I a b,I c d => eqb a c && eqb b d
  | _,_ => false end.
Lemma eqb_sound a b : eqb a b = true -> a = b.
Proof.
 revert b; induction a; intros b H; destruct b; simpl in H; try discriminate; auto.
 - apply Nat.eqb_eq in H. now subst.
 - apply andb_true_iff in H as [H1 H2]. now rewrite (IHa1 _ H1), (IHa2 _ H2).
Qed.

Fixpoint subst (env : list expr) (a : expr) : expr :=
 match a with Z => Z | V i => nth i env Z | I b c => imp (subst env b) (subst env c) end.
Lemma eval_subst v env a : eval v (subst env a) = eval (fun i => eval v (nth i env Z)) a.
Proof. induction a; simpl; auto. now rewrite eval_imp, IHa1, IHa2. Qed.

Fixpoint subterm (u a : expr) : bool :=
 eqb u a || match a with I b c => subterm u b || subterm u c | _ => false end.
Definition dominated u a := eqb u Z || subterm u a.
Lemma subterm_sound u a : subterm u a = true -> forall v, eval v u <= eval v a.
Proof.
 induction a; simpl; intros H v; apply orb_true_iff in H as [H|H].
 - apply eqb_sound in H. subst; simpl; lia.
 - discriminate.
 - apply eqb_sound in H. subst; simpl; lia.
 - discriminate.
 - apply eqb_sound in H. subst; simpl; lia.
 - apply orb_true_iff in H as [H|H]; simpl.
   + specialize (IHa1 H v). unfold wim. pose proof (P_ge_l (eval v a1) (eval v a2)). lia.
   + specialize (IHa2 H v). unfold wim. pose proof (P_ge_r (eval v a1) (eval v a2)). lia.
Qed.
Lemma dominated_sound u a : dominated u a = true -> forall v, eval v u <= eval v a.
Proof.
 unfold dominated. intros H v. apply orb_true_iff in H as [H|H].
 - apply eqb_sound in H. subst; simpl; lia.
 - now apply subterm_sound.
Qed.
Local Opaque wim.
Definition rho a b c u := imp (imp (imp c u) a) (imp (imp a c) (imp b c)).
Lemma eval_rho v a b c u : eval v (rho a b c u) = rho8 (eval v a) (eval v b) (eval v c) (eval v u).
Proof. unfold rho, rho8. repeat rewrite eval_imp. reflexivity. Qed.

(** The term table is a DAG: references are backward distances. Out-of-range
    indices mean truth, so malformed input cannot introduce an assumption. *)
Inductive term := TZero | TVar (i : nat) | TImp (a b : nat).
Definition term_expr (seen : list expr) (t : term) :=
 match t with TZero => Z | TVar i => V i | TImp a b => I (nth a seen Z) (nth b seen Z) end.
Definition decode (ts : list term) : list expr :=
 fold_left (fun seen t => term_expr seen t :: seen) ts [].

Definition get (xs : list expr) (i : nat) := nth i xs Z.
Inductive rule := Truth | Ax (a b c u : nat) | MP (major minor : nat) | Inst (parent : nat) (env : list nat).
(** Every instruction is sound, including malformed ones: a rejected axiom or
    detachment returns truth. Hence checking the final symbolic result suffices. *)
Definition derive (ts seen : list expr) (r : rule) : expr :=
 match r with
 | Truth => Z
 | Ax a b c u =>
   if dominated (get ts u) (get ts a)
   then rho (get ts a) (get ts b) (get ts c) (get ts u) else Z
 | MP major minor =>
   match get seen major with
   | I a b => if eqb a (get seen minor) then b else Z
   | _ => Z end
 | Inst p env => subst (map (get ts) env) (get seen p)
 end.
Fixpoint run (ts : list expr) (steps : list rule) (seen : list expr) : list expr :=
 match steps with [] => seen | s :: ss => run ts ss (derive ts seen s :: seen) end.
Definition check ts steps goal := eqb (get (run ts steps []) 0) goal.

Section Soundness.
Variable T : nat -> Prop.
Variable h : DomImp T.
Definition valid a := forall v, T (eval v a).
Lemma valid_truth : valid Z.
Proof. intros v; apply (dtruth h). Qed.
Lemma get_valid xs i : Forall valid xs -> valid (get xs i).
Proof.
 unfold get; intros H; revert i. induction H; intros [|i]; simpl; auto using valid_truth.
Qed.
Lemma inst_valid env a : valid a -> valid (subst env a).
Proof. intros H v; rewrite eval_subst; apply H. Qed.
Lemma derive_sound ts seen r : Forall valid seen -> valid (derive ts seen r).
Proof.
 intros Hs; destruct r; cbn [derive].
 - apply valid_truth.
 - destruct (dominated (get ts u) (get ts a)) eqn:Hd; [|apply valid_truth].
   intros v. rewrite eval_rho. apply (drho8 h). now apply dominated_sound.
 - pose proof (get_valid seen major Hs) as Hmaj.
   destruct (get seen major) as [|i|a b]; try apply valid_truth.
   destruct (eqb a (get seen minor)) eqn:He; [|apply valid_truth].
   apply eqb_sound in He. intros v. specialize (Hmaj v). cbn [eval] in Hmaj.
   rewrite He in Hmaj. exact (dmp h _ _ Hmaj (get_valid seen minor Hs v)).
 - apply inst_valid. now apply get_valid.
Qed.
Lemma run_sound ts steps seen : Forall valid seen -> Forall valid (run ts steps seen).
Proof.
 revert seen. induction steps as [|s ss IH]; intros seen Hs; simpl; [exact Hs|].
 apply IH. constructor; [now apply derive_sound|exact Hs].
Qed.
Theorem check_sound ts steps goal : check ts steps goal = true -> valid goal.
Proof.
 unfold check; intros H; apply eqb_sound in H; rewrite <- H.
 apply get_valid. apply run_sound. constructor.
Qed.
End Soundness.



Definition ti (a b : N) := TImp (N.to_nat a) (N.to_nat b).
Definition ax (a b c u : N) := Ax (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat u).
Definition mp (major minor : N) := MP (N.to_nat major) (N.to_nat minor).
Definition inst (parent : N) (env : list N) := Inst (N.to_nat parent) (map N.to_nat env).

Definition term_data : list term := [
TVar 0;
TVar 1;
ti 1 0;
ti 0 1;
ti 2 3;
TVar 2;
ti 0 5;
ti 1 5;
ti 5 0;
TVar 3;
ti 0 9;
ti 9 5;
ti 10 10;
TVar 5;
ti 6 12;
ti 0 7;
TVar 4;
TZero;
ti 17 0;
ti 1 18;
ti 0 15;
ti 19 3;
ti 4 20;
ti 0 15;
ti 11 22;
ti 24 24;
ti 23 25;
ti 0 20;
ti 27 16;
ti 19 27;
ti 18 20;
ti 0 25;
ti 29 26;
ti 21 31;
ti 32 22;
ti 6 33;
ti 28 26;
ti 0 20;
ti 37 32;
ti 37 0;
ti 39 0;
ti 35 24;
ti 32 0;
ti 38 42;
ti 27 34;
ti 39 35;
ti 41 40;
ti 37 41;
ti 1 0;
ti 48 0;
ti 17 2;
ti 0 50;
ti 35 51;
ti 25 43;
ti 4 37;
ti 9 49;
ti 25 11;
ti 56 0;
ti 0 56;
ti 58 49;
ti 0 54;
ti 58 15;
ti 9 52;
ti 0 17;
ti 2 0;
ti 38 59;
ti 0 65;
ti 0 56;
ti 34 58;
ti 68 0;
ti 0 68;
ti 32 70;
ti 70 69;
ti 67 55;
ti 62 35;
ti 72 0;
ti 74 0;
ti 0 75;
ti 0 3;
ti 4 2;
ti 4 0;
ti 77 5;
ti 0 80;
ti 0 81;
ti 80 0;
ti 0 82;
ti 0 83;
ti 1 0;
ti 3 1;
ti 0 4;
ti 0 2;
ti 3 2;
ti 10 5;
ti 8 0;
ti 0 9;
ti 0 8;
ti 9 2;
ti 4 0;
ti 14 5;
ti 16 15;
ti 18 16;
ti 0 19;
ti 0 2;
ti 3 2;
ti 19 20;
ti 0 101;
ti 0 102;
ti 1 0;
ti 3 1;
ti 0 4;
ti 0 2;
ti 3 2;
ti 30 5;
ti 8 0;
ti 0 9;
ti 0 8;
ti 9 2;
ti 4 0;
ti 34 5;
ti 12 37;
ti 35 15;
ti 117 16;
ti 0 118;
ti 0 2;
ti 3 2;
ti 48 43;
ti 0 124;
ti 0 125;
ti 44 0;
ti 0 127;
ti 0 47;
ti 5 0;
ti 3 0;
ti 0 4;
ti 0 3;
ti 4 2;
ti 4 0;
ti 9 5;
ti 11 10;
ti 13 11;
ti 0 14;
ti 0 2;
ti 3 2;
ti 60 14;
ti 143 68;
ti 63 0;
ti 145 0;
ti 143 0;
ti 0 144;
ti 0 3;
ti 4 2;
ti 4 0;
ti 149 148;
ti 152 149;
ti 0 153;
ti 0 2;
ti 3 2;
ti 118 81;
ti 83 0;
ti 83 158;
ti 131 121;
ti 0 149;
ti 0 150;
ti 134 0;
ti 0 163;
ti 0 164;
ti 5 0;
ti 3 0;
ti 0 4;
ti 0 3;
ti 4 2;
ti 4 0;
ti 9 5;
ti 9 10;
ti 0 145;
ti 0 146;
ti 15 0;
ti 3 0;
ti 0 4;
ti 0 3;
ti 4 2;
ti 4 0;
ti 19 5;
ti 7 22;
ti 109 23;
ti 0 173;
ti 0 174;
ti 24 0;
ti 0 176;
ti 0 27;
ti 5 0;
ti 3 0;
ti 0 4;
ti 0 3;
ti 4 2;
ti 4 0;
ti 9 5;
ti 35 9;
ti 195 37;
ti 196 160;
ti 39 161;
ti 0 1;
ti 173 2;
ti 1 0;
ti 175 0;
ti 4 0;
ti 0 5;
ti 0 3;
ti 4 2;
ti 4 0;
ti 49 8;
ti 50 8;
ti 8 0;
ti 0 52;
ti 0 12;
ti 4 0;
ti 0 55;
ti 0 56;
ti 0 4;
ti 17 6;
ti 21 17;
ti 9 18;
ti 0 1;
ti 62 2;
ti 1 0;
ti 64 0;
ti 4 0;
ti 0 5;
ti 0 3;
ti 4 2;
ti 4 0;
ti 19 8;
ti 20 8;
ti 8 0;
ti 0 22;
ti 0 12;
ti 4 0;
ti 0 25;
ti 0 26;
ti 0 4;
ti 17 6;
ti 42 80;
ti 0 21;
ti 0 82;
ti 0 83;
ti 3 0;
ti 0 47;
ti 0 48;
ti 5 0;
ti 3 0;
ti 0 4;
ti 0 3;
ti 4 2;
ti 4 0;
ti 9 5;
ti 9 10;
ti 0 14;
ti 0 15;
ti 15 0;
ti 3 0;
ti 0 4;
ti 0 3;
ti 4 2;
ti 4 0;
ti 19 5;
ti 7 22;
ti 42 23;
ti 0 106;
ti 0 107;
ti 24 0;
ti 0 109;
ti 0 27;
ti 5 0;
ti 3 0;
ti 0 4;
ti 0 3;
ti 4 2;
ti 4 0;
ti 9 5;
ti 35 9;
ti 277 59;
ti 38 0;
ti 279 0;
ti 41 0;
ti 0 42;
ti 0 3;
ti 4 2;
ti 4 0;
ti 88 67;
ti 86 0;
ti 69 287;
ti 245 290;
ti 253 236;
ti 254 287;
ti 1 0;
ti 256 283;
ti 2 0].
Definition proof_data : list rule := [
ax 295 291 296 295;
ax 289 287 296 295;
ax 285 287 296 295;
inst 1 [284; 294; 293; 291]%N;
inst 2 [295; 295; 296; 296]%N;
mp 1 0;
inst 4 [281; 284; 296; 287]%N;
inst 1 [291; 295; 296]%N;
mp 1 0;
ax 295 291 296 279;
inst 0 [278; 276; 291]%N;
inst 1 [296; 279; 295]%N;
mp 1 0;
inst 11 [273; 275; 296; 287]%N;
inst 1 [295; 291; 296]%N;
mp 1 0;
inst 0 [279; 279; 279; 296]%N;
inst 4 [279; 279; 279]%N;
mp 1 0;
inst 9 [296; 279; 295]%N;
inst 1 [278]%N;
mp 1 0;
inst 13 [279; 295; 295; 296]%N;
inst 1 [284; 272]%N;
mp 1 0;
Truth;
inst 1 [279; 296]%N;
inst 1 []%N;
mp 1 0;
inst 27 [271; 296; 296; 295]%N;
inst 1 [296]%N;
mp 1 0;
inst 0 [284; 296]%N;
inst 1 [295; 284]%N;
mp 1 0;
inst 0 [279; 296]%N;
inst 10 []%N;
mp 1 0;
inst 6 [295; 296]%N;
inst 1 [295]%N;
mp 1 0;
inst 0 [279; 296]%N;
inst 16 []%N;
mp 1 0;
inst 42 [296; 295; 296; 291]%N;
inst 1 [294]%N;
mp 1 0;
inst 45 [285; 295; 296; 287]%N;
inst 1 [295; 291; 296]%N;
mp 1 0;
inst 48 [267; 285; 296; 280]%N;
inst 1 [287; 295; 291; 296]%N;
mp 1 0;
inst 0 [223; 285; 287; 265; 296]%N;
inst 44 [291; 266; 295]%N;
mp 1 0;
inst 0 [279; 296; 295; 291]%N;
inst 31 []%N;
mp 1 0;
inst 57 [264; 295; 296; 287]%N;
inst 1 [296; 295; 291]%N;
mp 1 0;
inst 0 [285; 295; 295; 296]%N;
inst 16 [295; 291; 263]%N;
mp 1 0;
inst 0 [279; 296; 295]%N;
inst 40 []%N;
mp 1 0;
inst 67 [294; 296; 291]%N;
inst 1 [296; 295]%N;
mp 1 0;
inst 0 [262; 285; 296]%N;
inst 1 [295; 291; 262]%N;
mp 1 0;
inst 0 [279; 296; 295]%N;
inst 49 []%N;
mp 1 0;
inst 75 [295; 285; 296; 287]%N;
inst 7 [295; 291; 296]%N;
mp 1 0;
inst 3 [261; 295]%N;
inst 1 [296; 295; 291; 261]%N;
mp 1 0;
ax 259 283 296 295;
inst 83 [257; 296; 287]%N;
inst 2 [295; 296; 291]%N;
mp 1 0;
inst 34 [296; 295; 291; 287; 280]%N;
inst 11 [256; 257]%N;
inst 2 [296; 295; 291; 256]%N;
mp 1 0;
inst 89 [254; 285; 296; 283]%N;
inst 4 [287; 291; 280; 295; 296]%N;
mp 1 0;
inst 3 [253; 294; 295]%N;
inst 94 [295; 296; 253]%N;
mp 1 0;
inst 3 [267; 295; 291; 266; 287; 296]%N;
inst 95 [287; 295; 291; 291]%N;
mp 1 0;
inst 0 [279; 296; 295; 291]%N;
inst 1 [279; 279; 279; 279]%N;
mp 1 0;
inst 0 [292; 296; 288]%N;
inst 103 [295; 296; 291]%N;
mp 1 0;
inst 3 [295; 296; 248]%N;
inst 1 [292; 291; 287]%N;
mp 1 0;
inst 25 [296; 295; 296; 291; 249; 280]%N;
inst 4 [294; 291; 287]%N;
mp 1 0;
inst 6 [269; 287; 280]%N;
inst 66 [296; 295; 291]%N;
mp 1 0;
inst 38 [245; 296]%N;
inst 4 [296; 295; 291; 287; 245]%N;
mp 1 0;
inst 117 [246; 296; 280]%N;
inst 1 [296; 295; 291; 287]%N;
mp 1 0;
inst 24 [296; 288]%N;
inst 16 [296; 295; 291]%N;
mp 1 0;
inst 18 [247; 280; 283]%N;
inst 16 [296; 295; 291; 287]%N;
mp 1 0;
inst 50 [243; 287]%N;
inst 13 [296; 295; 291; 287; 243]%N;
mp 1 0;
inst 53 [242; 280]%N;
inst 4 [296; 295; 291; 287; 280; 242]%N;
mp 1 0;
inst 131 [295; 240; 296; 283]%N;
inst 13 [295; 291; 287; 280; 296]%N;
mp 1 0;
inst 59 [238; 295]%N;
inst 1 [296; 295; 291; 287; 280; 238]%N;
mp 1 0;
inst 15 [296; 285; 236]%N;
inst 1 [268; 296; 287; 291; 295]%N;
mp 1 0;
inst 9 [296; 280; 287; 291; 232]%N;
inst 1 [296; 234; 251; 295]%N;
mp 1 0;
inst 15 [296; 295; 287; 229]%N;
inst 4 [270; 287; 296; 291]%N;
mp 1 0;
inst 3 [228; 295; 280; 295; 296]%N;
inst 1 [295; 291; 287; 280]%N;
mp 1 0;
inst 74 [226; 295]%N;
inst 1 [296; 295; 291; 287; 226]%N;
mp 1 0;
inst 30 [296; 295; 225]%N;
inst 1 [294; 296; 291; 295]%N;
mp 1 0;
inst 155 [224; 294; 293; 291]%N;
inst 157 [295; 294; 296]%N;
mp 1 0;
inst 0 [291; 295; 296]%N;
inst 114 [289; 295; 295]%N;
mp 1 0;
inst 0 [279; 296; 295]%N;
inst 138 []%N;
mp 1 0;
inst 60 [295; 291; 296]%N;
inst 10 [295; 222; 221]%N;
mp 0 1;
inst 119 [294; 222; 220; 216]%N;
inst 93 [216; 217]%N;
mp 0 1;
inst 171 [221; 217; 295]%N;
mp 0 1;
inst 115 [222; 220; 221]%N;
mp 0 1;
ax 222 218 220 295;
inst 90 [218; 217; 220; 279]%N;
mp 0 1;
mp 0 153;
mp 0 4;
mp 0 12;
inst 76 [212; 294; 211]%N;
inst 26 [212; 209; 210]%N;
mp 0 1;
inst 123 [212; 294; 294; 212]%N;
ax 209 206 208 212;
inst 100 [206; 205; 208; 279]%N;
mp 0 1;
mp 0 163;
mp 0 4;
mp 0 6;
inst 35 [212; 210; 204]%N;
mp 0 1;
inst 144 [215; 210; 203; 199]%N;
inst 118 [199; 200]%N;
mp 0 1;
inst 196 [204; 200; 212]%N;
mp 0 1;
inst 140 [210; 203; 204]%N;
mp 0 1;
ax 210 201 203 212;
inst 115 [201; 200; 203; 279]%N;
mp 0 1;
mp 0 178;
mp 0 4;
mp 0 12;
inst 104 [293; 213; 204]%N;
mp 0 1;
inst 103 [215; 295; 214]%N;
inst 53 [215; 197; 213]%N;
mp 0 1;
inst 150 [215; 295; 295; 215]%N;
ax 197 194 196 215;
inst 127 [194; 193; 196; 279]%N;
mp 0 1;
mp 0 190;
mp 0 4;
mp 0 6;
inst 62 [215; 213; 210]%N;
mp 0 1;
ax 213 198 204 215;
mp 0 1;
inst 146 [198; 204]%N;
mp 0 1;
mp 0 16;
inst 173 [293; 294; 222; 211; 204]%N;
inst 150 [204; 210]%N;
mp 0 1;
mp 0 3;
inst 106 [294; 295; 214]%N;
mp 0 1;
inst 126 [192; 293; 191]%N;
inst 76 [192; 189; 190]%N;
mp 0 1;
inst 173 [192; 293; 293; 192]%N;
ax 189 186 188 192;
inst 150 [186; 185; 188; 279]%N;
mp 0 1;
mp 0 213;
mp 0 4;
mp 0 6;
inst 85 [192; 190; 184]%N;
mp 0 1;
inst 194 [215; 190; 183; 179]%N;
inst 168 [179; 180]%N;
mp 0 1;
inst 246 [184; 180; 192]%N;
mp 0 1;
inst 190 [190; 183; 184]%N;
mp 0 1;
ax 190 181 183 192;
inst 165 [181; 180; 183; 279]%N;
mp 0 1;
mp 0 228;
mp 0 4;
mp 0 12;
inst 154 [212; 213; 184]%N;
mp 0 1;
inst 102 [215; 213; 190]%N;
mp 0 41;
ax 213 178 184 215;
mp 0 1;
inst 186 [178; 184]%N;
mp 0 1;
mp 0 6;
inst 216 [191; 293; 221; 177]%N;
inst 190 [177; 215]%N;
mp 0 1;
inst 268 [190; 215; 184]%N;
mp 0 1;
inst 194 [184; 190]%N;
mp 0 1;
mp 0 7;
inst 168 [293; 213; 212]%N;
inst 118 [293; 176; 192]%N;
mp 0 1;
inst 215 [293; 213; 213; 293]%N;
ax 176 173 175 293;
inst 192 [173; 172; 175; 279]%N;
mp 0 1;
mp 0 255;
mp 0 4;
mp 0 6;
inst 187 [293; 192]%N;
mp 0 1;
mp 0 12;
mp 0 55;
inst 182 [168; 295; 215]%N;
inst 132 [168; 166; 165]%N;
mp 0 1;
inst 241 [171; 166; 164; 160]%N;
inst 215 [160; 161]%N;
mp 0 1;
inst 293 [165; 161; 168]%N;
mp 0 1;
inst 237 [166; 164; 165]%N;
mp 0 1;
ax 166 162 164 168;
inst 212 [162; 161; 164; 279]%N;
mp 0 1;
mp 0 275;
mp 0 4;
mp 0 12;
inst 201 [213; 169; 165]%N;
mp 0 1;
inst 200 [171; 295; 170]%N;
inst 150 [171; 158; 169]%N;
mp 0 1;
inst 247 [171; 295; 295; 171]%N;
ax 158 155 157 171;
inst 224 [155; 154; 157; 279]%N;
mp 0 1;
mp 0 287;
mp 0 4;
mp 0 6;
inst 159 [171; 169; 166]%N;
mp 0 1;
ax 169 159 165 171;
mp 0 1;
inst 243 [159; 165]%N;
mp 0 1;
mp 0 16;
inst 243 [167; 215; 295; 220]%N;
inst 322 [166; 215; 220; 165]%N;
mp 0 1;
inst 249 [165; 166]%N;
mp 0 1;
mp 0 5;
inst 223 [214; 295; 170]%N;
inst 328 [168; 295; 215; 166]%N;
inst 244 [166; 153; 168; 279]%N;
mp 0 1;
mp 0 307;
mp 0 4;
mp 0 6;
mp 0 48;
inst 213 [295; 221; 293]%N;
mp 0 1;
mp 0 157;
inst 234 [293; 221; 296]%N;
inst 184 [293; 151; 150]%N;
mp 0 1;
inst 293 [296; 151; 149; 145]%N;
inst 267 [145; 146]%N;
mp 0 1;
inst 345 [150; 146; 293]%N;
mp 0 1;
inst 289 [151; 149; 150]%N;
mp 0 1;
ax 151 147 149 293;
inst 264 [147; 146; 149; 279]%N;
mp 0 1;
mp 0 327;
mp 0 4;
mp 0 12;
inst 250 [296; 295; 294]%N;
inst 200 [296; 144; 293]%N;
mp 0 1;
inst 297 [296; 295; 295; 296]%N;
ax 144 141 143 296;
inst 274 [141; 140; 143; 279]%N;
mp 0 1;
mp 0 337;
mp 0 4;
mp 0 6;
inst 209 [296; 293; 151]%N;
mp 0 1;
ax 293 149 150 296;
mp 0 1;
inst 293 [149; 150]%N;
mp 0 1;
mp 0 16;
inst 282 [296; 215; 221]%N;
mp 0 1;
mp 0 35;
inst 326 [285; 258; 221; 138]%N;
inst 300 [138; 139]%N;
mp 0 1;
inst 378 [222; 139; 294]%N;
mp 0 1;
inst 322 [258; 221; 222]%N;
mp 0 1;
ax 221 137 296 291;
mp 0 1;
inst 308 [137; 296]%N;
mp 0 1;
inst 386 [221; 296; 152]%N;
mp 0 1;
inst 312 [152; 221]%N;
mp 0 1;
mp 0 15;
inst 26 [133; 296]%N;
inst 236 [133; 131; 130]%N;
mp 0 1;
inst 345 [136; 131; 129; 125]%N;
inst 319 [125; 126]%N;
mp 0 1;
inst 397 [130; 126; 133]%N;
mp 0 1;
inst 341 [131; 129; 130]%N;
mp 0 1;
ax 131 127 129 133;
inst 316 [127; 126; 129; 279]%N;
mp 0 1;
mp 0 379;
mp 0 4;
mp 0 12;
inst 305 [268; 134; 130]%N;
mp 0 1;
inst 44 [136; 285]%N;
inst 254 [136; 134; 131]%N;
mp 0 1;
ax 134 124 130 136;
mp 0 1;
inst 338 [124; 130]%N;
mp 0 1;
mp 0 7;
inst 365 [268; 296; 291; 132; 130]%N;
inst 342 [130; 131]%N;
mp 0 1;
mp 0 3;
inst 298 [296; 285; 135]%N;
mp 0 1;
inst 58 [123; 268]%N;
inst 268 [123; 121; 120]%N;
mp 0 1;
inst 377 [136; 121; 119; 115]%N;
inst 351 [115; 116]%N;
mp 0 1;
inst 429 [120; 116; 123]%N;
mp 0 1;
inst 373 [121; 119; 120]%N;
mp 0 1;
ax 121 117 119 123;
inst 348 [117; 116; 119; 279]%N;
mp 0 1;
mp 0 411;
mp 0 4;
mp 0 12;
inst 337 [133; 134; 120]%N;
mp 0 1;
inst 285 [136; 134; 121]%N;
mp 0 32;
ax 134 114 120 136;
mp 0 1;
inst 369 [114; 120]%N;
mp 0 1;
mp 0 6;
inst 399 [122; 268; 258; 113]%N;
inst 373 [113; 136]%N;
mp 0 1;
inst 451 [121; 136; 120]%N;
mp 0 1;
inst 377 [120; 121]%N;
mp 0 1;
mp 0 7;
inst 91 [268; 134]%N;
inst 361 [268; 123]%N;
mp 0 1;
mp 0 3;
mp 0 37;
inst 356 [109; 285; 136]%N;
inst 306 [109; 107; 106]%N;
mp 0 1;
inst 415 [112; 107; 105; 101]%N;
inst 389 [101; 102]%N;
mp 0 1;
inst 467 [106; 102; 109]%N;
mp 0 1;
inst 411 [107; 105; 106]%N;
mp 0 1;
ax 107 103 105 109;
inst 386 [103; 102; 105; 279]%N;
mp 0 1;
mp 0 449;
mp 0 4;
mp 0 12;
inst 375 [134; 110; 106]%N;
mp 0 1;
inst 114 [112; 285]%N;
inst 324 [112; 110; 107]%N;
mp 0 1;
ax 110 100 106 112;
mp 0 1;
inst 408 [100; 106]%N;
mp 0 1;
mp 0 7;
inst 408 [108; 136; 285; 222]%N;
inst 487 [107; 136; 222; 106]%N;
mp 0 1;
inst 414 [106; 107]%N;
mp 0 1;
mp 0 5;
inst 388 [135; 285; 111]%N;
inst 493 [109; 285; 136; 107]%N;
inst 409 [107; 99; 109; 279]%N;
mp 0 1;
mp 0 472;
mp 0 4;
mp 0 6;
mp 0 39;
inst 378 [285; 258; 268]%N;
mp 0 1;
inst 112 [294; 222; 136]%N;
mp 0 113;
mp 0 2;
inst 401 [96; 97; 268]%N;
inst 351 [96; 93; 92]%N;
mp 0 1;
inst 460 [268; 93; 91; 87]%N;
inst 434 [87; 88]%N;
mp 0 1;
inst 512 [92; 88; 96]%N;
mp 0 1;
inst 456 [93; 91; 92]%N;
mp 0 1;
ax 93 89 91 96;
inst 431 [89; 88; 91; 279]%N;
mp 0 1;
mp 0 494;
mp 0 4;
mp 0 12;
inst 157 [268; 258]%N;
inst 367 [268; 96; 93]%N;
mp 0 1;
ax 96 91 92 268;
mp 0 1;
inst 451 [91; 92]%N;
mp 0 1;
mp 0 7;
inst 440 [268; 95; 97]%N;
mp 0 1;
inst 427 [136; 258; 294]%N;
inst 168 [81; 136]%N;
inst 432 [86; 82; 79]%N;
mp 0 1;
ax 79 78 83 95;
mp 0 1;
inst 462 [78; 83]%N;
mp 0 1;
inst 461 [93; 136; 94; 80]%N;
inst 445 [83; 79]%N;
mp 0 1;
mp 0 3;
inst 421 [136; 95; 83]%N;
mp 0 1;
mp 0 13;
inst 442 [95; 94; 136]%N;
ax 95 82 84 136;
inst 463 [82; 77; 84; 279]%N;
mp 0 1;
mp 0 526;
mp 0 4;
mp 0 6;
mp 0 22;
inst 450 [75; 76; 136]%N;
inst 400 [75; 72; 71]%N;
mp 0 1;
inst 509 [136; 72; 70; 66]%N;
inst 483 [66; 67]%N;
mp 0 1;
inst 561 [71; 67; 75]%N;
mp 0 1;
inst 505 [72; 70; 71]%N;
mp 0 1;
ax 72 68 70 75;
inst 480 [68; 67; 70; 279]%N;
mp 0 1;
mp 0 543;
mp 0 4;
mp 0 12;
inst 206 [136; 94]%N;
inst 416 [136; 75; 72]%N;
mp 0 1;
ax 75 70 71 136;
mp 0 1;
inst 500 [70; 71]%N;
mp 0 1;
mp 0 7;
inst 489 [136; 74; 76]%N;
mp 0 1;
inst 476 [85; 94; 98]%N;
inst 217 [60; 85]%N;
inst 481 [65; 61; 58]%N;
mp 0 1;
ax 58 57 62 74;
mp 0 1;
inst 511 [57; 62]%N;
mp 0 1;
inst 510 [72; 85; 73; 59]%N;
inst 494 [62; 58]%N;
mp 0 1;
mp 0 3;
inst 470 [85; 74; 62]%N;
mp 0 1;
mp 0 13;
inst 491 [74; 73; 85]%N;
ax 74 61 63 85;
inst 512 [61; 56; 63; 279]%N;
mp 0 1;
mp 0 575;
mp 0 4;
mp 0 6;
mp 0 22;
mp 0 49;
inst 240 [51; 98]%N;
inst 450 [51; 49; 48]%N;
mp 0 1;
inst 559 [54; 49; 47; 43]%N;
inst 533 [43; 44]%N;
mp 0 1;
inst 611 [48; 44; 51]%N;
mp 0 1;
inst 555 [49; 47; 48]%N;
mp 0 1;
ax 49 45 47 51;
inst 530 [45; 44; 47; 279]%N;
mp 0 1;
mp 0 593;
mp 0 4;
mp 0 12;
inst 519 [55; 52; 48]%N;
mp 0 1;
inst 258 [54; 136]%N;
inst 468 [54; 52; 49]%N;
mp 0 1;
ax 52 42 48 54;
mp 0 1;
inst 552 [42; 48]%N;
mp 0 1;
mp 0 7;
inst 579 [55; 98; 94; 50; 48]%N;
inst 556 [48; 49]%N;
mp 0 1;
mp 0 3;
inst 512 [98; 136; 53]%N;
mp 0 1;
inst 272 [41; 55]%N;
inst 482 [41; 39; 38]%N;
mp 0 1;
inst 591 [54; 39; 37; 33]%N;
inst 565 [33; 34]%N;
mp 0 1;
inst 643 [38; 34; 41]%N;
mp 0 1;
inst 587 [39; 37; 38]%N;
mp 0 1;
ax 39 35 37 41;
inst 562 [35; 34; 37; 279]%N;
mp 0 1;
mp 0 625;
mp 0 4;
mp 0 12;
inst 551 [51; 52; 38]%N;
mp 0 1;
inst 499 [54; 52; 39]%N;
mp 0 32;
ax 52 32 38 54;
mp 0 1;
inst 583 [32; 38]%N;
mp 0 1;
mp 0 6;
inst 613 [40; 55; 76; 31]%N;
inst 587 [31; 54]%N;
mp 0 1;
inst 665 [39; 54; 38]%N;
mp 0 1;
inst 591 [38; 39]%N;
mp 0 1;
mp 0 7;
inst 305 [55; 52]%N;
inst 575 [55; 41]%N;
mp 0 1;
mp 0 3;
mp 0 37;
inst 570 [27; 136; 54]%N;
inst 520 [27; 25; 24]%N;
mp 0 1;
inst 629 [30; 25; 23; 19]%N;
inst 603 [19; 20]%N;
mp 0 1;
inst 681 [24; 20; 27]%N;
mp 0 1;
inst 625 [25; 23; 24]%N;
mp 0 1;
ax 25 21 23 27;
inst 600 [21; 20; 23; 279]%N;
mp 0 1;
mp 0 663;
mp 0 4;
mp 0 12;
inst 589 [52; 28; 24]%N;
mp 0 1;
inst 328 [30; 136]%N;
inst 538 [30; 28; 25]%N;
mp 0 1;
ax 28 18 24 30;
mp 0 1;
inst 622 [18; 24]%N;
mp 0 1;
mp 0 7;
inst 622 [26; 54; 136; 73]%N;
inst 701 [25; 54; 73; 24]%N;
mp 0 1;
inst 628 [24; 25]%N;
mp 0 1;
mp 0 5;
inst 602 [53; 136; 29]%N;
inst 707 [27; 136; 54; 25]%N;
inst 623 [25; 17; 27; 279]%N;
mp 0 1;
mp 0 686;
mp 0 4;
mp 0 6;
mp 0 39;
inst 592 [136; 76; 55]%N;
mp 0 1;
mp 0 112;
inst 613 [55; 76; 294]%N;
inst 563 [55; 15; 14]%N;
mp 0 1;
inst 672 [294; 15; 13; 9]%N;
inst 646 [9; 10]%N;
mp 0 1;
inst 724 [14; 10; 55]%N;
mp 0 1;
inst 668 [15; 13; 14]%N;
mp 0 1;
ax 15 11 13 55;
inst 643 [11; 10; 13; 279]%N;
mp 0 1;
mp 0 706;
mp 0 4;
mp 0 12;
inst 369 [294; 136]%N;
inst 579 [294; 55; 15]%N;
mp 0 1;
ax 55 13 14 294;
mp 0 1;
inst 663 [13; 14]%N;
mp 0 1;
mp 0 7;
inst 652 [294; 54; 76]%N;
mp 0 1;
mp 0 26;
inst 696 [268; 97; 76; 7]%N;
inst 670 [7; 8]%N;
mp 0 1;
inst 748 [94; 8; 98]%N;
mp 0 1;
inst 692 [97; 76; 94]%N;
mp 0 1;
ax 76 6 294 258;
mp 0 1;
inst 678 [6; 294]%N;
mp 0 1;
inst 756 [76; 294; 16]%N;
mp 0 1;
inst 682 [16; 76]%N;
mp 0 1;
mp 0 15;
mp 0 255;
inst 0 [258; 241; 291]%N;
inst 1 [258; 291; 285]%N;
inst 599 [0; 5]%N;
inst 600 [2; 5]%N;
inst 4 [5; 4; 3]%N;
inst 5 [5; 3; 1]%N;
inst 377 [251; 296; 291]%N;
inst 705 [258; 291; 287]%N;
mp 7 0;
mp 5 0;
mp 5 0;
mp 0 4;
inst 612 [258; 291; 295]%N;
mp 11 0;
mp 11 0;
mp 9 0;
mp 0 4].
Definition target := rho (V 0) (V 1) (V 2) (V 3).
Lemma certificate_checked : check (decode term_data) proof_data target = true.
Proof. vm_compute. reflexivity. Qed.
End Certificate.
Print Assumptions Certificate.check_sound.

(** Every rho8 instance follows from the dominated instances. *)
Theorem rho8_all (T : nat -> Prop) (h : DomImp T) a b c u : T (rho8 a b c u).
Proof.
 pose proof (Certificate.check_sound T h (Certificate.decode Certificate.term_data)
   Certificate.proof_data Certificate.target Certificate.certificate_checked) as H.
 specialize (H (fun i => nth i [a;b;c;u] 0)).
 unfold Certificate.target in H. rewrite Certificate.eval_rho in H. exact H.
Qed.
Print Assumptions rho8_all.
