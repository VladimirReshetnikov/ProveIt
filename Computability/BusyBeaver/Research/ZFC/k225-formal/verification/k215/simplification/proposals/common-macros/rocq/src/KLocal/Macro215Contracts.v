(** Complete concrete contract adapter: all 58 literal-node theorems from ProgLibPerm.
    The arithmetic proof is reused from the canonical 89-node MacroLibrary. *)
From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia.
From K230 Require Import RM.
From K230L Require Import Codes230.
From KLocal Require Import LocalProgram MacroProgram MacroLibrary Macro215Binding.
From K215F Require Import DagPerm.
Import ListNotations.
Definition sem (e : edge) (m : St) (x : exit) (m' : St) : Prop :=
  forall R, approx R m -> exists R', run dagPerm e R x R' /\ approx R' m'.
Lemma sem_lift e m x m' : inside macro_ok e = true ->
  MacroLibrary.sem e m x m' -> sem e m x m'.
Proof.
  intros He H R HR. destruct (H R HR) as (R' & Hr & Hm).
  exists R'. split; [|exact Hm].
  eapply run_transfer; [exact canonical_to_215|exact Hr|exact He].
Qed.
Lemma w117 m : sem (ENode 117) m XNormal (set (set m 1 (get m 1 + 4 * get m 7)) 7 0).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.w117; eauto. Qed.

Lemma w192 m : sem (ENode 192) m XNormal (set (set (set m 6 (get m 6 + get m 3)) 7 (get m 7 + get m 3)) 3 0).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.w192; eauto. Qed.

Lemma w193 m : sem (ENode 193) m XNormal (set (set (set m 1 (get m 1 + get m 3)) 6 (get m 6 + get m 3)) 3 0).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.w193; eauto. Qed.

Lemma w194 m : sem (ENode 194) m XNormal (set (set (set m 6 (get m 6 + get m 0)) 8 (get m 8 + get m 0)) 0 0).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.w194; eauto. Qed.

Lemma w197 m : sem (ENode 197) m XNormal (set (set m 5 (get m 5 + get m 4)) 4 0).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.w197; eauto. Qed.

Lemma w198 m : sem (ENode 198) m XNormal (set (set (set m 1 (get m 1 + get m 4)) 6 (get m 6 + get m 4)) 4 0).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.w198; eauto. Qed.

Lemma w199 m : sem (ENode 199) m XNormal (set m 5 0).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.w199; eauto. Qed.

Lemma w200 m : sem (ENode 200) m XNormal (set (set (set m 1 (get m 1 + get m 5)) 6 (get m 6 + get m 5)) 5 0).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.w200; eauto. Qed.

Lemma w201 m : sem (ENode 201) m XNormal (set (set m 3 (get m 3 + get m 6)) 6 0).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.w201; eauto. Qed.

Lemma w203 m : sem (ENode 203) m XNormal (set (set m 0 (get m 0 + get m 6)) 6 0).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.w203; eauto. Qed.

Lemma w205 m : sem (ENode 205) m XNormal (set (set m 4 (get m 4 + get m 6)) 6 0).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.w205; eauto. Qed.

Lemma w207 m : sem (ENode 207) m XNormal (set (set m 5 (get m 5 + get m 6)) 6 0).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.w207; eauto. Qed.

Lemma w208 m : sem (ENode 208) m XNormal (set (set m 1 (get m 1 + get m 6)) 6 0).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.w208; eauto. Qed.

Lemma w209 m : sem (ENode 209) m XNormal (set (set m 8 (get m 8 + get m 7)) 7 0).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.w209; eauto. Qed.

Lemma w211 m : sem (ENode 211) m XNormal (set (set m 6 (get m 6 + get m 7)) 7 0).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.w211; eauto. Qed.

Lemma w212 m : sem (ENode 212) m XNormal (set (set m 2 (get m 2 + get m 7)) 7 0).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.w212; eauto. Qed.

Lemma w214 m : sem (ENode 214) m XNormal (set m 1 0).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.w214; eauto. Qed.

Lemma w215 m : sem (ENode 215) m XNormal (set (set (set m 6 (get m 6 + get m 1)) 7 (get m 7 + get m 1)) 1 0).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.w215; eauto. Qed.

Lemma w216 m : sem (ENode 216) m XNormal (set (set m 6 (get m 6 + get m 1)) 1 0).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.w216; eauto. Qed.

Lemma w217 m : sem (ENode 217) m XNormal (set (set m 1 (get m 1 + get m 2)) 2 0).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.w217; eauto. Qed.

Lemma pair162 m :
  sem (ENode 162) m XNormal (set (set (set m 7 (get m 7 + P (get m 6) (get m 1))) 6 0) 1 0).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.pair162; eauto. Qed.

Lemma ubody154 m : sem (ENode 154) m (XContinue 1) (ustep 6 7 m).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.ubody154; eauto. Qed.

Lemma unpair115 m : sem (ENode 115) m XNormal (unpair_post 8 6 7 m).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.unpair115; eauto. Qed.

Lemma unpair116 m : sem (ENode 116) m XNormal (unpair_post 2 6 7 m).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.unpair116; eauto. Qed.

Lemma pushwff171 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 171) m XNormal (set (set m 2 (P (get m 1) (get m 2))) 1 0).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.pushwff171; eauto. Qed.

Lemma v177 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 177) m XNormal (set (set m 2 (P (get m 1) (get m 2))) 1 1).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.v177; eauto. Qed.

Lemma par166 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 166) m XNormal (set (set m 2 (P (get m 1) (get m 2))) 1 (get m 4)).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.par166; eauto. Qed.

Lemma par121 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 121) m XNormal (set (set m 2 (P (get m 1) (get m 2))) 1 (get m 5)).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.par121; eauto. Qed.

Lemma par168 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 168) m XNormal (set (set m 2 (P (get m 1) (get m 2))) 1 (get m 3)).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.par168; eauto. Qed.

Lemma n158 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 158) m XNormal (set (set m 6 (fst (unP (get m 8)))) 8 (snd (unP (get m 8)))).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.n158; eauto. Qed.

Lemma n160 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 160) m XNormal (set (set m 6 (fst (unP (get m 2)))) 2 (snd (unP (get m 2)))).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.n160; eauto. Qed.

Lemma cons119 m x r : get m 2 = P x r -> get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 119) m XNormal (set (set m 1 (wim x (get m 1))) 2 r).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.cons119; eauto. Qed.

Lemma wel181 m x r : get m 2 = P x r -> get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 181) m XNormal (set (set m 1 (wel x (get m 1))) 2 r).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.wel181; eauto. Qed.

Lemma wal180 m x r : get m 2 = P x r -> get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 180) m XNormal (set (set m 1 (wal x (get m 1))) 2 r).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.wal180; eauto. Qed.

Lemma weq182 m x r : get m 2 = P x r -> get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 182) m XNormal (set (set m 1 (weq x (get m 1))) 2 r).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.weq182; eauto. Qed.

Lemma wn218 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 218) m XNormal (set m 1 (wn (get m 1))).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.wn218; eauto. Qed.

Lemma wex183 m x r : get m 2 = P x r -> get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 183) m XNormal (set (set m 1 (wex x (get m 1))) 2 r).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.wex183; eauto. Qed.

Lemma wa178 m x r : get m 2 = P x r -> get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 178) m XNormal (set (set m 1 (wa x (get m 1))) 2 r).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.wa178; eauto. Qed.

Lemma read174 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 174) m XNormal (set (set m 3 (get m 3 + fst (unP (get m 8)))) 8 (snd (unP (get m 8)))).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.read174; eauto. Qed.

Lemma read175 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 175) m XNormal (set (set m 4 (get m 4 + fst (unP (get m 8)))) 8 (snd (unP (get m 8)))).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.read175; eauto. Qed.

Lemma read176 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 176) m XNormal (set (set m 5 (get m 5 + fst (unP (get m 8)))) 8 (snd (unP (get m 8)))).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.read176; eauto. Qed.

Lemma pop170 m : get m 6 = 0 -> get m 7 = 0 ->
  sem (ENode 170) m XNormal (set (set m 5 (get m 5 + fst (unP (get m 2)))) 2 (snd (unP (get m 2)))).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.pop170; eauto. Qed.

Lemma u462_pos m v : get m 6 = S v -> sem (ENode 462) m (XContinue 1) (set m 6 v).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.u462_pos; eauto. Qed.

Lemma u462_zero m : get m 6 = 0 -> sem (ENode 462) m (XBreak 1) m.
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.u462_zero; eauto. Qed.

Lemma loop463 a : forall m, get m 5 = a ->
  (a <= get m 6 -> sem (ENode 463) m XNormal (set (set m 5 0) 6 (get m 6 - a))) /\
  (get m 6 < a -> sem (ENode 463) m (XBreak 1) (set (set m 5 (a - get m 6 - 1)) 6 0)).
Proof.
  intros m Hm. destruct (MacroLibrary.loop463 a m Hm) as [Hle Hlt].
  split; intro Ha; eapply sem_lift; [reflexivity|apply Hle, Ha|reflexivity|apply Hlt, Ha].
Qed.

Lemma l464_eq m : get m 6 = get m 5 -> sem (ENode 464) m (XBreak 1) (clr m).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.l464_eq; eauto. Qed.

Lemma l464_neq m : get m 6 <> get m 5 ->
  exists x y, sem (ENode 464) m XNormal (set (set m 5 x) 6 y).
Proof.
  intro Hm. destruct (MacroLibrary.l464_neq m Hm) as (x & y & Hxy).
  exists x, y. apply sem_lift; [reflexivity|exact Hxy].
Qed.

Lemma z465 a : forall m, get m 5 = a -> sem (ENode 465) m XNormal (set m 5 0).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.z465; eauto. Qed.

Lemma r466 b : forall m, get m 6 = b -> sem (ENode 466) m (XBreak 1) (clr m).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.r466; eauto. Qed.

Lemma if123_eq m : get m 6 = get m 5 -> sem (ENode 123) m XNormal (clr m).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.if123_eq; eauto. Qed.

Lemma if123_neq m : get m 6 <> get m 5 -> sem (ENode 123) m (XBreak 1) (clr m).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.if123_neq; eauto. Qed.

Lemma ifeq130 m : get m 7 = 0 -> sem (ENode 130) m XNormal
  (if Nat.eqb (get m 6) (get m 5)
   then set (set (clr m) 2 (P (get m 1) (get m 2))) 1 (get m 4) else clr m).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.ifeq130; eauto. Qed.

Lemma ifeq131 m : sem (ENode 131) m XNormal
  (set (clr m) 1 (if Nat.eqb (get m 6) (get m 5) then 0 else get m 1)).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.ifeq131; eauto. Qed.

Lemma ifeq132_halt m : get m 6 = get m 5 -> sem (ENode 132) m XHalt (clr m).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.ifeq132_halt; eauto. Qed.

Lemma ifeq132_normal m : get m 6 <> get m 5 -> sem (ENode 132) m XNormal (clr m).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.ifeq132_normal; eauto. Qed.

Lemma w136_count k : forall m, get m 6 = k ->
  sem (ENode 136) m XNormal (set (set m 0 (get m 0 + S k)) 6 0).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.w136_count; eauto. Qed.

Lemma w136 m : sem (ENode 136) m XNormal
  (set (set m 0 (S (get m 0 + get m 6))) 6 0).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.w136; eauto. Qed.

Lemma ifnot133 m : get m 6 = 0 -> sem (ENode 133) m XNormal
  (set (set m 8 (match get m 8 with 0 => get m 0 | S v => v end))
       0 (match get m 8 with 0 => S (get m 0) | S _ => get m 0 end)).
Proof. intros; eapply sem_lift; [reflexivity|]; eapply MacroLibrary.ifnot133; eauto. Qed.

Print Assumptions w117.
Print Assumptions w192.
Print Assumptions w193.
Print Assumptions w194.
Print Assumptions w197.
Print Assumptions w198.
Print Assumptions w199.
Print Assumptions w200.
Print Assumptions w201.
Print Assumptions w203.
Print Assumptions w205.
Print Assumptions w207.
Print Assumptions w208.
Print Assumptions w209.
Print Assumptions w211.
Print Assumptions w212.
Print Assumptions w214.
Print Assumptions w215.
Print Assumptions w216.
Print Assumptions w217.
Print Assumptions pair162.
Print Assumptions ubody154.
Print Assumptions unpair115.
Print Assumptions unpair116.
Print Assumptions pushwff171.
Print Assumptions v177.
Print Assumptions par166.
Print Assumptions par121.
Print Assumptions par168.
Print Assumptions n158.
Print Assumptions n160.
Print Assumptions cons119.
Print Assumptions wel181.
Print Assumptions wal180.
Print Assumptions weq182.
Print Assumptions wn218.
Print Assumptions wex183.
Print Assumptions wa178.
Print Assumptions read174.
Print Assumptions read175.
Print Assumptions read176.
Print Assumptions pop170.
Print Assumptions u462_pos.
Print Assumptions u462_zero.
Print Assumptions loop463.
Print Assumptions l464_eq.
Print Assumptions l464_neq.
Print Assumptions z465.
Print Assumptions r466.
Print Assumptions if123_eq.
Print Assumptions if123_neq.
Print Assumptions ifeq130.
Print Assumptions ifeq131.
Print Assumptions ifeq132_halt.
Print Assumptions ifeq132_normal.
Print Assumptions w136_count.
Print Assumptions w136.
Print Assumptions ifnot133.
