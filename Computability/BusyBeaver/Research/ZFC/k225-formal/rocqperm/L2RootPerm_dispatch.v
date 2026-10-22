(** ** dispatch (node 141): selector 0 NIP, 1 DROP, 2 MP, 3 + c AX (axiomcode = c) *)
Lemma disp_nip m x m' : get m 3 = 0 -> sem (ENode 152) m x m' -> (x = XNormal \/ x = XHalt) ->
  sem (ENode 141) m x m'.
Proof.
  intros H3 H [-> | ->].
  - eapply sem_cdr_normal; [reflexivity | | exact H].
    eapply sem_car_break1; [reflexivity | apply sem_decnz_zero, H3].
  - eapply sem_cdr_halt; [reflexivity | | exact H].
    eapply sem_car_break1; [reflexivity | apply sem_decnz_zero, H3].
Qed.

(* selector >= 1: decrement, run the rest of the dispatch, break out of the switch *)
Ltac disp_pos :=
  intros H3 H [-> | ->];
  [ eapply sem_car_break1; [reflexivity|];
    eapply sem_cdr_break with (k := 0); [reflexivity | apply sem_decnz_pos; [lia | exact H3] |];
    eapply sem_cdr_break with (k := 0); [reflexivity | exact H | apply sem_breakS]
  | eapply sem_car_halt; [reflexivity|];
    eapply sem_cdr_halt; [reflexivity | apply sem_decnz_pos; [lia | exact H3] |];
    eapply sem_car_halt; [reflexivity | exact H] ].

(* selector 0: take the case's own body *)
Ltac disp_zero :=
  intros H3 m' H; eapply sem_cdr_normal; [reflexivity | | exact H];
  eapply sem_car_break1; [reflexivity | apply sem_decnz_zero, H3].

Lemma disp_1 m v x m' : get m 3 = S v -> sem (ENode 144) (set m 3 v) x m' ->
  (x = XNormal \/ x = XHalt) -> sem (ENode 141) m x m'.
Proof. disp_pos. Qed.

Lemma disp_drop m : get m 3 = 0 -> forall m', sem (ENode 121) m XNormal m' -> sem (ENode 144) m XNormal m'.
Proof. disp_zero. Qed.

Lemma disp_2 m v x m' : get m 3 = S v -> sem (ENode 147) (set m 3 v) x m' ->
  (x = XNormal \/ x = XHalt) -> sem (ENode 144) m x m'.
Proof. disp_pos. Qed.

(* mp() reads its own field: node 484 = (read_p1, mp body 150) *)
Lemma mp484 m : get m 6 = 0 -> get m 7 = 0 -> sem (ENode 484) m XNormal
  (if Nat.eqb (wim (get m 1) (get m 4 + fst (unP (get m 8)))) (get m 5)
   then set (set (set (set (set m 4 (get m 4 + fst (unP (get m 8)))) 8 (snd (unP (get m 8))))
          1 (get m 4 + fst (unP (get m 8)))) 2 (P 0 (get m 2))) 5 0
   else set (set (set (set m 4 (get m 4 + fst (unP (get m 8)))) 8 (snd (unP (get m 8)))) 1 0) 5 0).
Proof.
  intros H6 H7. eapply sem_cdr_normal; [reflexivity | apply read175; assumption |].
  eapply sem_conseq; [apply mp150; destruct m; nrm; assumption |].
  destruct m; nrm. reflexivity.
Qed.

Lemma disp_mp m : get m 3 = 0 -> forall m', sem (ENode 484) m XNormal m' -> sem (ENode 147) m XNormal m'.
Proof. disp_zero. Qed.

Lemma disp_ax m v m' : get m 3 = S v -> sem (ENode 236) (set m 3 v) XNormal m' -> sem (ENode 147) m XNormal m'.
Proof.
  intros H3 H. eapply sem_car_break1; [reflexivity|].
  eapply sem_cdr_break with (k := 0); [reflexivity | apply sem_decnz_pos; [lia | exact H3] |].
  eapply sem_cdr_break with (k := 0); [reflexivity | exact H | apply sem_breakS].
Qed.

Ltac elem9 := match goal with |- sem (ENode 133) _ _ _ => eapply ifnot133; side end.
Ltac elem ::= first [elem9 | elem8 | elem7 | elem6 | elem5 | elem4 | elem3 | elem2 | elem1 | elem0].

(** ** The prefix of main(): fetch the next command and read the selector. *)
Lemma prefix_ok s pl1 np1 ac pl2 :
  (if Nat.eqb (pl s) 0 then (np s, S (np s)) else (pred (pl s), np s)) = (pl1, np1) ->
  unP pl1 = (ac, pl2) ->
  seqx [ENode 133; ENode 174] (enc s) XNormal (mkSt np1 (tw s) (ws s) ac (d s) (h s) 0 0 pl2).
Proof.
  intros Hp E1. destruct s as [pl np t w d h]. unfold enc.
  cbn [EnumPerm.pl EnumPerm.np EnumPerm.tw EnumPerm.ws EnumPerm.d EnumPerm.h] in *.
  destruct pl as [|v]; injection Hp as <- <-; repeat step; apply sx_nil_eq;
    rewrite ?E1; cbn [fst snd]; reflexivity.
Qed.

Lemma main_flat : expand 200 (fst (dag_nodes 0)) ++ expand 200 (snd (dag_nodes 0)) =
  [ENode 133; ENode 174; ENode 141].
Proof. vm_compute. reflexivity. Qed.

Lemma root_of m x m' : seqx [ENode 133; ENode 174] m XNormal m' ->
  forall m'', sem (ENode 141) m' x m'' -> (x = XNormal \/ x = XHalt) -> sem (ENode 0) m x m''.
Proof.
  intros H1 m'' H2 Hx. apply seq_node. rewrite main_flat.
  change [ENode 133; ENode 174; ENode 141] with ([ENode 133; ENode 174] ++ [ENode 141]).
  eapply seqx_app; [exact H1|]. destruct Hx as [-> | ->].
  - eapply sx_normal; [exact H2 | constructor].
  - apply sx_halt, H2.
Qed.

(** ** One iteration of main() on abstract register files. *)
Theorem root_sem s :
  (enum_step s = None -> exists m', sem (ENode 0) (enc s) XHalt m') /\
  (forall s', enum_step s = Some s' -> sem (ENode 0) (enc s) XNormal (enc s')).
Proof.
  unfold enum_step.
  destruct (if Nat.eqb (pl s) 0 then (np s, S (np s)) else (pred (pl s), np s)) as [pl1 np1] eqn:Hp.
  destruct (unP pl1) as [ac pl2] eqn:E1.
  pose proof (prefix_ok s _ _ _ _ Hp E1) as Hpre.
  set (m := mkSt np1 (tw s) (ws s) ac (d s) (h s) 0 0 pl2) in Hpre.
  destruct ac as [|[|[|c]]].
  - (* NIP *)
    split.
    + intros Hn. destruct (Nat.eqb_spec (h s) 1) as [H1 | H1]; [|destruct (unP (ws s)); discriminate].
      destruct (nip152_halt m eq_refl H1) as [m' Hm'].
      exists m'. apply (root_of _ _ _ Hpre); [|now right].
      apply disp_nip; [reflexivity | exact Hm' | now right].
    + intros s' Hs. destruct (Nat.eqb_spec (h s) 1) as [H1 | H1]; [discriminate|].
      destruct (unP (ws s)) as [h1 w1] eqn:Ew. injection Hs as <-.
      apply (root_of _ _ _ Hpre); [|now left].
      apply disp_nip; [reflexivity | | now left].
      eapply sem_conseq; [apply nip152; [reflexivity | reflexivity | exact H1]|].
      subst m. cbn [get set]. rewrite Ew. reflexivity.
  - (* DROP *)
    split; [discriminate|]. intros s' Hs. injection Hs as <-.
    apply (root_of _ _ _ Hpre); [|now left].
    apply (disp_1 _ 0); [reflexivity | | now left].
    apply disp_drop; [reflexivity|].
    eapply sem_conseq; [apply par121; reflexivity|]. reflexivity.
  - (* MP *)
    split; [intros Hn; destruct (unP pl2); discriminate|].
    intros s' Hs. destruct (unP pl2) as [x pl3] eqn:E2. injection Hs as <-.
    apply (root_of _ _ _ Hpre); [|now left].
    apply (disp_1 _ 1); [reflexivity | | now left].
    apply (disp_2 _ 0); [reflexivity | | now left].
    apply disp_mp; [reflexivity|].
    eapply sem_conseq; [apply mp484; reflexivity|]. subst m. cbn [get set]. rewrite E2. cbn [fst snd].
    unfold enc. destruct (Nat.eqb (wim (tw s) (d s + x)) (h s)); reflexivity.
  - (* AX *)
    split; [intros Hn; destruct (unP pl2) as [y pl3]; destruct (unP pl3); discriminate|].
    intros s' Hs. destruct (unP pl2) as [y pl3] eqn:E3. destruct (unP pl3) as [u pl4] eqn:E4.
    injection Hs as <-.
    apply (root_of _ _ _ Hpre); [|now left].
    apply (disp_1 _ (S (S c))); [reflexivity | | now left].
    apply (disp_2 _ (S c)); [reflexivity | | now left].
    apply (disp_ax _ c); [reflexivity|].
    eapply sem_conseq; [apply (ax1 _ y pl3 u pl4); [reflexivity | reflexivity | exact E3 | exact E4]|].
    reflexivity.
Qed.

