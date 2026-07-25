(** Total standard rows for the fixed program evaluator. *)

From Stdlib Require Import List Arith Lia Bool Wf_nat
  Logic.FunctionalExtensionality Logic.ProofIrrelevance.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction
  FiniteSkolemHull CanonicalSelector CanonicalSelectorPA
  SkolemProgramCode FiniteBetaCoding ProgramTrace.

Import ListNotations.
Import PAHierarchyReduction.
Import PAFiniteSkolemHull.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PASkolemProgramCode.
Import PAFiniteBetaCoding.
Import PAProgramTrace.

Module PATotalProgramRows.

(** Parse exactly [width] raw child codes from the linked argument-code
    representation.  Child codes themselves are not decoded: malformed
    child programs are legitimate inputs to the total row recursion. *)
Fixpoint decodeFixedArgsFuel
    (fuel width code : nat) : option (list nat) :=
  match width with
  | 0 =>
      match scheduleSkolemCode code with
      | siArgsNil => Some []
      | _ => None
      end
  | S width' =>
      match fuel with
      | 0 => None
      | S fuel' =>
          match scheduleSkolemCode code with
          | siArgsCons child rest =>
              match decodeFixedArgsFuel fuel' width' rest with
              | Some children => Some (child :: children)
              | None => None
              end
          | _ => None
          end
      end
  end.

Definition decodeFixedArgs (width code : nat) : option (list nat) :=
  decodeFixedArgsFuel (S code) width code.

Fixpoint argsCodeOfCodes (codes : list nat) : nat :=
  match codes with
  | [] => polynomialNode tagArgsNil 0
  | child :: rest => polynomialNode tagArgsCons
      (polynomialPair child (argsCodeOfCodes rest))
  end.

Lemma schedule_argsCodeOfCodes : forall codes,
  scheduleSkolemCode (argsCodeOfCodes codes) =
  match codes with
  | [] => siArgsNil
  | child :: rest => siArgsCons child (argsCodeOfCodes rest)
  end.
Proof.
  intros [|child rest]; cbn [argsCodeOfCodes];
    unfold scheduleSkolemCode.
  - rewrite polynomialUnnode_node. reflexivity.
  - rewrite polynomialUnnode_node, polynomialSplit_pair. reflexivity.
Qed.

Local Opaque scheduleSkolemCode.

Lemma argsCodeOfCodes_positive : forall codes,
  0 < argsCodeOfCodes codes.
Proof.
  intros [|child rest]; simpl; apply polynomialNode_positive.
Qed.

Lemma argsCodeOfCodes_tail_lt : forall child rest,
  argsCodeOfCodes rest < argsCodeOfCodes (child :: rest).
Proof.
  intros child rest. cbn [argsCodeOfCodes].
  polynomial_child_lt polynomialPair_right_le.
Qed.

Lemma argsCodeOfCodes_head_lt : forall child rest,
  child < argsCodeOfCodes (child :: rest).
Proof.
  intros child rest. cbn [argsCodeOfCodes].
  polynomial_child_lt polynomialPair_left_le.
Qed.

Lemma argsCodeOfCodes_entry_lt : forall codes child,
  In child codes -> child < argsCodeOfCodes codes.
Proof.
  induction codes as [|head rest IH]; simpl; intros child hin.
  - contradiction.
  - destruct hin as [<- | hin].
    + apply argsCodeOfCodes_head_lt.
    + eapply Nat.lt_trans; [apply IH; exact hin |].
      apply argsCodeOfCodes_tail_lt.
Qed.

Lemma decodeFixedArgsFuel_codes : forall codes width fuel,
  length codes = width ->
  argsCodeOfCodes codes < fuel ->
  decodeFixedArgsFuel fuel width (argsCodeOfCodes codes) = Some codes.
Proof.
  induction codes as [|child rest IH]; intros [|width] fuel hlen hfuel;
    try discriminate.
  - destruct fuel as [|fuel]; [lia |].
    cbn [decodeFixedArgsFuel]. rewrite schedule_argsCodeOfCodes.
    reflexivity.
  - inversion hlen; subst width.
    destruct fuel as [|fuel]; [lia |].
    cbn [decodeFixedArgsFuel]. rewrite schedule_argsCodeOfCodes.
    rewrite (IH (length rest) fuel eq_refl).
    + reflexivity.
    + pose proof (argsCodeOfCodes_tail_lt child rest). lia.
Qed.

Corollary decodeFixedArgs_codes : forall codes,
  decodeFixedArgs (length codes) (argsCodeOfCodes codes) = Some codes.
Proof.
  intro codes. unfold decodeFixedArgs.
  apply decodeFixedArgsFuel_codes; [reflexivity | lia].
Qed.

Lemma decodeFixedArgsFuel_length : forall fuel width code codes,
  decodeFixedArgsFuel fuel width code = Some codes ->
  length codes = width.
Proof.
  intros fuel width. revert fuel.
  induction width as [|width IH]; intros fuel code codes h.
  - destruct fuel as [|fuel]; cbn [decodeFixedArgsFuel] in h;
      destruct (scheduleSkolemCode code); inversion h; reflexivity.
  - destruct fuel as [|fuel]; [discriminate |].
    cbn [decodeFixedArgsFuel] in h.
    destruct (scheduleSkolemCode code); try discriminate.
    destruct (decodeFixedArgsFuel fuel width n0) eqn:hrest;
      inversion h; subst.
    simpl. f_equal. exact (IH fuel n0 l hrest).
Qed.

Corollary decodeFixedArgs_length : forall width code codes,
  decodeFixedArgs width code = Some codes -> length codes = width.
Proof.
  intros width code codes h.
  exact (decodeFixedArgsFuel_length (S code) width code codes h).
Qed.

(** Successful linked-list decoding exposes only structurally smaller child
    codes.  This is the reason no additional child-bound test is needed in
    the total choose decoder. *)
Lemma decodeFixedArgsFuel_children_smaller : forall fuel width code codes,
  decodeFixedArgsFuel fuel width code = Some codes ->
  forall child, In child codes -> child < code.
Proof.
  intros fuel width. revert fuel.
  induction width as [|width IH]; intros fuel code codes hdecode child hin.
  - destruct fuel as [|fuel]; cbn [decodeFixedArgsFuel] in hdecode;
      destruct (scheduleSkolemCode code); try discriminate;
      inversion hdecode; subst codes; inversion hin.
  - destruct fuel as [|fuel]; [discriminate |].
    cbn [decodeFixedArgsFuel] in hdecode.
    destruct (scheduleSkolemCode code) eqn:hschedule; try discriminate.
    destruct (decodeFixedArgsFuel fuel width n0) eqn:hrest;
      inversion hdecode; subst codes.
    simpl in hin. destruct hin as [<- | hin].
    + apply (scheduled_children_smaller code n).
      rewrite hschedule. now left.
    + eapply Nat.lt_trans.
      * exact (IH fuel n0 l hrest child hin).
      * apply (scheduled_children_smaller code n0).
        rewrite hschedule. now right; left.
Qed.

Corollary decodeFixedArgs_children_smaller : forall width code codes,
  decodeFixedArgs width code = Some codes ->
  forall child, In child codes -> child < code.
Proof.
  intros width code codes hdecode child hin.
  exact (decodeFixedArgsFuel_children_smaller
    (S code) width code codes hdecode child hin).
Qed.

Corollary decoded_choose_children_smaller :
  forall target formulaIndex argsCode width childCodes,
  scheduleSkolemCode target = siChoose formulaIndex argsCode ->
  decodeFixedArgs width argsCode = Some childCodes ->
  forall child, In child childCodes -> child < target.
Proof.
  intros target formulaIndex argsCode width childCodes
    hschedule hdecode child hin.
  eapply Nat.lt_trans.
  - exact (decodeFixedArgs_children_smaller
      width argsCode childCodes hdecode child hin).
  - apply (scheduled_children_smaller target argsCode).
    rewrite hschedule. now left.
Qed.

(** Turn a raw list of child codes into the exact linked argument program
    list, calling the well-founded row recursion at every child. *)
Definition belowProgram (target : nat)
    (previous : forall child, child < target -> SkolemProgram)
    (child : nat) : SkolemProgram :=
  match lt_dec child target with
  | left h => previous child h
  | right _ => spZero
  end.

Fixpoint rowArgsFromCodes (target : nat)
    (previous : forall child, child < target -> SkolemProgram)
    (codes : list nat) : SkolemProgramArgs :=
  match codes with
  | [] => spaNil
  | child :: rest =>
      spaCons (belowProgram target previous child)
        (rowArgsFromCodes target previous rest)
  end.

Definition totalRowProgramStep (rank target : nat)
    (previous : forall child, child < target -> SkolemProgram) :
    SkolemProgram :=
  match scheduleSkolemCode target with
  | siSeed => spSeed
  | siZero => spZero
  | siSucc child => spSucc (belowProgram target previous child)
  | siAdd lhs rhs =>
      spAdd (belowProgram target previous lhs)
        (belowProgram target previous rhs)
  | siMul lhs rhs =>
      spMul (belowProgram target previous lhs)
        (belowProgram target previous rhs)
  | siChoose formulaIndex argsCode =>
      if formulaIndex <? length (formula_rank_enum rank) then
        match decodeFixedArgs rank argsCode with
        | Some childCodes =>
            spChoose formulaIndex
              (rowArgsFromCodes target previous childCodes)
        | None => spZero
        end
      else spZero
  | siArgsNil => spZero
  | siArgsCons _ _ => spZero
  end.

Definition totalRowProgram (rank target : nat) : SkolemProgram :=
  Fix lt_wf (fun _ => SkolemProgram) (totalRowProgramStep rank) target.

Lemma belowProgram_ext : forall target
    (f g : forall child, child < target -> SkolemProgram),
  (forall child h, f child h = g child h) ->
  forall child,
    belowProgram target f child = belowProgram target g child.
Proof.
  intros target f g hext child. unfold belowProgram.
  destruct (lt_dec child target) as [h | h]; [apply hext | reflexivity].
Qed.

Lemma rowArgsFromCodes_ext : forall target codes
    (f g : forall child, child < target -> SkolemProgram),
  (forall child h, f child h = g child h) ->
  rowArgsFromCodes target f codes = rowArgsFromCodes target g codes.
Proof.
  intros target codes. induction codes as [|child rest IH];
    intros f g hext; simpl; [reflexivity |].
  rewrite (belowProgram_ext target f g hext child), (IH f g hext).
  reflexivity.
Qed.

Lemma totalRowProgramStep_ext : forall rank target
    (f g : forall child, child < target -> SkolemProgram),
  (forall child h, f child h = g child h) ->
  totalRowProgramStep rank target f = totalRowProgramStep rank target g.
Proof.
  intros rank target f g hext.
  unfold totalRowProgramStep.
  destruct (scheduleSkolemCode target); try reflexivity.
  - now rewrite (belowProgram_ext target f g hext n).
  - now rewrite (belowProgram_ext target f g hext n),
      (belowProgram_ext target f g hext n0).
  - now rewrite (belowProgram_ext target f g hext n),
      (belowProgram_ext target f g hext n0).
  - destruct (n <? length (formula_rank_enum rank)); [|reflexivity].
    destruct (decodeFixedArgs rank n0) as [codes |]; [|reflexivity].
    now rewrite (rowArgsFromCodes_ext target codes f g hext).
Qed.

Theorem totalRowProgram_eq : forall rank target,
  totalRowProgram rank target =
  totalRowProgramStep rank target
    (fun child _ => totalRowProgram rank child).
Proof.
  intros rank target. unfold totalRowProgram.
  apply (@Fix_eq nat lt lt_wf (fun _ => SkolemProgram)
    (totalRowProgramStep rank)).
  intros x f g hext.
  apply totalRowProgramStep_ext. exact hext.
Qed.

Lemma belowProgram_total : forall rank target child,
  child < target ->
  belowProgram target
    (fun child _ => totalRowProgram rank child) child =
  totalRowProgram rank child.
Proof.
  intros rank target child hlt. unfold belowProgram.
  destruct (lt_dec child target); [reflexivity | contradiction].
Qed.

(** Shared opening move of every [totalRowProgram_of_*] case lemma:
    take one step of the program recursion and select the schedule case. *)
Ltac unfold_totalRowStep hs :=
  rewrite totalRowProgram_eq; unfold totalRowProgramStep; rewrite hs.

Theorem totalRowProgram_of_seed : forall rank target,
  scheduleSkolemCode target = siSeed ->
  totalRowProgram rank target = spSeed.
Proof.
  intros rank target hs. now unfold_totalRowStep hs.
Qed.

Theorem totalRowProgram_of_zero : forall rank target,
  scheduleSkolemCode target = siZero ->
  totalRowProgram rank target = spZero.
Proof.
  intros rank target hs. now unfold_totalRowStep hs.
Qed.

Theorem totalRowProgram_of_succ : forall rank target child,
  scheduleSkolemCode target = siSucc child ->
  child < target ->
  totalRowProgram rank target = spSucc (totalRowProgram rank child).
Proof.
  intros rank target child hs hlt. unfold_totalRowStep hs.
  now rewrite belowProgram_total by exact hlt.
Qed.

Theorem totalRowProgram_of_add : forall rank target left right,
  scheduleSkolemCode target = siAdd left right ->
  left < target -> right < target ->
  totalRowProgram rank target =
    spAdd (totalRowProgram rank left) (totalRowProgram rank right).
Proof.
  intros rank target left right hs hl hr. unfold_totalRowStep hs.
  now rewrite !belowProgram_total by assumption.
Qed.

Theorem totalRowProgram_of_mul : forall rank target left right,
  scheduleSkolemCode target = siMul left right ->
  left < target -> right < target ->
  totalRowProgram rank target =
    spMul (totalRowProgram rank left) (totalRowProgram rank right).
Proof.
  intros rank target left right hs hl hr. unfold_totalRowStep hs.
  now rewrite !belowProgram_total by assumption.
Qed.

Theorem totalRowProgram_of_choose : forall rank target formulaIndex
    argsCode childCodes,
  scheduleSkolemCode target = siChoose formulaIndex argsCode ->
  formulaIndex < length (formula_rank_enum rank) ->
  decodeFixedArgs rank argsCode = Some childCodes ->
  (forall child, In child childCodes -> child < target) ->
  totalRowProgram rank target =
    spChoose formulaIndex
      (rowArgsFromCodes target
        (fun child _ => totalRowProgram rank child) childCodes).
Proof.
  intros rank target formulaIndex argsCode childCodes hs hi hdecode hchildren.
  unfold_totalRowStep hs.
  assert (hib : (formulaIndex <? length (formula_rank_enum rank)) = true)
    by (apply Nat.ltb_lt; exact hi).
  rewrite hib, hdecode.
  reflexivity.
Qed.

Theorem totalRowProgram_of_default_choose_index :
  forall rank target formulaIndex argsCode,
  scheduleSkolemCode target = siChoose formulaIndex argsCode ->
  length (formula_rank_enum rank) <= formulaIndex ->
  totalRowProgram rank target = spZero.
Proof.
  intros rank target formulaIndex argsCode hs hi.
  unfold_totalRowStep hs.
  assert (hib : (formulaIndex <? length (formula_rank_enum rank)) = false)
    by (apply Nat.ltb_ge; exact hi).
  now rewrite hib.
Qed.

Theorem totalRowProgram_of_default_choose_args :
  forall rank target formulaIndex argsCode,
  scheduleSkolemCode target = siChoose formulaIndex argsCode ->
  formulaIndex < length (formula_rank_enum rank) ->
  decodeFixedArgs rank argsCode = None ->
  totalRowProgram rank target = spZero.
Proof.
  intros rank target formulaIndex argsCode hs hi hargs.
  unfold_totalRowStep hs.
  assert (hib : (formulaIndex <? length (formula_rank_enum rank)) = true)
    by (apply Nat.ltb_lt; exact hi).
  now rewrite hib, hargs.
Qed.

Theorem totalRowProgram_of_args_instruction : forall rank target,
  (scheduleSkolemCode target = siArgsNil \/
   exists child rest,
     scheduleSkolemCode target = siArgsCons child rest) ->
  totalRowProgram rank target = spZero.
Proof.
  intros rank target [hs | [child [rest hs]]]; now unfold_totalRowStep hs.
Qed.

(** Canonical fixed-rank representatives for arbitrary hull programs. *)
Fixpoint resizeProgramArgs (width : nat) (args : SkolemProgramArgs) :
    SkolemProgramArgs :=
  match width with
  | 0 => spaNil
  | S width' =>
      match args with
      | spaNil => spaCons spZero (resizeProgramArgs width' spaNil)
      | spaCons p rest =>
          spaCons p (resizeProgramArgs width' rest)
      end
  end.

Fixpoint normalizeTraceProgram (rank : nat) (p : SkolemProgram) :
    SkolemProgram :=
  match p with
  | spSeed => spSeed
  | spZero => spZero
  | spSucc q => spSucc (normalizeTraceProgram rank q)
  | spAdd q r =>
      spAdd (normalizeTraceProgram rank q) (normalizeTraceProgram rank r)
  | spMul q r =>
      spMul (normalizeTraceProgram rank q) (normalizeTraceProgram rank r)
  | spChoose i args =>
      if i <? length (formula_rank_enum rank) then
        spChoose i
          (resizeProgramArgs rank (normalizeTraceProgramArgs rank args))
      else spZero
  end
with normalizeTraceProgramArgs (rank : nat) (args : SkolemProgramArgs) :
    SkolemProgramArgs :=
  match args with
  | spaNil => spaNil
  | spaCons p rest =>
      spaCons (normalizeTraceProgram rank p)
        (normalizeTraceProgramArgs rank rest)
  end.

Lemma term_free_lt_rank : forall t n,
  PA.Term.Free n t -> n < term_rank t.
Proof.
  induction t; simpl; intros k hfree.
  - subst k. lia.
  - contradiction.
  - pose proof (IHt k hfree). lia.
  - destruct hfree as [hfree | hfree].
    + pose proof (IHt1 k hfree). lia.
    + pose proof (IHt2 k hfree). lia.
  - destruct hfree as [hfree | hfree].
    + pose proof (IHt1 k hfree). lia.
    + pose proof (IHt2 k hfree). lia.
Qed.

Lemma formula_free_lt_rank : forall f n,
  PA.Formula.Free n f -> n < formula_rank f.
Proof.
  induction f; simpl; intros k hfree.
  - destruct hfree as [hfree | hfree].
    + pose proof (term_free_lt_rank t k hfree). lia.
    + pose proof (term_free_lt_rank t0 k hfree). lia.
  - contradiction.
  - destruct hfree as [hfree | hfree].
    + pose proof (IHf1 k hfree). lia.
    + pose proof (IHf2 k hfree). lia.
  - destruct hfree as [hfree | hfree].
    + pose proof (IHf1 k hfree). lia.
    + pose proof (IHf2 k hfree). lia.
  - destruct hfree as [hfree | hfree].
    + pose proof (IHf1 k hfree). lia.
    + pose proof (IHf2 k hfree). lia.
  - pose proof (IHf (S k) hfree). lia.
  - pose proof (IHf (S k) hfree). lia.
Qed.

Lemma selectorBody_rank_of_index : forall rank i,
  i < length (formula_rank_enum rank) ->
  formula_rank (selectorBody rank i) <= rank.
Proof.
  intros rank i hi. unfold selectorBody.
  apply formula_rank_enum_sound.
  apply nth_In. exact hi.
Qed.

Lemma rawCanonicalSelectorGraph_env_ext : forall (M : RawPAModel)
    body env env' x,
  (forall n, PA.Formula.Free (S n) body -> env n = env' n) ->
  (rawCanonicalSelectorGraph M body env x <->
   rawCanonicalSelectorGraph M body env' x).
Proof.
  intros M body env env' x henv.
  assert (hsat : forall z,
    raw_formula_sat M (scons M z env) body <->
    raw_formula_sat M (scons M z env') body).
  {
    intro z. apply raw_formula_sat_ext_free.
    intros [|n] hfree; [reflexivity |].
    apply henv. exact hfree.
  }
  unfold rawCanonicalSelectorGraph.
  split; intros [[hx hmin] | [hnone hx0]].
  - left. split.
    + apply (proj1 (hsat x)). exact hx.
    + intros y hlt hy. apply (hmin y hlt).
      apply (proj2 (hsat y)). exact hy.
  - right. split; [|exact hx0].
    intros [y hy]. apply hnone. exists y.
    apply (proj2 (hsat y)). exact hy.
  - left. split.
    + apply (proj2 (hsat x)). exact hx.
    + intros y hlt hy. apply (hmin y hlt).
      apply (proj1 (hsat y)). exact hy.
  - right. split; [|exact hx0].
    intros [y hy]. apply hnone. exists y.
    apply (proj1 (hsat y)). exact hy.
Qed.

Lemma rawCanonicalSelector_env_ext : forall (M : RawPAModel),
  RawPASatisfies M -> forall body env env',
  (forall n, PA.Formula.Free (S n) body -> env n = env' n) ->
  rawCanonicalSelector M body env = rawCanonicalSelector M body env'.
Proof.
  intros M hPA body env env' henv.
  apply (rawCanonicalSelectorGraph_functional M
    (raw_order_trichotomy M hPA) body env').
  - apply (proj1 (rawCanonicalSelectorGraph_env_ext M body env env'
      (rawCanonicalSelector M body env) henv)).
    apply rawCanonicalSelector_graph.
    apply raw_definable_least_number_of_pa. exact hPA.
  - apply rawCanonicalSelector_graph.
    apply raw_definable_least_number_of_pa. exact hPA.
Qed.

Lemma rawCanonicalSelector_pBot : forall (M : RawPAModel),
  RawPASatisfies M -> forall env,
  rawCanonicalSelector M PA.pBot env = raw_zero M.
Proof.
  intros M hPA env.
  apply (rawCanonicalSelectorGraph_functional M
    (raw_order_trichotomy M hPA) PA.pBot env).
  - apply rawCanonicalSelector_graph.
    apply raw_definable_least_number_of_pa. exact hPA.
  - right. split.
    + intros [x hx]. exact hx.
    + reflexivity.
Qed.

Lemma selectorBody_out_of_range : forall rank i,
  length (formula_rank_enum rank) <= i ->
  selectorBody rank i = PA.pBot.
Proof.
  intros rank i hi. unfold selectorBody.
  apply nth_overflow. exact hi.
Qed.

Lemma resizeProgramArgs_eval : forall (M : RawPAModel)
    seed selectorRank selector width args n,
  n < width ->
  skolemProgramArgsEval M seed selectorRank selector
    (resizeProgramArgs width args) n =
  skolemProgramArgsEval M seed selectorRank selector args n.
Proof.
  intros M seed selectorRank selector width.
  induction width as [|width IH]; intros args [|n] hn; [lia | lia | |].
  - destruct args; reflexivity.
  - destruct args as [|p rest]; simpl.
    + apply IH. lia.
    + apply IH. lia.
Qed.

Theorem normalizeTraceProgram_eval : forall (M : RawPAModel),
  RawPASatisfies M -> forall seed rank p,
  skolemProgramEval M seed rank (rawCanonicalSelector M)
      (normalizeTraceProgram rank p) =
  skolemProgramEval M seed rank (rawCanonicalSelector M) p.
Proof.
  intros M hPA seed rank.
  apply (SkolemProgram_mutind
    (fun p =>
      skolemProgramEval M seed rank (rawCanonicalSelector M)
          (normalizeTraceProgram rank p) =
      skolemProgramEval M seed rank (rawCanonicalSelector M) p)
    (fun args => forall n,
      skolemProgramArgsEval M seed rank (rawCanonicalSelector M)
          (normalizeTraceProgramArgs rank args) n =
      skolemProgramArgsEval M seed rank (rawCanonicalSelector M) args n)).
  - reflexivity.
  - reflexivity.
  - intros p IH. simpl. now rewrite IH.
  - intros p IHp q IHq. simpl. now rewrite IHp, IHq.
  - intros p IHp q IHq. simpl. now rewrite IHp, IHq.
  - intros i args IHargs. cbn [normalizeTraceProgram].
    destruct (i <? length (formula_rank_enum rank)) eqn:hi.
    + apply Nat.ltb_lt in hi. simpl.
      apply rawCanonicalSelector_env_ext. exact hPA.
      intros n hfree.
      rewrite resizeProgramArgs_eval.
      * apply IHargs.
       * pose proof (selectorBody_rank_of_index rank i hi).
         pose proof (formula_free_lt_rank (selectorBody rank i) (S n) hfree).
        lia.
    + apply Nat.ltb_ge in hi. simpl.
      rewrite selectorBody_out_of_range by exact hi.
      symmetry. apply rawCanonicalSelector_pBot. exact hPA.
  - intro n. destruct n; reflexivity.
  - intros p IHp args IHargs [|n]; simpl.
    + exact IHp.
    + apply IHargs.
Qed.

(** Syntactic invariant recognized by [programCases]. *)
Inductive TraceProgram (rank : nat) : SkolemProgram -> Prop :=
| traceSeed : TraceProgram rank spSeed
| traceZero : TraceProgram rank spZero
| traceSucc : forall p,
    TraceProgram rank p -> TraceProgram rank (spSucc p)
| traceAdd : forall p q,
    TraceProgram rank p -> TraceProgram rank q ->
    TraceProgram rank (spAdd p q)
| traceMul : forall p q,
    TraceProgram rank p -> TraceProgram rank q ->
    TraceProgram rank (spMul p q)
| traceChoose : forall i args,
    i < length (formula_rank_enum rank) ->
    TraceProgramArgs rank rank args ->
    TraceProgram rank (spChoose i args)
with TraceProgramArgs (rank : nat) :
    nat -> SkolemProgramArgs -> Prop :=
| traceArgsNil : TraceProgramArgs rank 0 spaNil
| traceArgsCons : forall width p args,
    TraceProgram rank p -> TraceProgramArgs rank width args ->
    TraceProgramArgs rank (S width) (spaCons p args).

Scheme TraceProgram_ind' := Induction for TraceProgram Sort Prop
with TraceProgramArgs_ind' := Induction for TraceProgramArgs Sort Prop.
Combined Scheme TraceProgram_mutind from TraceProgram_ind',
  TraceProgramArgs_ind'.

Fixpoint skolemProgramArgsLength (args : SkolemProgramArgs) : nat :=
  match args with
  | spaNil => 0
  | spaCons _ rest => S (skolemProgramArgsLength rest)
  end.

Lemma normalizeTraceProgramArgs_length : forall rank args,
  skolemProgramArgsLength (normalizeTraceProgramArgs rank args) =
  skolemProgramArgsLength args.
Proof.
  intros rank args. induction args as [|p rest IH]; simpl; congruence.
Qed.

Lemma traceProgramArgs_resize : forall rank width args,
  TraceProgramArgs rank (skolemProgramArgsLength args) args ->
  TraceProgramArgs rank width (resizeProgramArgs width args).
Proof.
  intros rank width. induction width as [|width IH]; intros args htrace.
  - simpl. constructor.
  - destruct args as [|p rest].
    + simpl. constructor; [constructor |].
      apply IH. constructor.
    + inversion htrace; subst. simpl.
      constructor; [assumption |]. apply IH. assumption.
Qed.

(** Structural normalization and decoder round-trip.  These lemmas isolate
    the purely syntactic part of the total-row construction. *)
Theorem normalizeTraceProgram_trace_mutual : forall rank,
  (forall p,
    TraceProgram rank (normalizeTraceProgram rank p)) /\
  (forall args,
    TraceProgramArgs rank (skolemProgramArgsLength args)
      (normalizeTraceProgramArgs rank args)).
Proof.
  intro rank.
  apply (SkolemProgram_mutind
    (fun p => TraceProgram rank (normalizeTraceProgram rank p))
    (fun args =>
      TraceProgramArgs rank (skolemProgramArgsLength args)
        (normalizeTraceProgramArgs rank args))).
  - constructor.
  - constructor.
  - intros p hp. simpl. now constructor.
  - intros p hp q hq. simpl. now constructor.
  - intros p hp q hq. simpl. now constructor.
  - intros i args hargs. cbn [normalizeTraceProgram].
    destruct (i <? length (formula_rank_enum rank)) eqn:hi.
    + apply Nat.ltb_lt in hi. constructor; [exact hi |].
      apply traceProgramArgs_resize.
      rewrite normalizeTraceProgramArgs_length. exact hargs.
    + constructor.
  - constructor.
  - intros p hp args hargs. simpl. now constructor.
Qed.

Corollary normalizeTraceProgram_trace : forall rank p,
  TraceProgram rank (normalizeTraceProgram rank p).
Proof.
  intros rank p.
  apply (proj1 (normalizeTraceProgram_trace_mutual rank)).
Qed.

Corollary normalizeTraceProgramArgs_trace : forall rank args,
  TraceProgramArgs rank (skolemProgramArgsLength args)
    (normalizeTraceProgramArgs rank args).
Proof.
  intros rank args.
  apply (proj2 (normalizeTraceProgram_trace_mutual rank)).
Qed.

Fixpoint skolemProgramArgsCodes (args : SkolemProgramArgs) : list nat :=
  match args with
  | spaNil => []
  | spaCons p rest =>
      skolemProgramCode p :: skolemProgramArgsCodes rest
  end.

Lemma skolemProgramArgsCodes_length : forall args,
  length (skolemProgramArgsCodes args) = skolemProgramArgsLength args.
Proof.
  intro args. induction args as [|p rest IH]; simpl; congruence.
Qed.

Lemma argsCodeOfCodes_skolemProgramArgsCodes : forall args,
  argsCodeOfCodes (skolemProgramArgsCodes args) =
  skolemProgramArgsCode args.
Proof.
  intro args. induction args as [|p rest IH]; simpl; congruence.
Qed.

Lemma traceProgramArgs_length : forall rank width args,
  TraceProgramArgs rank width args ->
  skolemProgramArgsLength args = width.
Proof.
  intros rank width args htrace. induction htrace; simpl; congruence.
Qed.

Theorem totalRowProgram_trace_mutual : forall rank,
  (forall p, TraceProgram rank p ->
    totalRowProgram rank (skolemProgramCode p) = p) /\
  (forall width args, TraceProgramArgs rank width args ->
    forall target,
      (forall child, In child (skolemProgramArgsCodes args) ->
        child < target) ->
      rowArgsFromCodes target
        (fun child _ => totalRowProgram rank child)
        (skolemProgramArgsCodes args) = args).
Proof.
  intro rank.
  apply (TraceProgram_mutind rank
    (fun p _ => totalRowProgram rank (skolemProgramCode p) = p)
    (fun _ args _ => forall target,
      (forall child, In child (skolemProgramArgsCodes args) ->
        child < target) ->
      rowArgsFromCodes target
        (fun child _ => totalRowProgram rank child)
        (skolemProgramArgsCodes args) = args)).
  - apply totalRowProgram_of_seed.
    rewrite scheduleSkolemCode_program. reflexivity.
  - apply totalRowProgram_of_zero.
    rewrite scheduleSkolemCode_program. reflexivity.
  - intros p htrace IHp.
    pose proof (totalRowProgram_of_succ rank
      (skolemProgramCode (spSucc p)) (skolemProgramCode p)) as hrow.
    rewrite hrow, IHp; [reflexivity | |].
    + rewrite scheduleSkolemCode_program. reflexivity.
    + apply skolemProgramCode_succ_child.
  - intros p q htracep IHp htraceq IHq.
    pose proof (totalRowProgram_of_add rank
      (skolemProgramCode (spAdd p q))
      (skolemProgramCode p) (skolemProgramCode q)) as hrow.
    rewrite hrow, IHp, IHq; [reflexivity | | |].
    + rewrite scheduleSkolemCode_program. reflexivity.
    + apply skolemProgramCode_add_left.
    + apply skolemProgramCode_add_right.
  - intros p q htracep IHp htraceq IHq.
    pose proof (totalRowProgram_of_mul rank
      (skolemProgramCode (spMul p q))
      (skolemProgramCode p) (skolemProgramCode q)) as hrow.
    rewrite hrow, IHp, IHq; [reflexivity | | |].
    + rewrite scheduleSkolemCode_program. reflexivity.
    + apply skolemProgramCode_mul_left.
    + apply skolemProgramCode_mul_right.
  - intros i args hi htraceargs IHargs.
    assert (hlen : length (skolemProgramArgsCodes args) = rank).
    {
      rewrite skolemProgramArgsCodes_length.
      exact (traceProgramArgs_length rank rank args htraceargs).
    }
    assert (hdecode :
      decodeFixedArgs rank (skolemProgramArgsCode args) =
      Some (skolemProgramArgsCodes args)).
    {
      rewrite <- argsCodeOfCodes_skolemProgramArgsCodes, <- hlen.
      apply decodeFixedArgs_codes.
    }
    assert (hchildren : forall child,
      In child (skolemProgramArgsCodes args) ->
      child < skolemProgramCode (spChoose i args)).
    {
      intros child hin.
      eapply Nat.lt_trans with (m := skolemProgramArgsCode args).
      - rewrite <- argsCodeOfCodes_skolemProgramArgsCodes.
        apply argsCodeOfCodes_entry_lt. exact hin.
      - apply skolemProgramCode_choose_args.
    }
    pose proof (totalRowProgram_of_choose rank
      (skolemProgramCode (spChoose i args)) i
      (skolemProgramArgsCode args) (skolemProgramArgsCodes args))
      as hrow.
    rewrite hrow.
    + f_equal. apply IHargs. exact hchildren.
    + rewrite scheduleSkolemCode_program. reflexivity.
    + exact hi.
    + exact hdecode.
    + exact hchildren.
  - intros target hchildren. reflexivity.
  - intros width p args htracep IHp htraceargs IHargs
      target hchildren.
    cbn [skolemProgramArgsCodes rowArgsFromCodes].
    rewrite (belowProgram_total rank target (skolemProgramCode p)).
    + rewrite IHp. f_equal. apply IHargs.
      intros child hin. apply hchildren. now right.
    + apply hchildren. now left.
Qed.

Corollary totalRowProgram_trace : forall rank p,
  TraceProgram rank p ->
  totalRowProgram rank (skolemProgramCode p) = p.
Proof.
  intros rank p htrace.
  apply (proj1 (totalRowProgram_trace_mutual rank) p htrace).
Qed.

(** Programs denoting rows [0], ..., [target], in beta-table order. *)
Definition standardRowPrograms (rank target : nat) : list SkolemProgram :=
  map (totalRowProgram rank) (seq 0 (S target)).

Lemma standardRowPrograms_nth : forall rank target k,
  k <= target ->
  nth_error (standardRowPrograms rank target) k =
    Some (totalRowProgram rank k).
Proof.
  intros rank target k hk. unfold standardRowPrograms.
  rewrite nth_error_map, nth_error_seq.
  assert (hb : (k <? S target) = true) by (apply Nat.ltb_lt; lia).
  now rewrite hb, Nat.add_0_l.
Qed.

(** The total rows through a standard target admit beta parameters which
    are themselves values of finite Skolem programs, hence belong to the
    eventual hull. *)
Theorem finite_total_row_beta_programs :
  forall (M : RawPAModel) seed selectorRank rank target,
  RawPASatisfies M ->
  formula_rank betaCodeExtensionSelectorBody <= selectorRank ->
  exists codeProgram stepProgram,
    forall k, k <= target ->
    RawBetaEntry M
      (skolemProgramEval M seed selectorRank
        (rawCanonicalSelector M) (totalRowProgram rank k))
      (skolemProgramEval M seed selectorRank
        (rawCanonicalSelector M) codeProgram)
      (skolemProgramEval M seed selectorRank
        (rawCanonicalSelector M) stepProgram)
      (rawNumeralValue M k).
Proof.
  intros M seed selectorRank rank target hPA hsupport.
  destruct (finite_beta_code_in_canonical_skolem_hull
    M seed selectorRank hPA hsupport
    (standardRowPrograms rank target))
    as [codeProgram [stepProgram htable]].
  exists codeProgram, stepProgram.
  intros k hk.
  unfold RawBetaCodesList in htable.
  apply (htable k
    (skolemProgramEval M seed selectorRank
      (rawCanonicalSelector M) (totalRowProgram rank k))).
  rewrite nth_error_map, standardRowPrograms_nth by exact hk.
  reflexivity.
Qed.

End PATotalProgramRows.
