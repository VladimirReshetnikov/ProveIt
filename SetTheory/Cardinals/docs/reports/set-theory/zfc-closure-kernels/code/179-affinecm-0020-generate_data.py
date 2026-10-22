#!/usr/bin/env python3
"""Render the literal K215 checkpoint graph and kernel-checked drain tests.

The generator is not a logical premise.  Coq checks the printed graph and all
finite tests.  The JSON SHA-256 ties the literal to the existing affine-cores
proposal; the source-to-checkpoint compiler is outside this packet's scope.
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
raw = (ROOT / 'input_graph.json').read_bytes()
G = {int(k): v for k, v in json.loads(raw).items()}
ranks = {int(k): v for k, v in json.loads((ROOT / 'drain_ranks.json').read_text()).items()}

def pair(x):
    r, n = x
    if not (type(r) is int and 0 <= r < 9 and type(n) is int and n >= 0):
        raise ValueError(f'Invalid increment: {x}')
    return f'({r},{n})'

def arc(x):
    target, inc = x
    if target not in G:
        raise ValueError(f'Missing graph successor {target}')
    return f'(Arc {target}%N [' + ';'.join(map(pair,inc)) + '])'

def node(x):
    op, succ = x['op'], x['successors']
    if op == ['halt']:
        if succ:
            raise ValueError('Halt has successors')
        return 'Halt'
    if not (len(op)==2 and op[0]=='decnz' and type(op[1]) is int and 0<=op[1]<9 and len(succ)==2):
        raise ValueError(f'Invalid test {x}')
    return f'(Test {op[1]} {arc(succ[0])} {arc(succ[1])})'

def tree(items, render):
    if not items:
        return 'Empty'
    mid=len(items)//2
    k,v=items[mid]
    return f'(Branch {tree(items[:mid],render)} {k}%N {render(v)}\n {tree(items[mid+1:],render)})'

graph_literal = tree(sorted(G.items()),node)
rank_literal = tree(sorted(ranks.items()),str)
text = r'''From Coq Require Import Lists.List Arith.PeanoNat NArith Lia.
Require Import DrainCore CoreContraction.
Import ListNotations.

Inductive tree (A : Type) :=
| Empty : tree A
| Branch : tree A -> N -> A -> tree A -> tree A.
Arguments Empty {A}.
Arguments Branch {A}.

Fixpoint lookup {A} (t : tree A) (q : N) : option A :=
  match t with
  | Empty => None
  | Branch l k a r =>
      match N.compare q k with
      | Eq => Some a | Lt => lookup l q | Gt => lookup r q
      end
  end.

Fixpoint elements {A} (t : tree A) : list (N * A) :=
  match t with
  | Empty => []
  | Branch l k a r => (k,a) :: elements l ++ elements r
  end.

Lemma lookup_member {A} (t : tree A) q a :
  lookup t q = Some a -> In (q,a) (elements t).
Proof.
  induction t as [|l IHl k x r IHr]; simpl; [discriminate|].
  destruct (N.compare q k) eqn:E; intro H.
  - apply N.compare_eq_iff in E; subst. inversion H; subst; left; reflexivity.
  - right; apply in_or_app; left; apply IHl; assumption.
  - right; apply in_or_app; right; apply IHr; assumption.
Qed.

Definition k215_tree : tree node :=
''' + graph_literal + r'''.

Definition k215 : graph := lookup k215_tree.
Definition vertices : list N := map fst (elements k215_tree).
Definition drains : list N := filter (drainb k215) vertices.
Definition core : list N := filter (fun v => negb (drainb k215 v)) vertices.

Definition rank_tree : tree nat :=
''' + rank_literal + r'''.

Definition drain_rank (v : N) : nat :=
  match lookup rank_tree v with Some k => k | None => 0 end.

Definition rank_ok (v : N) : bool :=
  match k215 v with
  | Some (Test _ _ b) =>
      Nat.ltb (drain_rank (destination b)) (drain_rank v) && Nat.leb (drain_rank v) 6
  | _ => false
  end.

Theorem vertex_count : length vertices = 1426.
Proof. vm_compute; reflexivity. Qed.
Theorem drain_count : length drains = 1059.
Proof. vm_compute; reflexivity. Qed.
Theorem core_count : length core = 367.
Proof. vm_compute; reflexivity. Qed.

Theorem vertices_nodup : NoDup vertices.
Proof.
  assert (E : nodup N.eq_dec vertices = vertices) by (vm_compute; reflexivity).
  rewrite <- E; apply NoDup_nodup.
Qed.

Theorem core_nodup : NoDup core.
Proof. apply NoDup_filter; exact vertices_nodup. Qed.

Definition definedb (v : N) : bool :=
  match k215 v with Some _ => true | None => false end.

Theorem vertices_defined_checked : forallb definedb vertices = true.
Proof. vm_compute; reflexivity. Qed.

Theorem member_defined v : In v vertices -> exists x, k215 v = Some x.
Proof.
  intro Hv; pose proof vertices_defined_checked as H.
  rewrite forallb_forall in H; specialize (H v Hv).
  unfold definedb in H; destruct (k215 v) as [x|] eqn:E; [eauto|discriminate].
Qed.

Theorem all_drains_valid : forall v, In v drains -> drainb k215 v = true.
Proof.
  intros v H; apply filter_In in H; exact (proj2 H).
Qed.

Theorem drain_ranks_checked : forallb rank_ok drains = true.
Proof. vm_compute; reflexivity. Qed.

Theorem drain_rank_decreases v r a b :
  In v drains -> k215 v = Some (Test r a b) ->
  drain_rank (destination b) < drain_rank v /\ drain_rank v <= 6.
Proof.
  intros Hv E.
  pose proof drain_ranks_checked as H.
  rewrite forallb_forall in H; specialize (H v Hv).
  unfold rank_ok in H; rewrite E in H.
  rewrite Bool.andb_true_iff, Nat.ltb_lt, Nat.leb_le in H; exact H.
Qed.

Theorem normalization_targets_checked :
  forallb (fun v => existsb (N.eqb (target 6 k215 v)) core) vertices = true.
Proof. vm_compute; reflexivity. Qed.

Theorem normalizes_to_core v : In v vertices -> In (target 6 k215 v) core.
Proof.
  intro Hv; pose proof normalization_targets_checked as H.
  rewrite forallb_forall in H; specialize (H v Hv).
  apply existsb_exists in H; destruct H as [w [Hw E]].
  apply N.eqb_eq in E; subst; assumption.
Qed.

Theorem every_vertex_normalizes v :
  In v vertices -> drainb k215 (target 6 k215 v) = false.
Proof.
  intro Hv; pose proof (normalizes_to_core v Hv) as H.
  apply filter_In in H; destruct H as [_ H]; apply Bool.negb_true_iff in H; exact H.
Qed.

Theorem defined_vertex_member v x : k215 v = Some x -> In v vertices.
Proof.
  intro H; unfold k215 in H; apply lookup_member in H.
  apply (in_map fst) in H; exact H.
Qed.

Theorem all_defined_normalize_to_core v x R :
  k215 v = Some x -> In (fst (normalize 6 k215 v R)) core.
Proof.
  intro H; rewrite normalize_target.
  apply normalizes_to_core; eapply defined_vertex_member; eauto.
Qed.

Theorem k215_normalization_correct v R :
  halts k215 v R <->
    halts k215 (fst (normalize 6 k215 v R)) (snd (normalize 6 k215 v R)).
Proof. apply normalize_halts_iff. Qed.

Theorem entry_is_core : In 0%N core.
Proof.
  assert (H : existsb (N.eqb 0%N) core = true) by (vm_compute; reflexivity).
  apply existsb_exists in H; destruct H as [w [Hw E]].
  apply N.eqb_eq in E; subst; assumption.
Qed.

Definition destinations_ok (x : N * node) : bool :=
  match snd x with
  | Halt => true
  | Test _ a b =>
      existsb (N.eqb (destination a)) vertices && existsb (N.eqb (destination b)) vertices
  end.

Theorem graph_closed_checked : forallb destinations_ok (elements k215_tree) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma destination_member v r a b : k215 v = Some (Test r a b) ->
  In (destination a) vertices /\ In (destination b) vertices.
Proof.
  intro Hv; unfold k215 in Hv; apply lookup_member in Hv.
  pose proof graph_closed_checked as H; rewrite forallb_forall in H.
  specialize (H (v, Test r a b) Hv); simpl in H.
  apply Bool.andb_true_iff in H; destruct H as [Ha Hb].
  split; [apply existsb_exists in Ha; destruct Ha as [w [Hw E]]|
          apply existsb_exists in Hb; destruct Hb as [w [Hw E]]];
    apply N.eqb_eq in E; subst; assumption.
Qed.

Theorem k215_closed v r a b : k215 v = Some (Test r a b) ->
  (exists x, k215 (destination a) = Some x) /\
  (exists x, k215 (destination b) = Some x).
Proof.
  intro H; destruct (destination_member _ _ _ _ H) as [Ha Hb].
  split; apply member_defined; assumption.
Qed.

Theorem step_destination_member v R w Q :
  step k215 v R w Q -> In w vertices.
Proof.
  intro H; destruct H.
  - exact (proj2 (destination_member _ _ _ _ H)).
  - exact (proj1 (destination_member _ _ _ _ H)).
Qed.

Theorem accelerated_successor_in_core v R w Q :
  step k215 v R w Q -> In (fst (normalize 6 k215 w Q)) core.
Proof.
  intro H; rewrite normalize_target.
  apply normalizes_to_core; eapply step_destination_member; eauto.
Qed.

Theorem k215_core_halts_iff v R : core_halts 6 k215 v R <-> halts k215 v R.
Proof. apply core_halts_iff. Qed.

Theorem k215_normalized_core_halts_iff v R :
  core_halts 6 k215 (fst (normalize 6 k215 v R)) (snd (normalize 6 k215 v R))
  <-> halts k215 v R.
Proof. apply normalized_core_halts_iff. Qed.

Theorem core_has_one_halt :
  length (filter (fun v => match k215 v with Some Halt => true | _ => false end) core) = 1.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions k215_core_halts_iff.
Print Assumptions k215_normalized_core_halts_iff.
Print Assumptions accelerated_successor_in_core.

Print Assumptions k215_normalization_correct.
Print Assumptions all_defined_normalize_to_core.
Print Assumptions drain_rank_decreases.
'''
(ROOT/'K215DrainData.v').write_text(text)
summary={
    'input_graph_sha256':hashlib.sha256(raw).hexdigest(),
    'rank_input_sha256':hashlib.sha256((ROOT/'drain_ranks.json').read_bytes()).hexdigest(),
    'generated_source_sha256':hashlib.sha256(text.encode()).hexdigest(),
    'vertices':len(G), 'rank_records':len(ranks),
    'source_bytes':len(text.encode()),
    'status':'generated; kernel results are recorded by build.py',
}
(ROOT/'generation.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
