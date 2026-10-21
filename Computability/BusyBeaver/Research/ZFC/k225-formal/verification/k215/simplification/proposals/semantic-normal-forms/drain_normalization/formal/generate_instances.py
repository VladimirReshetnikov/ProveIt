"""Generate untrusted literal data; Coq checks all semantic obligations."""
from pathlib import Path
import json,hashlib
B=Path(__file__).resolve().parent
src=B.parent/'reference/structural/input_graph.json'
ranksrc=B.parent/'reference/structural/drain_ranks.json'
G=json.loads(src.read_text()); ranks=json.loads(ranksrc.read_text())
def ls(xs):return '['+';'.join(map(str,xs))+']'
def vec(xs):
 v=[0]*9
 for r,n in xs:
  if type(r)!=int or type(n)!=int or not 0<=r<9 or n<0:raise ValueError('bad increment')
  v[r]+=n
 return ls(v)
rows=[]
for k,x in sorted(G.items(),key=lambda t:int(t[0])):
 if x['op']==['halt']:n='Stop'
 else:
  assert x['op'][0]=='decnz'
  (nz,c),(z,d)=x['successors'];n=f'Test {x["op"][1]} {nz}%N {vec(c)} {z}%N {vec(d)}'
 rows.append(f'({k}%N,{n})')
drains=[int(k) for k in ranks]
text='''From Coq Require Import Arith Lia List Bool NArith.
Require Import DrainAffine.
Import ListNotations.
Definition literal_nodes : list (N * node) := [\n'''+ ';\n'.join(rows)+'].\n'
text+='Definition literal_graph (v:N) : node := lookup v literal_nodes.\n'
text+='Definition drain_ids : list N := '+ls(f'{x}%N' for x in drains)+'.\n'
text+='Definition literal_ranks : list (N * nat) := '+ls(f'({k}%N,{v})' for k,v in sorted(ranks.items(),key=lambda t:int(t[0])))+'.\n'
text+='''Fixpoint nat_lookup (v:N) (xs:list (N*nat)) : nat :=
 match xs with [] => 0 | (w,n)::ys => if N.eqb v w then n else nat_lookup v ys end.
Definition literal_rank (v:N) := nat_lookup v literal_ranks.
Theorem vertex_count : length literal_nodes = 1426. Proof. vm_compute; reflexivity. Qed.
Theorem drain_count : length drain_ids = 1059. Proof. vm_compute; reflexivity. Qed.
Theorem all_drain_checks : forallb (drain_check literal_graph) drain_ids = true.
Proof. vm_compute; reflexivity. Qed.
Theorem drain_coverage : drain_ids = filter (drain_check literal_graph) (map fst literal_nodes).
Proof. vm_compute; reflexivity. Qed.
Theorem all_rank_checks : forallb (rank_check literal_graph literal_rank) (map fst literal_nodes) = true.
Proof. vm_compute; reflexivity. Qed.
Theorem literal_rank_ok : rank_ok literal_graph literal_rank.
Proof. apply rank_list_sound; exact all_rank_checks. Qed.
Lemma nat_lookup_bound : forall xs b,
 forallb (fun p => Nat.leb (snd p) b) xs = true -> forall v, nat_lookup v xs <= b.
Proof.
 induction xs as [|[w n] xs IH]; intros b H v; [simpl; lia|].
 cbn in H. apply andb_true_iff in H as [B Rest]. apply Nat.leb_le in B.
 cbn. destruct (N.eqb v w); auto.
Qed.
Theorem all_rank_bounds : forallb (fun p => Nat.leb (snd p) 6) literal_ranks = true.
Proof. vm_compute; reflexivity. Qed.
Theorem literal_rank_bound : forall v, literal_rank v <= 6.
Proof. intro v; apply nat_lookup_bound; exact all_rank_bounds. Qed.
Theorem concrete_normalize_core : forall v R,
 drain_check literal_graph (fst (normalize 6 literal_graph (v,R))) = false.
Proof. intros; apply normalize_core with (rank:=literal_rank); auto using literal_rank_ok,literal_rank_bound. Qed.
Theorem concrete_normalize_preserves_halting : forall v R, length R = 9 ->
 (Halts literal_graph (v,R) <-> Halts literal_graph (normalize 6 literal_graph (v,R))).
Proof. intros; apply normalize_halts_iff; auto. Qed.
Theorem concrete_drain_contract : forall v, In v drain_ids ->
 exists r c w d, literal_graph v = Test r v c w d /\\ get c r = 0 /\\ r < 9 /\\
 forall R, length R = 9 ->
 Run literal_graph (S (get R r)) (v,R) (w,affine R r c d) /\\
 (Halts literal_graph (v,R) <-> Halts literal_graph (w,affine R r c d)).
Proof.
 intros v H. apply drain_check_sound.
 pose proof all_drain_checks as C. apply forallb_forall with (x:=v) in C; auto.
Qed.
Print Assumptions concrete_normalize_core.
Print Assumptions concrete_normalize_preserves_halting.
Print Assumptions concrete_drain_contract.
'''
# Match the literal source's vertex order, not the preexisting rank insertion order.
text += r"""
Fixpoint distinct_labels (xs:list N) : bool :=
 match xs with [] => true | x::ys => negb (existsb (N.eqb x) ys) && distinct_labels ys end.
Definition target_check (p:N*node) : bool :=
 match snd p with
 | Stop => true
 | Test r nz c z d => existsb (N.eqb nz) (map fst literal_nodes) &&
                     existsb (N.eqb z) (map fst literal_nodes)
 end.
Theorem literal_labels_unique : distinct_labels (map fst literal_nodes) = true.
Proof. vm_compute; reflexivity. Qed.
Theorem literal_targets_closed : forallb target_check literal_nodes = true.
Proof. vm_compute; reflexivity. Qed.
Theorem literal_core_count : length (filter (fun v => negb (drain_check literal_graph v)) (map fst literal_nodes)) = 367.
Proof. vm_compute; reflexivity. Qed.
Theorem literal_stop_count : length (filter (fun p => match snd p with Stop => true | _ => false end) literal_nodes) = 1.
Proof. vm_compute; reflexivity. Qed.
Theorem initial_is_core : drain_check literal_graph 0%N = false.
Proof. vm_compute; reflexivity. Qed.
Print Assumptions literal_targets_closed.
Print Assumptions literal_labels_unique.
"""
text=text.replace('Definition drain_ids : list N := '+ls(f'{x}%N' for x in drains), 'Definition drain_ids : list N := '+ls(f'{x}%N' for x in sorted(drains)))
(B/'DrainInstances.v').write_text(text)
(B/'input_binding.json').write_text(json.dumps({'repository':'VladimirReshetnikov/ProveIt','commit':'56e487ce8fa4cf63ad169ffe0cd2944e9fc62dd3','input_graph_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'rank_sha256':hashlib.sha256(ranksrc.read_bytes()).hexdigest(),'generated_source_sha256':hashlib.sha256(text.encode()).hexdigest(),'graph_nodes':len(G),'drains':len(drains),'bound':6,'scope':'Canonical graph: source-to-graph adequacy and compact matrix representation remain outside this theorem'},indent=2)+'\n')
print('Generated',len(text),'bytes,',len(G),'nodes,',len(drains),'drains')
