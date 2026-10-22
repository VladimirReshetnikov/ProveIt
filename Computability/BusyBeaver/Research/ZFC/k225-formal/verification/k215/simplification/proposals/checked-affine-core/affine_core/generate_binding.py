#!/usr/bin/env python3
"""Generate compact literal addresses and finite source-to-graph checks."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
raw=(ROOT/'leaves.json').read_bytes()
leaves=json.loads(raw)
G={int(k):v for k,v in json.loads((ROOT/'input_graph.json').read_text()).items()}

def code(bits):
    if set(bits)-{'0','1'}:
        raise ValueError('Nonbinary source location')
    return (1<<len(bits)) + sum(int(b)<<i for i,b in enumerate(bits))

def tree(items):
    if not items:
        return 'Empty'
    mid=len(items)//2
    k,v=items[mid]
    return f'(Branch {tree(items[:mid])} {k}%N {v}%positive\n {tree(items[mid+1:])})'

for side in ['source','reference']:
    for v,g in G.items():
        if leaves[side][v][1] != g['op']:
            raise ValueError(f'{side} ordinal {v} has a different operation')

text=r'''From Coq Require Import Lists.List Bool Arith NArith.
From K230 Require Import RM RMEquiv.
From K230P Require Import Bisim230.
From K215F Require Import Prog215 DagPerm.
Require Import PathCodec NormalizedBisim DrainCore CoreContraction K215DrainData SourceGraphBridge.
Import ListNotations.

'''
for side in ['source','reference']:
    text+=f'Definition locations_{side} : K215DrainData.tree positive :=\n'
    text+=tree([(v,code(leaves[side][v][0])) for v in sorted(G)])+'.\n\n'
    text+=f'''Definition loc_{side} (v : N) : list bool :=
  match K215DrainData.lookup locations_{side} v with
  | Some c => decode_path c
  | None => []
  end.

'''

text+=r'''
Theorem source_nodes_checked :
  forallb (node_ok (ptree p215) k215 loc_source) vertices = true.
Proof. vm_compute; reflexivity. Qed.

Theorem reference_nodes_checked :
  forallb (node_ok (ptree dagPerm) k215 loc_reference) vertices = true.
Proof. vm_compute; reflexivity. Qed.

Theorem source_valid v x : k215 v = Some x -> node_ok (ptree p215) k215 loc_source v = true.
Proof.
  intro H; pose proof source_nodes_checked as A; rewrite forallb_forall in A.
  apply A; eapply defined_vertex_member; eauto.
Qed.

Theorem reference_valid v x : k215 v = Some x -> node_ok (ptree dagPerm) k215 loc_reference v = true.
Proof.
  intro H; pose proof reference_nodes_checked as A; rewrite forallb_forall in A.
  apply A; eapply defined_vertex_member; eauto.
Qed.

Theorem source_graph_bound v x R : k215 v = Some x ->
  rm_halts p215 (loc_source v,R) <-> DrainCore.halts k215 v R.
Proof.
  apply source_graph_halts_iff; [exact source_valid|exact k215_closed].
Qed.

Theorem reference_graph_bound v x R : k215 v = Some x ->
  rm_halts dagPerm (loc_reference v,R) <-> DrainCore.halts k215 v R.
Proof.
  apply source_graph_halts_iff; [exact reference_valid|exact k215_closed].
Qed.

Theorem source_entry : ipeq [] (loc_source 0%N).
Proof. apply NormalizedBisim.ibeq_ok; vm_compute; reflexivity. Qed.
Theorem reference_entry : ipeq [] (loc_reference 0%N).
Proof. apply NormalizedBisim.ibeq_ok; vm_compute; reflexivity. Qed.

Theorem source_entry_halts R : rm_halts p215 ([],R) <-> rm_halts p215 (loc_source 0%N,R).
Proof.
  split; apply NormalizedBisim.halts_ipeq; [exact source_entry|apply ipeq_sym; exact source_entry].
Qed.

Theorem reference_entry_halts R : rm_halts dagPerm ([],R) <-> rm_halts dagPerm (loc_reference 0%N,R).
Proof.
  split; apply NormalizedBisim.halts_ipeq; [exact reference_entry|apply ipeq_sym; exact reference_entry].
Qed.

Theorem entry_node : k215 0%N = Some (Test 8 (Arc 9%N []) (Arc 2%N [])).
Proof. vm_compute; reflexivity. Qed.

Theorem p215_graph_halts R : rm_halts p215 ([],R) <-> DrainCore.halts k215 0%N R.
Proof.
  rewrite source_entry_halts; eapply source_graph_bound; exact entry_node.
Qed.

Theorem dagPerm_graph_halts R : rm_halts dagPerm ([],R) <-> DrainCore.halts k215 0%N R.
Proof.
  rewrite reference_entry_halts; eapply reference_graph_bound; exact entry_node.
Qed.

Theorem p215_core_halts R : rm_halts p215 ([],R) <-> core_halts 6 k215 0%N R.
Proof. rewrite p215_graph_halts; symmetry; apply core_halts_iff. Qed.

Theorem dagPerm_core_halts R : rm_halts dagPerm ([],R) <-> core_halts 6 k215 0%N R.
Proof. rewrite dagPerm_graph_halts; symmetry; apply core_halts_iff. Qed.

(** Exact replacement for the existing public source-correspondence theorem. *)
Theorem p215_dagPerm_affine : forall R,
  rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).
Proof. intro R; rewrite p215_core_halts, dagPerm_core_halts; reflexivity. Qed.

Print Assumptions p215_core_halts.
Print Assumptions dagPerm_core_halts.
Print Assumptions p215_dagPerm_affine.
'''
(ROOT/'K215GraphBinding.v').write_text(text)
(ROOT/'locations_generation.json').write_text(json.dumps({
    'input_leaves_sha256':hashlib.sha256(raw).hexdigest(),
    'generated_source_sha256':hashlib.sha256(text.encode()).hexdigest(),
    'source_locations':len(G),'reference_locations':len(G),'source_bytes':len(text.encode()),
    'max_source_depth':max(len(leaves['source'][v][0]) for v in G),
    'max_reference_depth':max(len(leaves['reference'][v][0]) for v in G),
    'status':'generated; kernel results recorded separately',
},indent=2)+'\n')
print('Generated K215GraphBinding.v',len(text.encode()),'bytes')
