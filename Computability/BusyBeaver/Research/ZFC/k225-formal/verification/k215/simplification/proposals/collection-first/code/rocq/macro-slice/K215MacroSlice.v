(** Generated untrusted support; all finite claims checked below. *)
From Coq Require Import List.
From K230 Require Import RM.
From K215F Require Import DagPerm.
From K217F Require Import DagDom.
From K218F Require Import Dag219.
Require Import RMSlice.
Import ListNotations.

Definition macro_roots : list nat := [115; 116; 117; 119; 121; 123; 130; 131; 132; 133; 136; 154; 158; 160; 162; 166; 168; 170; 171; 174; 175; 176; 177; 178; 180; 181; 182; 183; 192; 193; 194; 197; 198; 199; 200; 201; 203; 205; 207; 208; 209; 211; 212; 214; 215; 216; 217; 218; 462; 463; 464; 465; 466].
Definition macro_support : list nat := [115; 116; 117; 118; 119; 120; 121; 122; 123; 130; 131; 132; 133; 134; 135; 136; 137; 138; 154; 155; 156; 157; 158; 159; 160; 162; 163; 164; 165; 166; 167; 168; 169; 170; 171; 172; 173; 174; 175; 176; 177; 178; 179; 180; 181; 182; 183; 184; 185; 186; 187; 188; 189; 190; 191; 192; 193; 194; 195; 196; 197; 198; 199; 200; 201; 202; 203; 204; 205; 206; 207; 208; 209; 210; 211; 212; 213; 214; 215; 216; 217; 218; 300; 461; 462; 463; 464; 465; 466].

Lemma perm_dom_slice : check_slice dagPerm dagDom macro_support = true.
Proof. vm_compute. reflexivity. Qed.

Lemma perm_219_slice : check_slice dagPerm dag219 macro_support = true.
Proof. vm_compute. reflexivity. Qed.

Lemma macro_roots_covered :
  forallb (fun n => allowedb macro_support (ENode n)) macro_roots = true.
Proof. vm_compute. reflexivity. Qed.

Lemma root_allowed n : In n macro_roots -> allowed macro_support (ENode n).
Proof.
  intro Hn. apply allowedb_sound.
  exact (proj1 (forallb_forall _ _) macro_roots_covered n Hn).
Qed.

Theorem macro_run_215_217 n R x R' : In n macro_roots ->
  (run dagPerm (ENode n) R x R' <-> run dagDom (ENode n) R x R').
Proof.
  intro Hn. exact (checked_run_iff _ _ _ perm_dom_slice _ _ _ _ (root_allowed n Hn)).
Qed.

Theorem macro_run_215_218 n R x R' : In n macro_roots ->
  (run dagPerm (ENode n) R x R' <-> run dag219 (ENode n) R x R').
Proof.
  intro Hn. exact (checked_run_iff _ _ _ perm_219_slice _ _ _ _ (root_allowed n Hn)).
Qed.

Print Assumptions macro_run_215_217.
Print Assumptions macro_run_215_218.
