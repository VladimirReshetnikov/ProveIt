(** The canonical footprint, independent of any complete candidate program. *)
From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia.
From K230 Require Import RM.
From KLocal Require Export LocalProgram MacroProgram.
Import ListNotations.
Definition macro_nodes_used : list nat := [115; 116; 117; 118; 119; 120; 121; 122; 123; 130; 131; 132; 133; 134; 135; 136; 137; 138; 154; 155; 156; 157; 158; 159; 160; 162; 163; 164; 165; 166; 167; 168; 169; 170; 171; 172; 173; 174; 175; 176; 177; 178; 179; 180; 181; 182; 183; 184; 185; 186; 187; 188; 189; 190; 191; 192; 193; 194; 195; 196; 197; 198; 199; 200; 201; 202; 203; 204; 205; 206; 207; 208; 209; 210; 211; 212; 213; 214; 215; 216; 217; 218; 300; 461; 462; 463; 464; 465; 466].
Definition macro_roots : list nat := [115; 116; 117; 119; 121; 123; 130; 131; 132; 133; 136; 154; 158; 160; 162; 166; 168; 170; 171; 174; 175; 176; 177; 178; 180; 181; 182; 183; 192; 193; 194; 197; 198; 199; 200; 201; 203; 205; 207; 208; 209; 211; 212; 214; 215; 216; 217; 218; 462; 463; 464; 465; 466].
Definition macro_ok (n : nat) : bool :=
  (n <? 467) && existsb (Nat.eqb n) macro_nodes_used.
Lemma macro_bound n : macro_ok n = true -> n < 467.
Proof.
  unfold macro_ok. rewrite andb_true_iff. intros [H _]. now apply Nat.ltb_lt.
Qed.
Theorem all_macro_roots_inside : forallb macro_ok macro_roots = true.
Proof. vm_compute. reflexivity. Qed.
