From Coq Require Import ZArith.
Require Import MarkerFold MarkerTables.

Lemma M124_certificate :
  check K215 M124 124 127 254 62 14 138 8 59=true.
Proof. vm_compute. reflexivity. Qed.
Theorem M124_all_tapes h t :
  Halts K215 254 (C 0 h t) <-> Halts M124 254 (C 0 h t).
Proof. exact (checked_fold K215 M124 124 127 254 62 14 138 8 59
  M124_certificate h t). Qed.
Print Assumptions M124_all_tapes.

Lemma FM215_certificate :
  check K215 FM215 124 127 254 62 14 138 8 109=true.
Proof. vm_compute. reflexivity. Qed.
Theorem FM215_all_tapes h t :
  Halts K215 254 (C 0 h t) <-> Halts FM215 254 (C 0 h t).
Proof. exact (checked_fold K215 FM215 124 127 254 62 14 138 8 109
  FM215_certificate h t). Qed.
Print Assumptions FM215_all_tapes.

Lemma M125_certificate :
  check K215 M125 124 127 254 62 14 138 8 125=true.
Proof. vm_compute. reflexivity. Qed.
Theorem M125_all_tapes h t :
  Halts K215 254 (C 0 h t) <-> Halts M125 254 (C 0 h t).
Proof. exact (checked_fold K215 M125 124 127 254 62 14 138 8 125
  M125_certificate h t). Qed.
Print Assumptions M125_all_tapes.

Theorem M125_blank_transfer (P : Prop) :
  ((~ Halts K215 254 (C 0 0 (fun _ => false))) <-> P) ->
  ((~ Halts M125 254 (C 0 0 (fun _ => false))) <-> P).
Proof. pose proof (M125_all_tapes 0 (fun _ => false)). tauto. Qed.
Print Assumptions M125_blank_transfer.
