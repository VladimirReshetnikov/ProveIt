(** The full old API is restated verbatim; all names must still typecheck. *)
From ZF Require Import Logic L1_LDef L1_LProp.
From ZF Require Import L1_LMeta.
From K215F Require Import L224Def L224Prop L224Meta.
Example standard_llp5 (w0 w1 : wff) : lprov (Wim (Wim w0 w1) (Wim (Wim (Wn w0) w0) w1)).
Proof. exact (llp5 w0 w1). Qed.
Example standard_llp7 (w0 w1 w2 : wff) : lprov (Wim (Wim (Wim (Wn w0) w1) w2) (Wim w0 w2)).
Proof. exact (llp7 w0 w1 w2). Qed.
Example standard_llp8 (w0 : wff) : lprov (Wim w0 w0).
Proof. exact (llp8 w0). Qed.
Example standard_llp9 (w0 w1 : wff) : lprov (Wim (Wn (Wim w0 w0)) w1).
Proof. exact (llp9 w0 w1). Qed.
Example standard_llp12 (w0 w1 w2 : wff) : lprov (Wim w0 (Wim (Wim w1 w2) (Wim (Wn w0) w2))).
Proof. exact (llp12 w0 w1 w2). Qed.
Example standard_llp14 (w0 w1 w2 : wff) : lprov (Wim (Wim w0 w1) (Wim (Wn (Wim w2 w2)) w1)).
Proof. exact (llp14 w0 w1 w2). Qed.
Example standard_llp15 (w0 w1 w2 : wff) : lprov (Wim w0 (Wim (Wn (Wim w1 w1)) w2)).
Proof. exact (llp15 w0 w1 w2). Qed.
Example standard_llp26 (w0 w1 w2 w3 : wff) : lprov (Wim (Wim (Wim (Wn (Wim w0 w0)) w1) w2) (Wim w3 w2)).
Proof. exact (llp26 w0 w1 w2 w3). Qed.
Example standard_llp27 (w0 w1 : wff) : lprov (Wim w0 (Wim w1 w1)).
Proof. exact (llp27 w0 w1). Qed.
Example standard_llp29 (w0 w1 w2 : wff) : lprov (Wim (Wim (Wim w0 w0) w1) (Wim w2 w1)).
Proof. exact (llp29 w0 w1 w2). Qed.
Example standard_llp31 (w0 w1 : wff) : lprov (Wim w0 (Wim (Wim (Wn w1) w1) w1)).
Proof. exact (llp31 w0 w1). Qed.
Example standard_llp44 (w0 w1 w2 : wff) : lprov (Wim (Wim (Wim (Wim (Wn w0) w0) w0) w1) (Wim w2 w1)).
Proof. exact (llp44 w0 w1 w2). Qed.
Example standard_llp118 (w0 w1 w2 w3 : wff) : lprov (Wim (Wim (Wim w0 w1) w2) (Wim (Wim (Wim (Wn w0) w3) w1) w2)).
Proof. exact (llp118 w0 w1 w2 w3). Qed.
Example standard_llp119 (w0 w1 : wff) : lprov (Wim (Wim (Wim (Wn (Wn w0)) w1) w0) w0).
Proof. exact (llp119 w0 w1). Qed.
Example standard_llp135 (w0 w1 w2 w3 : wff) : lprov (Wim (Wim (Wim (Wim w0 w1) (Wim (Wn w2) w1)) w3) (Wim w2 w3)).
Proof. exact (llp135 w0 w1 w2 w3). Qed.
Example standard_llp136 (w0 w1 w2 : wff) : lprov (Wim w0 (Wim w1 (Wim (Wn w0) w2))).
Proof. exact (llp136 w0 w1 w2). Qed.
Example standard_llp143 (w0 w1 w2 w3 : wff) : lprov (Wim (Wim (Wim w0 (Wim (Wn w1) w2)) w3) (Wim w1 w3)).
Proof. exact (llp143 w0 w1 w2 w3). Qed.
Example standard_llp241 (w0 w1 w2 w3 : wff) : lprov (Wim (Wim (Wim (Wim w0 w1) (Wim w2 w1)) w3) (Wim (Wim w2 w0) w3)).
Proof. exact (llp241 w0 w1 w2 w3). Qed.
Example standard_llp244 (w0 w1 w2 : wff) : lprov (Wim (Wim w0 (Wn w1)) (Wim w1 (Wim w0 w2))).
Proof. exact (llp244 w0 w1 w2). Qed.
Example standard_llp253 (w0 w1 w2 : wff) : lprov (Wim (Wim w0 (Wim (Wn w1) w1)) (Wim w2 (Wim w0 w1))).
Proof. exact (llp253 w0 w1 w2). Qed.
Example standard_llp254 (w0 w1 w2 : wff) : lprov (Wim w0 (Wim w1 (Wim w2 w0))).
Proof. exact (llp254 w0 w1 w2). Qed.
Example standard_llp255 (w0 w1 w2 : wff) : lprov (Wim w0 (Wim w1 (Wim w2 w1))).
Proof. exact (llp255 w0 w1 w2). Qed.
Example standard_llp256 (w0 w1 : wff) : lprov (Wim w0 (Wim w1 w0)).
Proof. exact (llp256 w0 w1). Qed.
Example standard_llp261 (w0 w1 w2 : wff) : lprov (Wim (Wim (Wim w0 w1) w2) (Wim w1 w2)).
Proof. exact (llp261 w0 w1 w2). Qed.
Example standard_llp274 (w0 w1 w2 : wff) : lprov (Wim w0 (Wim (Wim (Wim w1 (Wn w2)) w2) w2)).
Proof. exact (llp274 w0 w1 w2). Qed.
Example standard_llp275 (w0 w1 : wff) : lprov (Wim (Wim (Wim w0 (Wn w1)) w1) w1).
Proof. exact (llp275 w0 w1). Qed.
Example standard_llp300 (w0 w1 w2 : wff) : lprov (Wim (Wim (Wim (Wn (Wim w0 (Wn w1))) w2) w1) w1).
Proof. exact (llp300 w0 w1 w2). Qed.
Example standard_llp329 (w0 w1 w2 : wff) : lprov (Wim w0 (Wim (Wim (Wim (Wim (Wn w1) w1) w1) w2) w2)).
Proof. exact (llp329 w0 w1 w2). Qed.
Example standard_llp330 (w0 w1 : wff) : lprov (Wim (Wim (Wim (Wim (Wn w0) w0) w0) w1) w1).
Proof. exact (llp330 w0 w1). Qed.
Example standard_llp331 (w0 w1 : wff) : lprov (Wim (Wim w0 (Wim (Wn w1) w1)) (Wim w0 w1)).
Proof. exact (llp331 w0 w1). Qed.
Example standard_llp334 (w0 w1 : wff) : lprov (Wim (Wim (Wn w0) w1) (Wim (Wim w1 w0) w0)).
Proof. exact (llp334 w0 w1). Qed.
Example standard_llp335 (w0 w1 : wff) : lprov (Wim w0 (Wim (Wim w0 w1) w1)).
Proof. exact (llp335 w0 w1). Qed.
Example standard_llp359 (w0 w1 w2 : wff) : lprov (Wim (Wim (Wim (Wim w0 w1) w1) w2) (Wim w0 w2)).
Proof. exact (llp359 w0 w1 w2). Qed.
Example standard_llp360 (w0 : wff) : lprov (Wim (Wn (Wn w0)) w0).
Proof. exact (llp360 w0). Qed.
Example standard_llp362 (w0 w1 : wff) : lprov (Wim (Wn w0) (Wim w0 w1)).
Proof. exact (llp362 w0 w1). Qed.
Example standard_llp364 (w0 w1 : wff) : lprov (Wim (Wn (Wim w0 (Wn w1))) w1).
Proof. exact (llp364 w0 w1). Qed.
Example standard_llp367 (w0 : wff) : lprov (Wim (Wim w0 (Wn w0)) (Wn w0)).
Proof. exact (llp367 w0). Qed.
Example standard_llp368 (w0 : wff) : lprov (Wim w0 (Wn (Wn w0))).
Proof. exact (llp368 w0). Qed.
Example standard_llp369 (w0 w1 : wff) : lprov (Wim (Wim (Wim w0 w1) w0) w0).
Proof. exact (llp369 w0 w1). Qed.
Example standard_llp430 (w0 w1 : wff) : lprov (Wim (Wim (Wim w0 (Wn (Wn w0))) w1) w1).
Proof. exact (llp430 w0 w1). Qed.
Example standard_llp437 (w0 w1 : wff) : lprov (Wim (Wim w0 (Wim w0 w1)) (Wim w0 w1)).
Proof. exact (llp437 w0 w1). Qed.
Example standard_llp475 (w0 w1 : wff) : lprov (Wim (Wim w0 w1) (Wim w0 (Wn (Wn w1)))).
Proof. exact (llp475 w0 w1). Qed.
Example standard_llp476 (w0 w1 : wff) : lprov (Wim (Wn w0) (Wn (Wn (Wim w0 w1)))).
Proof. exact (llp476 w0 w1). Qed.
Example standard_llp483 (w0 w1 w2 : wff) : lprov (Wim (Wn (Wim w0 w1)) (Wim (Wn w0) w2)).
Proof. exact (llp483 w0 w1 w2). Qed.
Example standard_llp484 (w0 w1 : wff) : lprov (Wim (Wn (Wim w0 w1)) w0).
Proof. exact (llp484 w0 w1). Qed.
Example standard_llp505 (w0 w1 w2 : wff) : lprov (Wim (Wim (Wim w0 w1) w2) (Wim (Wn w0) w2)).
Proof. exact (llp505 w0 w1 w2). Qed.
Example standard_llp716 (w0 w1 w2 : wff) : lprov (Wim (Wim w0 w1) (Wim (Wim w2 w0) (Wim w2 w1))).
Proof. exact (llp716 w0 w1 w2). Qed.
Example standard_llp719 (w0 w1 w2 : wff) : lprov (Wim (Wim w0 (Wim w1 w2)) (Wim w1 (Wim w0 w2))).
Proof. exact (llp719 w0 w1 w2). Qed.
Example standard_llp721 (w0 w1 : wff) : lprov (Wim (Wim w0 w1) (Wim (Wim (Wn w1) w0) w1)).
Proof. exact (llp721 w0 w1). Qed.
Example standard_llp722 (w0 w1 : wff) : lprov (Wim w0 (Wim (Wim (Wn w1) (Wn w0)) w1)).
Proof. exact (llp722 w0 w1). Qed.
Example standard_llp724 (w0 w1 : wff) : lprov (Wim (Wim (Wn w0) (Wn w1)) (Wim w1 w0)).
Proof. exact (llp724 w0 w1). Qed.
Example standard_llp1317 (w0 w1 : wff) : lprov (Wim (Wim w0 (Wim w1 (Wn w1))) (Wim w0 (Wn w1))).
Proof. exact (llp1317 w0 w1). Qed.
Example standard_llp1549 (w0 w1 : wff) : lprov (Wim (Wim w0 w1) (Wim (Wim w1 (Wn w0)) (Wn w0))).
Proof. exact (llp1549 w0 w1). Qed.
Example standard_llp1582 (w0 w1 : wff) : lprov (Wim (Wim w0 (Wn w1)) (Wim (Wim w1 w0) (Wn w1))).
Proof. exact (llp1582 w0 w1). Qed.
Example standard_llp1583 (w0 w1 : wff) : lprov (Wim w0 (Wim (Wim w1 (Wn w0)) (Wn w1))).
Proof. exact (llp1583 w0 w1). Qed.
Example standard_llp1584 (w0 w1 : wff) : lprov (Wim (Wn w0) (Wim (Wim w1 w0) (Wn w1))).
Proof. exact (llp1584 w0 w1). Qed.
Example standard_llp1585 (w0 w1 : wff) : lprov (Wim (Wim w0 (Wn w1)) (Wim w1 (Wn w0))).
Proof. exact (llp1585 w0 w1). Qed.
Example standard_llp1586 (w0 w1 : wff) : lprov (Wim (Wim w0 w1) (Wim (Wn w1) (Wn w0))).
Proof. exact (llp1586 w0 w1). Qed.
Example standard_llp1588 (w0 w1 : wff) : lprov (Wim w0 (Wim w1 (Wn (Wim w0 (Wn w1))))).
Proof. exact (llp1588 w0 w1). Qed.
Example standard_lpc_id (w0 : wff) : lprov (Wim w0 w0).
Proof. exact (lpc_id w0). Qed.
Example standard_lpc_K (w0 w1 : wff) : lprov (Wim w0 (Wim w1 w0)).
Proof. exact (lpc_K w0 w1). Qed.
Example standard_lpc_C (w0 w1 w2 : wff) : lprov (Wim (Wim w0 (Wim w1 w2)) (Wim w1 (Wim w0 w2))).
Proof. exact (lpc_C w0 w1 w2). Qed.
Example standard_lpc_B (w0 w1 w2 : wff) : lprov (Wim (Wim w1 w2) (Wim (Wim w0 w1) (Wim w0 w2))).
Proof. exact (lpc_B w0 w1 w2). Qed.
Example standard_lpc_W (w0 w1 : wff) : lprov (Wim (Wim w0 (Wim w0 w1)) (Wim w0 w1)).
Proof. exact (lpc_W w0 w1). Qed.
Example standard_lpc_contra (w0 w1 : wff) : lprov (Wim (Wim w0 w1) (Wim (Wn w1) (Wn w0))).
Proof. exact (lpc_contra w0 w1). Qed.
Example standard_lpc_contra2 (w0 w1 : wff) : lprov (Wim (Wim (Wn w0) (Wn w1)) (Wim w1 w0)).
Proof. exact (lpc_contra2 w0 w1). Qed.
Example standard_lpc_nn_elim (w0 : wff) : lprov (Wim (Wn (Wn w0)) w0).
Proof. exact (lpc_nn_elim w0). Qed.
Example standard_lpc_nn_intro (w0 : wff) : lprov (Wim w0 (Wn (Wn w0))).
Proof. exact (lpc_nn_intro w0). Qed.
Example standard_lpc_andl (w0 w1 : wff) : lprov (Wim (Wn (Wim w0 (Wn w1))) w0).
Proof. exact (lpc_andl w0 w1). Qed.
Example standard_lpc_andr (w0 w1 : wff) : lprov (Wim (Wn (Wim w0 (Wn w1))) w1).
Proof. exact (lpc_andr w0 w1). Qed.
Example standard_lpc_andi (w0 w1 : wff) : lprov (Wim w0 (Wim w1 (Wn (Wim w0 (Wn w1))))).
Proof. exact (lpc_andi w0 w1). Qed.
Example restricted_mllp5 (w0 w1 : wff) : lprov224 (Wim (Wim w0 w1) (Wim (Wim (Wn w0) w0) w1)).
Proof. exact (mllp5 w0 w1). Qed.
Example restricted_mllp7 (w0 w1 w2 : wff) : lprov224 (Wim (Wim (Wim (Wn w0) w1) w2) (Wim w0 w2)).
Proof. exact (mllp7 w0 w1 w2). Qed.
Example restricted_mllp8 (w0 : wff) : lprov224 (Wim w0 w0).
Proof. exact (mllp8 w0). Qed.
Example restricted_mllp9 (w0 w1 : wff) : lprov224 (Wim (Wn (Wim w0 w0)) w1).
Proof. exact (mllp9 w0 w1). Qed.
Example restricted_mllp12 (w0 w1 w2 : wff) : lprov224 (Wim w0 (Wim (Wim w1 w2) (Wim (Wn w0) w2))).
Proof. exact (mllp12 w0 w1 w2). Qed.
Example restricted_mllp14 (w0 w1 w2 : wff) : lprov224 (Wim (Wim w0 w1) (Wim (Wn (Wim w2 w2)) w1)).
Proof. exact (mllp14 w0 w1 w2). Qed.
Example restricted_mllp15 (w0 w1 w2 : wff) : lprov224 (Wim w0 (Wim (Wn (Wim w1 w1)) w2)).
Proof. exact (mllp15 w0 w1 w2). Qed.
Example restricted_mllp26 (w0 w1 w2 w3 : wff) : lprov224 (Wim (Wim (Wim (Wn (Wim w0 w0)) w1) w2) (Wim w3 w2)).
Proof. exact (mllp26 w0 w1 w2 w3). Qed.
Example restricted_mllp27 (w0 w1 : wff) : lprov224 (Wim w0 (Wim w1 w1)).
Proof. exact (mllp27 w0 w1). Qed.
Example restricted_mllp29 (w0 w1 w2 : wff) : lprov224 (Wim (Wim (Wim w0 w0) w1) (Wim w2 w1)).
Proof. exact (mllp29 w0 w1 w2). Qed.
Example restricted_mllp31 (w0 w1 : wff) : lprov224 (Wim w0 (Wim (Wim (Wn w1) w1) w1)).
Proof. exact (mllp31 w0 w1). Qed.
Example restricted_mllp44 (w0 w1 w2 : wff) : lprov224 (Wim (Wim (Wim (Wim (Wn w0) w0) w0) w1) (Wim w2 w1)).
Proof. exact (mllp44 w0 w1 w2). Qed.
Example restricted_mllp118 (w0 w1 w2 w3 : wff) : lprov224 (Wim (Wim (Wim w0 w1) w2) (Wim (Wim (Wim (Wn w0) w3) w1) w2)).
Proof. exact (mllp118 w0 w1 w2 w3). Qed.
Example restricted_mllp119 (w0 w1 : wff) : lprov224 (Wim (Wim (Wim (Wn (Wn w0)) w1) w0) w0).
Proof. exact (mllp119 w0 w1). Qed.
Example restricted_mllp135 (w0 w1 w2 w3 : wff) : lprov224 (Wim (Wim (Wim (Wim w0 w1) (Wim (Wn w2) w1)) w3) (Wim w2 w3)).
Proof. exact (mllp135 w0 w1 w2 w3). Qed.
Example restricted_mllp136 (w0 w1 w2 : wff) : lprov224 (Wim w0 (Wim w1 (Wim (Wn w0) w2))).
Proof. exact (mllp136 w0 w1 w2). Qed.
Example restricted_mllp143 (w0 w1 w2 w3 : wff) : lprov224 (Wim (Wim (Wim w0 (Wim (Wn w1) w2)) w3) (Wim w1 w3)).
Proof. exact (mllp143 w0 w1 w2 w3). Qed.
Example restricted_mllp241 (w0 w1 w2 w3 : wff) : lprov224 (Wim (Wim (Wim (Wim w0 w1) (Wim w2 w1)) w3) (Wim (Wim w2 w0) w3)).
Proof. exact (mllp241 w0 w1 w2 w3). Qed.
Example restricted_mllp244 (w0 w1 w2 : wff) : lprov224 (Wim (Wim w0 (Wn w1)) (Wim w1 (Wim w0 w2))).
Proof. exact (mllp244 w0 w1 w2). Qed.
Example restricted_mllp253 (w0 w1 w2 : wff) : lprov224 (Wim (Wim w0 (Wim (Wn w1) w1)) (Wim w2 (Wim w0 w1))).
Proof. exact (mllp253 w0 w1 w2). Qed.
Example restricted_mllp254 (w0 w1 w2 : wff) : lprov224 (Wim w0 (Wim w1 (Wim w2 w0))).
Proof. exact (mllp254 w0 w1 w2). Qed.
Example restricted_mllp255 (w0 w1 w2 : wff) : lprov224 (Wim w0 (Wim w1 (Wim w2 w1))).
Proof. exact (mllp255 w0 w1 w2). Qed.
Example restricted_mllp256 (w0 w1 : wff) : lprov224 (Wim w0 (Wim w1 w0)).
Proof. exact (mllp256 w0 w1). Qed.
Example restricted_mllp261 (w0 w1 w2 : wff) : lprov224 (Wim (Wim (Wim w0 w1) w2) (Wim w1 w2)).
Proof. exact (mllp261 w0 w1 w2). Qed.
Example restricted_mllp274 (w0 w1 w2 : wff) : lprov224 (Wim w0 (Wim (Wim (Wim w1 (Wn w2)) w2) w2)).
Proof. exact (mllp274 w0 w1 w2). Qed.
Example restricted_mllp275 (w0 w1 : wff) : lprov224 (Wim (Wim (Wim w0 (Wn w1)) w1) w1).
Proof. exact (mllp275 w0 w1). Qed.
Example restricted_mllp300 (w0 w1 w2 : wff) : lprov224 (Wim (Wim (Wim (Wn (Wim w0 (Wn w1))) w2) w1) w1).
Proof. exact (mllp300 w0 w1 w2). Qed.
Example restricted_mllp329 (w0 w1 w2 : wff) : lprov224 (Wim w0 (Wim (Wim (Wim (Wim (Wn w1) w1) w1) w2) w2)).
Proof. exact (mllp329 w0 w1 w2). Qed.
Example restricted_mllp330 (w0 w1 : wff) : lprov224 (Wim (Wim (Wim (Wim (Wn w0) w0) w0) w1) w1).
Proof. exact (mllp330 w0 w1). Qed.
Example restricted_mllp331 (w0 w1 : wff) : lprov224 (Wim (Wim w0 (Wim (Wn w1) w1)) (Wim w0 w1)).
Proof. exact (mllp331 w0 w1). Qed.
Example restricted_mllp334 (w0 w1 : wff) : lprov224 (Wim (Wim (Wn w0) w1) (Wim (Wim w1 w0) w0)).
Proof. exact (mllp334 w0 w1). Qed.
Example restricted_mllp335 (w0 w1 : wff) : lprov224 (Wim w0 (Wim (Wim w0 w1) w1)).
Proof. exact (mllp335 w0 w1). Qed.
Example restricted_mllp359 (w0 w1 w2 : wff) : lprov224 (Wim (Wim (Wim (Wim w0 w1) w1) w2) (Wim w0 w2)).
Proof. exact (mllp359 w0 w1 w2). Qed.
Example restricted_mllp360 (w0 : wff) : lprov224 (Wim (Wn (Wn w0)) w0).
Proof. exact (mllp360 w0). Qed.
Example restricted_mllp362 (w0 w1 : wff) : lprov224 (Wim (Wn w0) (Wim w0 w1)).
Proof. exact (mllp362 w0 w1). Qed.
Example restricted_mllp364 (w0 w1 : wff) : lprov224 (Wim (Wn (Wim w0 (Wn w1))) w1).
Proof. exact (mllp364 w0 w1). Qed.
Example restricted_mllp367 (w0 : wff) : lprov224 (Wim (Wim w0 (Wn w0)) (Wn w0)).
Proof. exact (mllp367 w0). Qed.
Example restricted_mllp368 (w0 : wff) : lprov224 (Wim w0 (Wn (Wn w0))).
Proof. exact (mllp368 w0). Qed.
Example restricted_mllp369 (w0 w1 : wff) : lprov224 (Wim (Wim (Wim w0 w1) w0) w0).
Proof. exact (mllp369 w0 w1). Qed.
Example restricted_mllp430 (w0 w1 : wff) : lprov224 (Wim (Wim (Wim w0 (Wn (Wn w0))) w1) w1).
Proof. exact (mllp430 w0 w1). Qed.
Example restricted_mllp437 (w0 w1 : wff) : lprov224 (Wim (Wim w0 (Wim w0 w1)) (Wim w0 w1)).
Proof. exact (mllp437 w0 w1). Qed.
Example restricted_mllp475 (w0 w1 : wff) : lprov224 (Wim (Wim w0 w1) (Wim w0 (Wn (Wn w1)))).
Proof. exact (mllp475 w0 w1). Qed.
Example restricted_mllp476 (w0 w1 : wff) : lprov224 (Wim (Wn w0) (Wn (Wn (Wim w0 w1)))).
Proof. exact (mllp476 w0 w1). Qed.
Example restricted_mllp483 (w0 w1 w2 : wff) : lprov224 (Wim (Wn (Wim w0 w1)) (Wim (Wn w0) w2)).
Proof. exact (mllp483 w0 w1 w2). Qed.
Example restricted_mllp484 (w0 w1 : wff) : lprov224 (Wim (Wn (Wim w0 w1)) w0).
Proof. exact (mllp484 w0 w1). Qed.
Example restricted_mllp505 (w0 w1 w2 : wff) : lprov224 (Wim (Wim (Wim w0 w1) w2) (Wim (Wn w0) w2)).
Proof. exact (mllp505 w0 w1 w2). Qed.
Example restricted_mllp716 (w0 w1 w2 : wff) : lprov224 (Wim (Wim w0 w1) (Wim (Wim w2 w0) (Wim w2 w1))).
Proof. exact (mllp716 w0 w1 w2). Qed.
Example restricted_mllp719 (w0 w1 w2 : wff) : lprov224 (Wim (Wim w0 (Wim w1 w2)) (Wim w1 (Wim w0 w2))).
Proof. exact (mllp719 w0 w1 w2). Qed.
Example restricted_mllp721 (w0 w1 : wff) : lprov224 (Wim (Wim w0 w1) (Wim (Wim (Wn w1) w0) w1)).
Proof. exact (mllp721 w0 w1). Qed.
Example restricted_mllp722 (w0 w1 : wff) : lprov224 (Wim w0 (Wim (Wim (Wn w1) (Wn w0)) w1)).
Proof. exact (mllp722 w0 w1). Qed.
Example restricted_mllp724 (w0 w1 : wff) : lprov224 (Wim (Wim (Wn w0) (Wn w1)) (Wim w1 w0)).
Proof. exact (mllp724 w0 w1). Qed.
Example restricted_mllp1317 (w0 w1 : wff) : lprov224 (Wim (Wim w0 (Wim w1 (Wn w1))) (Wim w0 (Wn w1))).
Proof. exact (mllp1317 w0 w1). Qed.
Example restricted_mllp1549 (w0 w1 : wff) : lprov224 (Wim (Wim w0 w1) (Wim (Wim w1 (Wn w0)) (Wn w0))).
Proof. exact (mllp1549 w0 w1). Qed.
Example restricted_mllp1582 (w0 w1 : wff) : lprov224 (Wim (Wim w0 (Wn w1)) (Wim (Wim w1 w0) (Wn w1))).
Proof. exact (mllp1582 w0 w1). Qed.
Example restricted_mllp1583 (w0 w1 : wff) : lprov224 (Wim w0 (Wim (Wim w1 (Wn w0)) (Wn w1))).
Proof. exact (mllp1583 w0 w1). Qed.
Example restricted_mllp1584 (w0 w1 : wff) : lprov224 (Wim (Wn w0) (Wim (Wim w1 w0) (Wn w1))).
Proof. exact (mllp1584 w0 w1). Qed.
Example restricted_mllp1585 (w0 w1 : wff) : lprov224 (Wim (Wim w0 (Wn w1)) (Wim w1 (Wn w0))).
Proof. exact (mllp1585 w0 w1). Qed.
Example restricted_mllp1586 (w0 w1 : wff) : lprov224 (Wim (Wim w0 w1) (Wim (Wn w1) (Wn w0))).
Proof. exact (mllp1586 w0 w1). Qed.
Example restricted_mllp1588 (w0 w1 : wff) : lprov224 (Wim w0 (Wim w1 (Wn (Wim w0 (Wn w1))))).
Proof. exact (mllp1588 w0 w1). Qed.
Example restricted_mlpc_id (w0 : wff) : lprov224 (Wim w0 w0).
Proof. exact (mlpc_id w0). Qed.
Example restricted_mlpc_K (w0 w1 : wff) : lprov224 (Wim w0 (Wim w1 w0)).
Proof. exact (mlpc_K w0 w1). Qed.
Example restricted_mlpc_C (w0 w1 w2 : wff) : lprov224 (Wim (Wim w0 (Wim w1 w2)) (Wim w1 (Wim w0 w2))).
Proof. exact (mlpc_C w0 w1 w2). Qed.
Example restricted_mlpc_B (w0 w1 w2 : wff) : lprov224 (Wim (Wim w1 w2) (Wim (Wim w0 w1) (Wim w0 w2))).
Proof. exact (mlpc_B w0 w1 w2). Qed.
Example restricted_mlpc_W (w0 w1 : wff) : lprov224 (Wim (Wim w0 (Wim w0 w1)) (Wim w0 w1)).
Proof. exact (mlpc_W w0 w1). Qed.
Example restricted_mlpc_contra (w0 w1 : wff) : lprov224 (Wim (Wim w0 w1) (Wim (Wn w1) (Wn w0))).
Proof. exact (mlpc_contra w0 w1). Qed.
Example restricted_mlpc_contra2 (w0 w1 : wff) : lprov224 (Wim (Wim (Wn w0) (Wn w1)) (Wim w1 w0)).
Proof. exact (mlpc_contra2 w0 w1). Qed.
Example restricted_mlpc_nn_elim (w0 : wff) : lprov224 (Wim (Wn (Wn w0)) w0).
Proof. exact (mlpc_nn_elim w0). Qed.
Example restricted_mlpc_nn_intro (w0 : wff) : lprov224 (Wim w0 (Wn (Wn w0))).
Proof. exact (mlpc_nn_intro w0). Qed.
Example restricted_mlpc_andl (w0 w1 : wff) : lprov224 (Wim (Wn (Wim w0 (Wn w1))) w0).
Proof. exact (mlpc_andl w0 w1). Qed.
Example restricted_mlpc_andr (w0 w1 : wff) : lprov224 (Wim (Wn (Wim w0 (Wn w1))) w1).
Proof. exact (mlpc_andr w0 w1). Qed.
Example restricted_mlpc_andi (w0 w1 : wff) : lprov224 (Wim w0 (Wim w1 (Wn (Wim w0 (Wn w1))))).
Proof. exact (mlpc_andi w0 w1). Qed.
Print Assumptions standard_lpc_id.
Print Assumptions restricted_mlpc_id.
Print Assumptions standard_lpc_K.
Print Assumptions restricted_mlpc_K.
Print Assumptions standard_lpc_C.
Print Assumptions restricted_mlpc_C.
Print Assumptions standard_lpc_B.
Print Assumptions restricted_mlpc_B.
Print Assumptions standard_lpc_W.
Print Assumptions restricted_mlpc_W.
Print Assumptions standard_lpc_contra.
Print Assumptions restricted_mlpc_contra.
Print Assumptions standard_lpc_contra2.
Print Assumptions restricted_mlpc_contra2.
Print Assumptions standard_lpc_nn_elim.
Print Assumptions restricted_mlpc_nn_elim.
Print Assumptions standard_lpc_nn_intro.
Print Assumptions restricted_mlpc_nn_intro.
Print Assumptions standard_lpc_andl.
Print Assumptions restricted_mlpc_andl.
Print Assumptions standard_lpc_andr.
Print Assumptions restricted_mlpc_andr.
Print Assumptions standard_lpc_andi.
Print Assumptions restricted_mlpc_andi.
Print Assumptions L1_LMeta.ae_sound.
Print Assumptions L224Meta.malpha.
