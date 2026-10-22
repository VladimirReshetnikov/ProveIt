From Coq Require Import Arith List.
From K215F Require Import EnumPerm Thm222 L1_CompPerm SeedPerm.

Definition old_drain : forall k s, pl s <= k ->
  halts_from s \/ exists n s', run n s = Some s' /\ pl s' = 0 /\ np s' = np s := drain.
Definition old_reach : forall m, enum_halts \/
  exists n s, run n s0 = Some s /\ pl s = 0 /\ np s = m := reach.
Definition old_prefix : forall n s, run n s0 = Some s ->
  halts_from s -> enum_halts := halts_from_reach.
Definition old_seed_reach : forall seed k, pl seed = 0 ->
  halts_from seed \/ exists n s, run n seed = Some s /\ pl s = 0 /\ np s = np seed + k := SeedPerm.reach_from.
Definition old_seed_prefix : forall seed n s, run n seed = Some s ->
  halts_from s -> halts_from seed := SeedPerm.halts_from_reached.
Definition old_complete : thm222 1 -> enum_halts := enum_complete.
Definition old_seed_complete : thm222 1 -> halts_from seedPerm := seedPerm_complete.
Definition old_seed_sound : halts_from seedPerm -> thm222 1 := seedPerm_sound.
Definition old_seed_iff : halts_from seedPerm <-> thm222 1 := seedPerm_iff_thm.

Print Assumptions old_drain.
Print Assumptions old_reach.
Print Assumptions old_prefix.
Print Assumptions old_seed_reach.
Print Assumptions old_seed_prefix.
Print Assumptions old_complete.
Print Assumptions old_seed_complete.
Print Assumptions old_seed_sound.
Print Assumptions old_seed_iff.

Definition new_boundary_complete : forall seed, pl seed = 0 ->
  thm222 1 -> halts_from seed := enum_complete_from_boundary.
Print Assumptions new_boundary_complete.
Print Assumptions reach_from_boundary.
Print Assumptions halts_from_run.
