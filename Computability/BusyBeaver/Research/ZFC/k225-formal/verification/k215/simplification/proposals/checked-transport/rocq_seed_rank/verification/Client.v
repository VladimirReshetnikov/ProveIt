From K215F Require Import EnumPerm Thm222 L1_CompPerm L1_SoundPerm SeedPerm.
Check (enum_complete : thm222 1 -> enum_halts).
Check (seedPerm_complete : thm222 1 -> halts_from seedPerm).
Check (seedPerm_sound : halts_from seedPerm -> thm222 1).
Check (seedPerm_iff_thm : halts_from seedPerm <-> thm222 1).
Print Assumptions enum_complete.
Print Assumptions seedPerm_iff_thm.
Check (enum_complete_from : forall s : state, thm222 1 -> halts_from s).
Check (enum_from_iff : forall s : state, Inv s -> (halts_from s <-> thm222 1)).
Print Assumptions candidate_rank_step.
Print Assumptions find_candidate_bounded.
Print Assumptions enum_complete_from.
Print Assumptions enum_from_iff.
