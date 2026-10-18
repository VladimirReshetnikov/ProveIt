(** * L1_254: the abstract enumerator of the zfc_254 source halts iff the code-level calculus
    derives the code 1 (= F = Rel(0,0) = v0 e. v0). *)
From M254L Require Import Enum254 Thm254 L1_Sound254 L1_Comp254.

Theorem L1_254 : enum254_halts <-> thm254 1.
Proof. split; [exact enum_sound | exact enum_complete]. Qed.

Print Assumptions L1_254.
