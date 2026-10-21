(** Copy of rocq224/src/L1_222.v (SHA256 ee824354918dc216608ab66e3146d2e3d254221e42128995245f9d9a127e802f) under namespace K218F. *)
(** Forked by gen_logic222.py from Elliot Glazer's k230-rocq (3142e4d) logic/L1_230.v for the seed-K
    222 calculus [thm222]: rho7 is replaced by the merged equality row [growG] and the
    bundle by the helper-free seed bundle [bundle222]. *)
(** Adapted from the pinned m254/L1_254.v; same command calculus with K230 bundle. *)
(** * L1_222: the abstract enumerator of the zfc_230 source halts iff the code-level calculus
    derives the code 1 (= F = Rel(0,0) = v0 e. v0). *)
From K218F Require Import Enum222 Thm222 L1_Sound222 L1_Comp222.

Theorem L1_222 : enum222_halts <-> thm222 1.
Proof. split; [exact enum_sound | exact enum_complete]. Qed.

Print Assumptions L1_222.
