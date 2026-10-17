(** * Bridge254: the code-level calculus vs. the set theory SIR (m254/settheory/S_def.v).
      thm254 1 <-> SIR ⊢TC ⊥,  hence  enum254_halts <-> SIR ⊢TC ⊥. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From M254S Require Import S_def.
From M254L Require Import Enum254 Thm254 L1_254 Sound254 Comp_Bundle254.

Theorem bridge254 : thm254 1 <-> @tprv _ _ falsity_on class SIR falsity.
Proof. split; [exact thm_to_SIR | exact SIR_to_thm]. Qed.

Theorem enum254_SIR : enum254_halts <-> @tprv _ _ falsity_on class SIR falsity.
Proof. rewrite L1_254. exact bridge254. Qed.

Print Assumptions enum254_SIR.
