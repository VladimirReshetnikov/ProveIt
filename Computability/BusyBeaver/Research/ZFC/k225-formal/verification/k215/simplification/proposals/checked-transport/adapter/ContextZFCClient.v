(** Integration client against the maintained complete K215 endpoint.
    This file needs the repository's full audited dependency closure.
    Do not describe it as freshly compiled unless that closure is available
    and this client has actually been compiled. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From K230S Require Import KQuotZFC.
From K215F Require Import Correct215.
Require Import NativeContext LiteralBindings ContextLiteralSparse.

Theorem context_halts_iff_ZFC_inconsistent :
  NativeContext.halts LiteralBindings.literal_new NativeContext.blank <->
  StandardZFC ⊢TC ⊥.
Proof.
  rewrite ContextLiteralSparse.context_literal_blank_halts_iff_sparse.
  exact K215F.Correct215.tm215_sparse_halts_iff_ZFC_inconsistent.
Qed.

Corollary context_nonhalting_iff_ZFC_consistent :
  (~ NativeContext.halts LiteralBindings.literal_new NativeContext.blank) <->
  ~(StandardZFC ⊢TC ⊥).
Proof. rewrite context_halts_iff_ZFC_inconsistent. reflexivity. Qed.
Print Assumptions context_halts_iff_ZFC_inconsistent.
Print Assumptions context_nonhalting_iff_ZFC_consistent.
