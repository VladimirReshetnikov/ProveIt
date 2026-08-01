(** * Assumption-based routes: [Admitted], [Axiom], [Program] obligations

    The three ways to obtain [False] by *assuming* it, and what each one leaves
    in [Print Assumptions].  None of these is a defect: all are documented, all
    are tracked.  They are recorded here because a catalog of ways to prove
    [False] that omits the easy ones is not a catalog.

    Category (see ../../README.md): ESCAPE HATCH -- sanctioned, and visible in
    the audit.

    Toolchain: The Rocq Prover 9.2.  Verified by ../verify.ps1. *)

(** ** 1. [Admitted] turns the goal into a global axiom under the lemma's name *)

Lemma admitted_false : False.
Admitted.

Definition uses_admitted : False := admitted_false.

(** [admitted_false : False] *)
Print Assumptions uses_admitted.

(** [Abort] is the only safe way out of a proof: it declares nothing. *)

Lemma aborted : False.
Proof.
Abort.

Fail Check aborted.

(** ** 2. [Axiom], [Parameter], [Hypothesis], [Conjecture] are the same command

    The manual states the distinction is purely stylistic.  The blunt form is
    obvious; the subtle form below is exactly as lethal and reads as harmless. *)

Axiom blunt : False.

Axiom everything_inhabited : forall A : Type, A.
Definition subtle : False := everything_inhabited False.

(** [everything_inhabited : forall A : Type, A] *)
Print Assumptions subtle.

(** *** The section trap

    [Variable] and [Hypothesis] are discharged at [End]; an [Axiom] declared
    inside a section is *not*.  Rocq 9.2 refuses [Variable] outside a section,
    which is the guard rail; inside one, the two commands look interchangeable
    and are not. *)

Fail Variable loose : False.

(** ** 3. [Program] obligations become ordinary axioms

    [Admit Obligations] is the hazard: a project-wide [Obligation Tactic] can
    silently admit obligations across an entire development, and each one is a
    fresh axiom named after its parent. *)

#[program] Definition strictly_bigger (n : nat) : { m : nat | m > n } := n.
Admit Obligations.

(** [strictly_bigger_obligation_1 : forall n : nat, (fun m : nat => m > n) n] *)
Print Assumptions strictly_bigger.

Lemma from_obligation : False.
Proof.
  pose proof (proj2_sig (strictly_bigger 0)) as h; simpl in h; inversion h.
Qed.

Print Assumptions from_obligation.

(** ** What this file shows

    Every route here is reported by [Print Assumptions], by name, at the use
    site.  That is the whole point of the mechanism, and it is the sharp
    contrast with ../../KernelDefects/, where a proof of [False] reports
    "Closed under the global context".

    The Lean counterparts are ../Lean/Sorry.lean and ../Lean/Axioms.lean. *)
