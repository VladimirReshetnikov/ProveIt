(** * Rewrite rules: unchecked definitional equalities in the kernel

    Requires [-allow-rewrite-rules].  This is the newest sanctioned unsoundness
    switch in Rocq (9.x), and the sharpest: [Symbol] declares an axiom, and
    [Rewrite Rule] injects user-supplied equations *directly into kernel
    conversion*.  The manual's own warning: "ill-typed rewrite rules will lead
    to mistyped expressions, and manipulating these will most often result in
    inconsistencies and anomalies."  Type preservation gets an incomplete check
    that only warns on failure; confluence and termination are not checked at
    all, and subject reduction is intentionally broken.

    Category (see ../../README.md): ESCAPE HATCH -- experimental, documented,
    unsound by construction, and tracked.

    Lean has no counterpart: there is no way to add a definitional equation to
    the Lean kernel from source.  The nearest analogue is a *defect* rather than
    a feature -- the kernel's name-keyed normalizer extensions, which a
    [prelude] module can redirect (../../KernelDefects/Lean/Accelerators/).

    Toolchain: The Rocq Prover 9.2, compiled with [-allow-rewrite-rules].
    Verified by ../verify.ps1. *)

(** ** 1. [Symbol] alone is just an axiom with a different spelling *)

Symbol raise : forall (A : Type), A.

Definition symbol_false : False := raise False.

(** [raise : forall A : Type, A] and
    [Theory: Rewrite rules are allowed (subject reduction might be broken)] *)
Print Assumptions symbol_false.

(** ** 2. [Rewrite Rule] adds equations the kernel will use for conversion

    These are not lemmas.  [reflexivity] below is discharged by *kernel
    conversion*, not by any proof term, because the rule became part of the
    reduction relation. *)

Symbol pplus : nat -> nat -> nat.

Rewrite Rule pplus_rew :=
| pplus ?n 0 => ?n
| pplus 0 ?n => ?n.

Lemma by_kernel_conversion : pplus 3 0 = 3.
Proof. reflexivity. Qed.

Print Assumptions by_kernel_conversion.

(** ** 3. What is and is not checked

    A [Rewrite Rule] declaration passes only an *incomplete* type-preservation
    check, which the manual says "only emits a warning if failed".  Confluence
    and termination are not checked at all, and subject reduction is
    intentionally not preserved -- the manual's own words.  So a rule set can
    make the kernel's conversion relation non-confluent, or non-terminating, and
    nothing in the declaration will say so.

    That is qualitatively different from every other item in this directory: the
    other escape hatches let you *assume* something false, whereas this one lets
    you change what the kernel *computes*.  It is the only user-facing way to do
    that in either system. *)

(** ** What this file shows

    Every declaration above is reported by [Print Assumptions] -- the [Symbol]s
    by name, and the whole file by the [Theory:] banner.  The banner is the
    important one: it says the *theory has changed*, not merely that an
    assumption was used.  That is the distinction this directory is organised
    around, and it is why rewrite rules sit here rather than in
    ../../KernelDefects/. *)
