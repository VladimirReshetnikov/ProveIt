# Checked identity substitution at a larger ambient arity

The unchanged [SubstIdentity source](Lean/ZFCinPA/SubstIdentity.lean) passes
a fresh Lean check and **nine axiom probes with twelve typed clients**,
with no warnings. The [actual record](results/subst-identity-verification.json)
checks that substitution by the identity bound-variable vector preserves
an arbitrary internally coded formula in an IΣ₁ model.

The raw theorem permits an internal arity. The typed versions use external
natural arities and express equality through the explicit, code-preserving
weakening `castLE`. The compiler corollary applies to placeholder atoms whose
arguments are the identity vector, at an ambient arity large enough for the
leaf. It reconciles the compiler's substituted leaf with the raw leaf used
by later certificate formulas; it does not construct those certificates.

Source and audit took 2.766 and 2.205 seconds with default proof limits,
one thread, 4,096 MiB and a shared 120-second deadline. All 78 recorded inputs
and the fresh first-provider object remained unchanged after the audit.
Every probe uses only standard Lean axioms.

Nine selected project providers, five opaque boundaries and Init are explicit.
The accepted open-set compiler replay supplies the exact predicate compiler
and SetPlaceholders objects; Foundation Z supplies Basic.Axioms and Basic.Misc.
The older open-set replay's two source warnings and absent modern pre-audit
captures remain historical limitations. The new check does not rebuild those
dependencies or attest the whole cache.

The [publication](results/subst-identity-publication.json) and
[history](subst-identity/history.json.gz) retain the source/API review,
audit, guard and actual logs, including an unexecuted metadata draft corrected
before the run. The source overview's stale theorem name is retained verbatim;
the audit calls the actual `subst_bvarVec_eq_castLE` declaration.
This closes one original validator inventory entry; the final PA composition
remains pending.
