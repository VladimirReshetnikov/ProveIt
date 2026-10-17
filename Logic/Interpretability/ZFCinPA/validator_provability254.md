# Internal C254 theorem predicate and classical interface

`ValidatorProvability254.lean` defines the fixed Sigma1 predicate

```
CProv(n) := exists code, ArithmeticHistory254.value(code)=n+1.
```

Its arithmetic formula is selected before the ambient IΣ1 model. Every
closure theorem permits arbitrary internal numbers, including nonstandard
formula parameters and proof witnesses. This is an existence interface;
no canonical proof-code selector is assumed or constructed.

The twelve original rules are reused from the already checked numeric
Constructors equations: truth 0, MP, whole-tail GEN, all eight logical rows,
and the bundle with both `c≠a` and `c≠b`. MP's public interface takes the
major premise first, while its actual node payload remains conclusion,
minor proof code, major proof code. No rule or gate is removed.

The existing finite Lukasiewicz certificates are polymorphic in the carrier,
implication operation and theorem predicate. Instantiating them at internal
V, numeric `wim` and CProv gives K, S, Peirce and composition without an
implication-injectivity or standard-code assumption. A fixed propositional
argument using original rho6 supplies ex falso at literal false 1. The result
is the actual `Kalmar.Classical wim 1 CProv` interface, even with the numeric
zero alias `wim(0,0)=0`. The separate Nat adapter identifies CProv with the
original external `Code254.C254` only on standard inputs.

The final bounded check passed 22 ordered axiom probes and 16 callers, using
only `propext`, `Classical.choice`, and `Quot.sound`, with zero warnings.
Source/audit command times were 2.782070s/2.263899s. The exact 19-project
prerequisite closure includes the checked Constructors object. Four cached
external boundaries are retained: three direct DFS imports and the parent's
explicit Seq iteration anchor. The actual Omega provider, compiler,
dependency pins/clean state, manifest, base providers, all 57 immutable inputs,
and selected first providers were checked before and after the run. This is
boundary source/object provenance, not a fresh check of the complete
transitive Foundation/Mathlib caches. No dependency build or download occurred.

Two preceding overall FAIL records are retained distinctly. Run 1 failed on
an unused unavailable Bootstrapping namespace open, removed by a one-line
source edit. Run 2 reached object writing without source diagnostics but
failed because the guard had not created the new ZFCinPA output directory;
the repair creates that directory. Neither failure ran the audit or is
reported as a whole PASS. The historical original/next preparations and all
executed source/audit/guard snapshots are embedded in the history record.

The maintained guard retains the frozen source/audit pins, uses portable
repo/dependency and maintained source/audit defaults, and additionally checks
the implicit Init provider alongside Omega against the actual toolchain.
This supplemental provider check strengthens preflight validation; the
original successful proof guard/evidence are unchanged and did not record
that dedicated Init comparison. Prepare-only checks do not compile a source
or audit, though compiler identity includes a `lean --version` query.

Reproduce using the existing pinned dependency checkout and recorded cached
objects (or supply `--project-cache` for byte-identical relocated project
objects):

```sh
python Logic/Interpretability/ZFCinPA/check_validator_provability254.py \
  --repo /absolute/path/to/Proofs \
  --dependency-root /absolute/path/to/existing/dependency/Proofs \
  --output /outside/checkout/fresh-cprov-check
```

Add `--prepare-only` for provider/hash validation without a proof build.
The output must be fresh and outside both checkouts. Assertions must remain
enabled. Explicit source/audit/evidence/compiler/library overrides remain
available and must satisfy the same frozen identities.

This checkpoint supplies neither an internal Foundation-formula encoder nor
an internal sequent compiler, actual ZF axiom clients in CProv, reverse
consistency, or the binary arithmetic endpoint. Those obligations remain
separate. In particular a bundle's c simultaneously denotes a formula code
and a variable label, so blanket CProv renaming closure cannot be inferred
by renaming the literal rule parameters. The separately drafted encoder and
opening-transport notes are not part of this checked publication packet.
