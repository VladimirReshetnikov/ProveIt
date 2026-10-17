# Internal relative falsity and numerical rho6

`ModelCodedDecoderRho6_254` proves the actual numerical row

```text
Provable ZF  (decode (ArithmeticTemplates254.rho6 a b))
Provable ZFC (decode (ArithmeticTemplates254.rho6 a b))
```

for every model of IΣ1 and every internal label `a` and matrix code `b`.
Selected label zero and matrix zero are included. These are internal
proof-existence statements about the actual theories and literal decoder,
not a quotation theorem restricted to standard formula codes.

The source rho6 is `(∃a ∀a b) → b`. Its existential and negation are expressed
using implication to numerical falsity1. The decoder sends1 to membership(0,0),
so the apparent falsity can be captured when a named universal binds label0.
The proof keeps this syntax exact. It does not replace decoded1 by primitive
Bottom under a binder or assume that the matrix has no free label0.

The proof uses three already checked resources. First, repeated-binding
absorption says that binding the same label again leaves the first bound body
unchanged, at arbitrary internal depth. Consequently the negation of a named
universal is invariant under binding that same label. Opening this body is
exactly the shifted negation formula, which supplies the premise of a finite
logical generalization proof. Contraposition and ordinary named-universal
elimination then prove

```text
(¬AllNamed(a, ¬AllNamed(a,p))) → p
```

for arbitrary internal typed matrices in any internal theory.

Second, a fixed ordinary ZF irreflexivity theorem is weakened to the target
ordinary theory before D1/internalization and specialization. Its result is an
internal proof of `¬decoded1`. No arbitrary internal matrix is quoted. This
identifies implication to decoded1 with ordinary logical negation at the proof
level.

Third, the already checked actual named-GEN rule lifts the implication-to-falsity
versus negation equivalence through the named universal. This step resolves the
capture at selected label0. Literal numerical constructor equations and decoded
implication equivalence identify the resulting finite logical theorem with the
actual arithmetic rho6 code. The generic helpers expose exactly `hFalse` and
`hGen`; the ZF and ZFC endpoints discharge both resources.

The final138-line source and focused audit have one actual Lean4.32.0 PASS:
12 ordered axiom reports and16 callers, source2.511120s and audit2.433374s.
The source has one unnecessary-`simpa` suggestion; the audit has no warnings.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. No dependency build,
download, or proof replay was used in packaging.

Two unsuccessful attempts remain recorded. The first required a classical
formula-equality instance and hit two deterministic elaboration heartbeat
limits while trying to unfold numerical implication through the decoder.
Explicit unfolding of `wim`, `tagged`, and `add_zero` resolved this without
raising the compiler limits. The second source passed, but its audit lacked
the namespace containing `decoded`; the final audit adds that namespace.
Exact failed source/audit/guard snapshots and logs remain in the history record;
old changed-path hashes are not asserted to match the current files.

The portable maintained replay is

```bash
python Logic/Interpretability/ZFCinPA/check_model_coded_decoder_rho6_254.py --output /tmp/decoded-rho6-replay
```

The guard accepts explicit repository, dependency-root, compiler, library,
source/audit and parent evidence/source/audit paths. `--project-cache` relocates
the38 selected project predecessor objects, while `--namespace-cache` supplies
the complete existing Foundation namespace. The separately recorded unused
Cantor artifact remains an explicit historical input; a relocated parent record
can provide its new path with the same identity. This is an exact previously
accepted same-source Cantor pair, not a general allowance for object variance.

The guard merges the actual Absorption7/9, rho2 8/8, and Falsity8/12 PASS records,
checks all shared source/object/provider identities, imports all three fresh
parent objects, and enforces the exact38-project/six-boundary closure. Its104
input paths include actual first external/toolchain providers and Omega,
compiler/pins/manifest, source/audit snapshots, and the historical unused object;
all are rechecked after the proof and audit. Packaging adds two explicitly
unbuilt override/relocated preflights and three rejection controls. Preflights
query the compiler version and execute zero Lean proof builds.

This checkpoint does not supply the remaining C254 axiom families, arbitrary
accepted-proof translation, or a PA consistency equivalence with ZFC or the
binary machine. In particular, rho1 is the actual `ArithmeticCode254.rho1`
(`wex a (weq a b)`), and its internal decoded proof is a separate remaining
obligation; this is not a claim that all eight logical rows are complete.
