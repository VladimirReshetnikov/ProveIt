# Shared Euclidean division certificate

Source baseline: ProveIt `6175dff9a15491497c7a3c1bda4f6a62a6349c74`.

`RegisterDivMod.certificate_iff` and `QuadraticDivMod.certificate_iff` are
literally the same 17-line declaration, apart from their enclosing namespace.
Their shared statement is

```
(exists s, n = q*b+r and b = r+s+1)
  iff (0 < b and q = n/b and r = n%b).
```

The patch moves the numerical theorem to the low-dependency
`ArithmeticCertificates` module and leaves both existing names and types as
transparent theorem wrappers. The common proof uses the core theorem
`Nat.div_mod_unique`, with the correct multiplication/addition orientation,
instead of separately calculating a quotient and a remainder. The helper uses
only `Std.Tactic`, so it introduces no dependency between the two representation
backends.

The graph programs, row data, witness counts, expression syntax, definition
bodies and all callers are unchanged. A static check confirms byte equality of
each whole source file after removing only the replaced theorem declaration and
the added import. The public theorem statements have identical SHA-256 hashes.

## Novelty relative to previous incoming packets

The older proposals normalize digit/carry decompositions. They do not identify
this duplicated existential certificate or factor its two backend consumers.
The essential new interface is the same *guarded, existential certificate*
shared by two different syntactic realizations. This is a proof-engineering
improvement, not new number theory.

## Exact source accounting

| Production source | Before | After |
|---|---:|---:|
| RegisterDivMod.lean | 87 | 75 |
| QuadraticDivMod.lean | 72 | 60 |
| New ArithmeticCertificates.lean | 0 | 20 |
| Total physical lines | 159 | 155 |

The net saving is **4 physical lines**, including the whole new helper file and
both new imports. Each old 17-line theorem becomes four lines. The main gain is
one numerical proof and one dependency boundary, not a large source-size win.
Optional validation/extension theorems are not part of that production delta.

## Verified extension

`ArithmeticCertificatesChecks.certificate_unique` proves that two certificates
for the same numerator and denominator determine the same quotient, remainder
and slack. The proof obtains quotient/remainder uniqueness from the shared iff
and slack uniqueness by linear arithmetic. No positivity hypothesis is added:
the certificate itself forces a positive denominator. The check module also
proves explicitly that denominator zero admits no certificate and that every
positive denominator admits one.

This is an optional reusable theorem. It is included as a checked extension,
not automatically added to production code. The host-natural-number theorem
should not replace `ObjectDivision` statements about arbitrary model naturals;
that requires a separate internal semantic theorem.

## Validation and replay

Lean 4.32.0 compiled the standalone helper and the check module successfully.
All five axiom probes report exactly `propext` and `Quot.sound`. The patch passes
`git apply --check` against the source baseline. These checks do **not** constitute
a rebuild of the complete production backend modules or their downstream
clients. Logs and the machine-readable scope are under `evidence/`.

```
python3 replay.py --lean /absolute/path/to/lean --repo /absolute/path/to/ProveIt
python3 make_patch.py --repo /absolute/path/to/ProveIt
```

`replay.py` needs only the pinned Lean toolchain, not Mathlib, for the proof
checks. It writes fresh logs into `replay-results/` unless `--output` is supplied.
The optional repository argument checks the exact commit and patch applicability;
it never applies the patch. `make_patch.py` regenerates the candidate full files,
reviewable patch and source metrics from the baseline, without modifying it.

The proposed production file is under `lean/DiophantineConsistency/`; the
check module is `lean/ArithmeticCertificatesChecks.lean`; the two complete
modified candidate modules are under `patched-modules/`.
