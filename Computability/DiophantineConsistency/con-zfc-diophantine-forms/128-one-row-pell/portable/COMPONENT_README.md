# One congruence and one bound in one Pell row

This portable component supplies the complete 378-variable integer quartic
and a 242-variable natural quartic. The manuscript explains their unbounded
meaning. Every final residual and every collected coefficient is literal JSON.

## Principal artifacts

- `integer378/equation.json`: the 230 quadratic residuals and all 378 integer coordinates.
- `integer378/expanded_polynomial.json`: all 9,421 monomials of their sum of squares.
- `integer378/residuals.txt`, `variables.tsv`: full human-readable data.
- `natural242/natural/`: the complete natural-domain companion, with 190 residuals and 9,308 quartic monomials.
- `SIGNED_CONSTRUCTION_PROOF.md`: the complete sign-recovery and quotient proof schedule.
- `GUARD_TABLE.tsv`: all 36 scalar guards and twelve separate product guards.
- `SOURCE_LEDGER.json`: pinned input archives and exact retained source hashes.
- `CLAIMS.json`: exact final domains, counts, paths and polynomial hashes.
- `audits/`: separately implemented raw-source interface and mathematical review.

## Offline verification

Python 3.10 or later, standard library only:

```
python3 -B verify_release.py --rebuild
python3 -B -O verify_release.py --rebuild
python3 -B audits/audit_interfaces.py natural242
python3 -B audits/audit_signed.py
```

The first two commands authenticate inherited source files, replay all 117
natural and 125 integer polynomial inverses, expand every final coefficient,
check all 250 sign identities and the exact guard graphs, and rebuild all 27
normative JSON outputs in temporary directories. The three corruption controls
modify a signed inverse, a sign identity and a pair interface. The source
interface audits additionally bind the frame, the full cap, each exact-power
and modular-digit port, and the noncircular prefix.

`-O` disables Python assertions. The independent checkers use exceptions,
and the rebuild driver propagates `-O` to all three construction subprocesses.
The retained finite checks are not a proof of unsolvability or of Con(ZFC).
The ordinary cap, arithmetic and calculus proofs establish the interpretation.

## Rebuilding selected equations

```
python3 -B build_capped_modular.py --out rebuilt/natural242 --syntax xx0 --cap 16 --merged
python3 -B build_capped_modular.py --out rebuilt/fullroot --syntax xx0 --cap 16 --merged --recover-x
python3 -B build_signed_merged.py --source rebuilt/fullroot/raw/equation.json --out rebuilt/integer378 --defer-quotients --pair-guards
```

The signed constructor requires the exact reviewed full-root input hash.
The natural companion without the abscissa-error terms cannot be passed to
it. A new architecture requires its own mathematical source binding.

## Scope and provenance

The public repository snapshot is ProveIt commit
`f4d8db99e060339f3306a04d507c35bc1d0d68c5`. The three incoming archive
hashes are in `SOURCE_LEDGER.json`. The construction uses the direct numerical
C222 calculus, not a K215 execution or Jones universal equation. Its ordinary
calibration to ZFC refutations is inherited and is retained with source proofs
and endpoint files. No new end-to-end Lean/Rocq proof is asserted.

The 378-integer equation has fewer variables and residuals than the inspected
442-integer input, with increased coefficient height and monomial count.
The 242-natural equation improves all four displayed variable/row/support/
height metrics against the inspected 261-natural input. These compare
specific direct quartic families; no global simplicity minimum is claimed.

Original licenses and notices are retained beside the copied source modules.
