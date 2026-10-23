# Free-coordinate split116 composition

This separate adjunct combines the supplied FreeCoordinate carrier/quotient-shift idea and leading-block deletion with the degree-separated source and positivity-first norm of the frozen `nine/` family. It does not modify that family.

## Result

| Domain | Unknowns | Exact total degree | Live binary operations |
|---|---:|---:|---:|
| Strictly positive integers | 9 | 1,910,404 | 473 |
| Nonnegative integers | 9 | 1,910,404 | 480 |

The positive equation uses coordinates `b,g,h,s,w,C,i,j,n`. All powers have fixed exponents. Registers are abbreviations, not additional unknowns. Its operation ledger is 162 additions, 22 subtractions, and 289 multiplications. The natural version is the bijective all-inputs-plus-one translation; its internal CRT coordinate is the unshifted natural `j`.

ZFC proves that existence of a zero is equivalent to existence of a finite syntactic ZFC refutation, using the explicitly identified original31 compiler and Jones numerical ratio theorems. Thus absence of zeros is equivalent in ZFC to Con(ZFC). This is not a consistency proof, a global minimality claim, an unrestricted-integer nine-variable claim, or a new end-to-end proof-assistant formalization.

## Canonical artifacts

- `PROOF.md`: complete composition proof, including unconditional source bounds, the exact four-word soundness range, binary calibration, free-carrier sign recovery, exact CRT transport, positive final witness, and degree.
- `section.tex`: report-ready mathematical section, intended for the parent report after its split-source section.
- `generated/split_116_positive.json`: canonical literal division-free polynomial DAG.
- `generated/split_116_natural.json`: canonical nonnegative-domain translation.
- `generated/*_certificate.json` and `generated/*_certificate_degree.json`: equal-polynomial cancellation-resolving circuits and exact-degree certificates.
- `build_nine.py`, `circuit.py`, `verify_nine.py`: locally authored standard-library builder and finite checker.
- `independent_review.py`, `INDEPENDENT_REVIEW.md`, `generated/INDEPENDENT_REVIEW.json`: independent tail, carrier, degree, and circuit review without builder/verifier imports.
- `check_source_independent.py`, `INDEPENDENT_SOURCE_REVIEW.md`, `INDEPENDENT_SOURCE_CHECK.json`, `INDEPENDENT_SOURCE_RECEIPT.json`: independent split-source and reduced-block audit.
- `SOURCE_PINS.json`: exact raw-file provenance, including the supplied late FreeCoordinate proof/review, retained verbatim under `upstream/`.
- `coefficients/old_tuple/`: the entire authenticated original31 four-port tuple used by this equation. No ports are mixed with the alternate packet52 tuple retained solely for the source-transcription bridge.

## Reproduce

From the package root:

```sh
python3 nine_free_adjunct/build_nine.py
python3 nine_free_adjunct/verify_nine.py
python3 nine_free_adjunct/independent_review.py
python3 nine_free_adjunct/check_source_independent.py
```

Or use the corresponding path from this repository root. No package installation or network access is needed. The primary finite checker deliberately rejects optimized Python because its imported source auditor uses assertions; both independent checkers also pass with `python3 -O`.

The main checker authenticates all imported files and the full tuple, rebuilds four circuits, proves the exact kernel expansion and finite isolation certificate, evaluates the actual tuple modulo three primes, verifies named-register identities, and checks binary/CRT/radical fixtures. These finite audits support the implementation and do not replace the unbounded proof or imported theorems.

## Attribution and limits

The late supplied FreeCoordinate archive is pinned at repository snapshot `4b4349064a750ba6347293b55874a7f92abdd0db`. It supplies free `C`, the positive quotient shift, and removal of the leading binary block. The new split116 source and normalized-margin finalizer come from this iteration's earlier work. This adjunct newly composes them, reproves all changed numerical hypotheses, and certifies the resulting literal polynomial. The new builder does not execute upstream programs.

The source floor remains the already proved `a = 2^2134939 = 4096 * 2^2134927`. The recalibrated threshold uses `c = 2^17079501`. The exact diagonal leading coefficient is `2^186 * a^954792 * c^400`, strictly positive. Both independent reviews are internal AI-assisted audits, not external human peer review.
