# Commensurate Lerch Calculus

**Finite cyclotomic closure, unequal-center expansions, harmonic remainders,
and Stieltjes–Gamma identities.** Research continuation for Vladimir
Reshetnikov's ProveIt programme, 10 October 2026 (Pacific time).

The 26-page article gives analytic proofs. The exact and numerical programs
are independent checks of the implementation, not substitutes for those proofs.

## Main files

- `ProveIt_Commensurate_Lerch_Calculus_2026-10-10.pdf`: compiled article.
- `ProveIt_Commensurate_Lerch_Calculus_2026-10-10.tex`: standalone, self-contained source.
- `article.tex`, `preamble.tex`, `references.tex`, `sections/`: editable modular sources.
- `code/commensurate.py`: reusable exact Laurent-table and numerical identity engine.
- `code/verify.py`, `code/verify_extra.py`: executed verification suites.
- `verification/`: complete JSON records, summary, tables and build/review notes.
- `integration/`: theorem map, scope safeguards, and suggested incorporation.
- `SOURCE_AUDIT.md`, `source-audit.json`: inspected sources and explicit access limitations.
- `SHA256SUMS`: checksums of the delivered members, excluding the checksum file itself.

## Reproduce

Use Python 3.10 or newer, with the packages in `requirements.txt`.
The completed run used Python 3.13.5, SymPy 1.14.0 and mpmath 1.3.0.

```sh
python3 -m pip install -r requirements.txt
make verify
make pdf
```

Without `make`, execute the three verification scripts and then
`code/summarize_verification.py`. To rebuild the PDF, execute
`code/make_standalone.py` and run `pdflatex` three times on the named standalone
source. A normal TeX Live installation with AMS packages, Latin Modern,
mathrsfs, microtype, geometry, hyperref, enumitem and booktabs suffices.
No network access is needed after dependencies are installed.

The scripts write new result files, including fresh timing values. PDF metadata
and run times may differ on a rebuild; the supplied checksums identify this
specific delivery, not a promise of bit-identical rebuilding.

## Example use

```python
import sys
sys.path.insert(0, 'code')
import mpmath as mp
from commensurate import pole_table, central, pair_master, odd_resonance

mp.mp.dps = 55
T = pole_table((1, 2, 3))
print(T.coefficients)                    # exact SymPy coefficients
print(central(T, mp.mpc('0.4', '0.3')))   # all-complex-order central value
print(pair_master(2, 1, 1))              # pi*Catalan - 3*zeta(3)/8
print(odd_resonance((1, 2, 3), 0))       # 49*pi**2/432
```

Supply rational scales as integers, SymPy rationals, or rational strings such
as `'2/3'`. Decimal binary floats are not a reliable way to specify intended
rational scales. Pole-table size depends on the common multiple and may be
large. The generic finite-Lerch evaluator intentionally exposes only the
negative-real-mu branch; positive-real branch cancellation is proved in the
article, not implemented as an automatic numerical boundary-value routine.
The general mixed-moment reduction is proved as a terminating algorithm;
the code verifies its polynomial recurrence but does not expose a complete
one-call arbitrary-multiindex moment evaluator.

## Result status

The package proves commensurate-scale finite closure for aligned, normalized
profiles, a normally convergent unequal-center expansion in a common weighted
strip, every mixed logarithmic moment, all anchored primitive orders, and a
universal negative-integer parity law even for incommensurate scales. The
necessary normalization and the two restricted rigidity statements are explicit.

The completed suites contain **307 exact assertions, 91 numerical diagnostics,
and five negative controls**. Numerical checks are not interval-certified.
Historical priority for every special case and novelty relative to every
unread incoming ZIP are not claimed. Canonical Gaussian S6 and revised S8
remain unresolved by this delivery. No repository or Library file was modified.
