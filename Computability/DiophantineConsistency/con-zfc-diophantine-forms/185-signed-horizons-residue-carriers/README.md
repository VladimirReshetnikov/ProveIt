# Signed horizons and residue-encoded Pell witnesses

**Explicit Diophantine equations for the consistency of ZFC**  
Research prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026.

The main deliverable is [the article](report/report.pdf), with editable
[LaTeX source](report/report.tex). It proves new reductions in three
existing, explicitly calibrated constructions. All final equations have
fixed integer coefficients and use only ordinary polynomial operations.

For each delivered final polynomial `P`, in its specified domain `D`, the
claim is the ordinary mathematical theorem formalizable in ZFC:

> ZFC proves `(exists x in D, P(x)=0) iff ZFC has a finite refutation`.
> Therefore ZFC proves `(there are no zeros in D) iff Con(ZFC)`.

The formal presentation of ZFC and its finite proof relation are the
repository's `ZFCax_s`, `BProv`, and `Form.fBot`. The theorem proves an
equivalence; it does not prove consistency or the absence of solutions.

## Which equation to use

| Goal | Completed equation | Domain | Variables | Exact degree | Other exact cost |
|---|---|---|---:|---:|---|
| Low degree and moderate expanded coefficients | `Q214` | unrestricted integers | 214 | 4 | 153 quadratic residuals; height 655,360; 5,875 monomials |
| Fewer variables at degree four | `Q212` | unrestricted integers | 212 | 4 | 151 residuals; much larger coefficients |
| Short factorized integer formula | `P36` | unrestricted integers | 36 | 288 | 145 binary arithmetic operations |
| Few positive variables at minimum delivered evaluation length | `P_E` | positive integers | 14 | 174 | 66 operations |
| Lower degree with fourteen positive variables | `P_q^circ` | positive integers | 14 | 146 | 68 operations |
| Direct construction with small circuit literals | pooled profile | unrestricted integers | 117 | 16 | maximum absolute literal 256 |
| Further direct variable reduction | pooled profile | unrestricted integers | 108 | 32 | maximum absolute literal 256 |
| Fewest delivered direct variables | pooled profile | unrestricted integers | 86 | 2,097,780 | maximum absolute literal 256 |

The `quartic/` equations are literal sums of squares of fully listed
quadratic integer polynomials. The PDF prints all 153 residuals of Q214.
Both quartics also include every collected quartic coefficient as JSON.

The `compact/` equation uses four fixed native constants. Their complete
big-endian byte files total 97,046 bytes; the largest is 194,440 bits.
The article gives a finite reconstruction recipe, and the verifier
regenerates all four integers from that recipe. Registers in a circuit
are polynomial abbreviations, not extra quantified variables.

The `direct/` circuits do not use K215, Jones's universal polynomial, or
Sun's integer-domain reduction. Their small literal constants must not be
confused with their much larger **expanded polynomial coefficient bounds**.
All eight direct profiles and those bounds are in `direct/METRICS.json`.

These endpoints optimize different metrics. No global minimum or
worldwide-priority claim is made. In particular, 36 and 86 are not
variable-count records across all calibrated Diophantine encodings.

Operation counts are binary `+`, `-`, and `*` gates in the supplied
straight-line programs, with fixed coefficients as input numerals and
shared intermediates counted once. They measure arithmetic circuit
length; the bit complexity of big-integer operations is a separate cost.

## New mathematical ideas

1. **Use existing power certificates to recover a signed horizon.**
   Replace a quadratic positive slice by `t=8+16z`. The power equations,
   CRT parity, and beta endpoint force `t>=8` at any zero. Eliminate `t`
   affinely. For Q214 use `U=2t^2` and `K=512U^2`; the growth inequality
   holds even at `t=8`. This is a semantic source change followed by an
   exact affine projection, not a zero-set bijection with the old slice.

2. **Let an auxiliary Pell ordinate carry a missing quotient residue.**
   Replace two old positive witnesses by one signed residue expression
   `u=k-Mn-R`. The main Pell rank is authenticated before restoring the
   deleted quotient. A strict index bound and a growth argument resolve
   the two possible signs. Completeness chooses fresh private Pell
   witnesses, with the required residue built into their construction.
   A separate domain audit leaves `f,n,tau` unrestricted and encodes only
   eleven positive coordinates, giving the 36-integer-variable equation.

3. **Compose a signed horizon, a reused CRT anchor, and oriented pools.**
   The noncircular sign bootstrap permits the earlier oriented power
   pools to be used after removing redundant anchor machinery. Certified
   unit-linear projections give eight final integer profiles. This
   composition credits and retains the earlier Oriented Powers packet.

## Reproduce the finite verification

Python 3.10 or later and its standard library suffice. No network or
third-party Python package is required. From this directory:

```bash
python3 -B verify_all.py
python3 -O -B verify_all.py
```

The root verifier propagates the optimized-interpreter flag to every
child. It checks both quartic expansions and inherited-transform
commutation; all compact graphs, exact degrees, and the integer-domain
lift; full coefficient reconstruction; all direct source bindings,
pool identities, projections, degree witnesses, and corruption controls;
and the match between the printed residual list and the literal Q214.
The direct component also reconstructs its mathematical JSON files.

Release receipts are in `verification/`; the components retain their
more detailed receipts. `SHA256SUMS` binds the final archive contents.
To check the mathematics after intentional changes or a local PDF rebuild:

```bash
python3 -B verify_all.py --skip-manifest
```

To rebuild the PDF:

```bash
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

PDF byte identity can depend on the TeX installation and metadata.
Mathematical reconstruction and release-byte authentication are separate.

## Proof status and inherited calibration

The new proofs have separately assigned AI-assisted mathematical reviews.
The direct branch retains the repository's C222/ZF/ZFC calibration; the
compact branch retains the **whole coherent Start-only4127 coefficient
tuple** and its P66/native calibration. The article identifies the exact
boundary. The finite programs do not establish unbounded soundness or
completeness by testing examples.

The two named Lean endpoint files are included in `calibration/` for
inspection. Their complete transitive import closure is not rebuilt here.
No new end-to-end Lean/Rocq proof term or encoded object-language ZFC
derivation is claimed. Separate AI reviews are not human peer review.

## Repository integration

The source commit is `02a78a08603cbae248c19c23a75907c6c6bd6443`.
See [integration notes](INTEGRATION.md), [provenance and credits](NOTICE.md),
and each component's exact source ledger. The package is additive and
does not require replacing historical equations or their calibrations.

Code and new documentation are provided under the included MIT No
Attribution license. Retained source notices remain with their files.
