# Smaller explicit Diophantine equations for ZFC consistency

Research package prepared for Vladimir Reshetnikov and ProveIt, 23 October 2026.
Baseline: **124c07c0b77a9e20e84676514d8b1ff78536ea3f**.

Read **[report.pdf](report.pdf)** for the article, or compile
**[report.tex](report.tex)** with the supplied section files. The comparison
uses the actual wave-6 packages 38–45 as well as the active research status,
rather than relying solely on the older collection summary.

## Results

| Form | Supplied unknowns | Exact degree | Live binary operations | Reviewed comparison |
|---|---|---:|---:|---|
| Support-aware Jones | 9 positive | 30,947,584 | 651 | Package 45: 129,875,980 / 788 |
| Nonnegative translation | 9 nonnegative | 30,947,584 | 654 | Package 45: 129,875,980 / 791 |
| Support-aware Sun | 10 unrestricted integers | 56,593,864 | 653 | Package 40: 237,520,456 / 782 |
| Midpoint quotient absorber | 11 positive | 954 | 115 | Package 38: 1140 / 129, or 1154 / 123 |
| Midpoint system | 11 positive | 2 and 952 | 111 | Two equations |
| Shifted midpoint system | 11 positive | 2 and 952 | 110 | Two equations; equality tests free |
| Ordinary-strong quotient absorber | 14 positive | 56 | 79 | Historical Q56: 15 positive / degree 56 / 74 operations |

The archive also retains the full-carrier eleven-variable comparison:
degree 958 / 116 operations; its systems use 112 or 111 operations.
The midpoint version improves it on both displayed measures.

An operation means one binary addition, subtraction, or multiplication,
including squaring and multiplication by a numeral. Shared registers and
fixed coefficient leaves are free under this arithmetic-circuit convention.
Every delivered input and gate is live. Exponents are fixed, and the literal
circuits expand them into multiplication gates. Registers are abbreviations,
not additional quantified unknowns. Coefficient size is reported separately.

These are improvements at specific points of a size tradeoff. No global
minimum or new absolute operation-count record is claimed: the reviewed
historical P67 remains a 67-operation circuit on 15 positive unknowns.

## New ideas

1. **Protect only supported monomials.** Of the 528 possible quadratic
   monomials, only the 71 occurring in the source must have isolated labels.
   Each is still isolated against *all* 528 monomials, including unsupported
   ones. Unsupported labels may collide. A certified weight vector of maximum
   190 replaces maximum 799; all 71,808 source/expansion combinations are checked.
2. **Use the coupled root gap.** The sufficient inequality is
   `d*(I*g-c*f) > b+c*f`. It is available before recovering the deleted index
   quotient; the stronger inequality `I*g-c*f>1` is unnecessary.
3. **Recover an exact index with a small modulus.** Set `U=4*q^4`.
   The carrier gives `U | H*(k-R-1)`, while `gcd(U,H)` is at most three.
   Pell congruences and a short index range recover `2*n=R+1`, and hence
   reconstruct the omitted positive quotient.
4. **Clear the midpoint denominator within the carrier.** The midpoint
   `ell+k/2` needs no global doubling because `U/2=2*q^4` is a polynomial.
5. **Bootstrap the ordinary strong-rank lemma early.** For the degree-56
   form, the congruence already forces a large main Pell index before its
   equality to R is known. This supplies the strict hypothesis of the
   inherited ordinary strong-rank lemma and removes one supplied variable.

## Exact logical claim and dependencies

For each polynomial P on its specified domain D, the mathematical reductions
compose to establish

    ZFC proves: (there is no x in D with P(x)=0) iff Con(ZFC).

Here Con(ZFC) is syntactic consistency for the repository's explicit axiom
predicate, whose endpoint is `¬ BProv ZFCax_s [] Form.fBot`.
The inherited chain is finite ZFC refutation iff literal blank K215 halts
iff the calibrated positive compiler source has a solution.

The new encoding and Pell adapters have ordinary mathematical proofs.
The unbounded compiler/native-window calibration, signed or ordinary
strong-rank interfaces, and K215/refutation endpoint are inherited from
the pinned sources. The nine-variable form uses the Jones interface.
Only the ten-unrestricted-integer form additionally uses Sun's 2026
ten-integer theorem. That theorem is Sun's contribution, not ours.

The article identifies these interfaces rather than claiming that finite
arithmetic tests prove an unbounded semantic theorem. It supplies no new
end-to-end Lean/Rocq certificate and no exported object-language ZFC proof.
The active repository status explicitly leaves those explicit compiler
obligations open. No consistency assumption is used to choose coefficients;
the package does not prove either consistency or inconsistency of ZFC.
The independent local reviews are AI-assisted reviews within this work,
not external human peer review.

## Fixed coefficients

All new main forms use the **complete, unchanged package-31 tuple**:

    B_native = 2^1064921
    beta = B_native - 1
    K0 = DC + B_native*DR
    MC = native current mask
    MF = MF_native + B_native - 1

**MF is already shifted.** Do not substitute an unshifted mask, mix ports
from different tuples, or interpret a historical upstream default binding
as the active binding. The four uncompressed payloads total 533,099 bytes.
The compressed binaries, SHA-256 bindings, finite construction recipe,
430 literal K215 actions, and 943-tile list are all included. The recipe
does not search for a contradiction or wait for the machine to halt.

`coefficients/ports.json` is the active binding for the eleven- and
fourteen-variable forms. The packing subtree contains a byte-identical
complete copy and exact recipes for its derived coefficient leaves.
We retain this tuple to make the arithmetic change independently reviewable;
we do not claim the smallest native coefficient payload in the repository.

## Files

| Path | Purpose |
|---|---|
| `report.tex`, `report.pdf` | Main article, equations, proof details, comparison, dependencies |
| `packing/` | Nine- and ten-variable circuits, support theorem, certificates, rebuild scripts |
| `eleven/` | Eleven-variable literal circuits, builders, leading-form and norm checks |
| `fourteen/` | Degree-56 equation, full reduction proof, symbolic degree check |
| `coefficients/` | Coherent fixed tuple, finite recipe, original table data |
| `review/` | Local mathematical reviews and independent formal-radical multiplication auditor |
| `provenance/` | Pinned inherited proofs, comparison snapshots, licenses and source ledger |
| `verify.py` | Offline combined rebuild and finite verification driver |
| `VERIFICATION.json` | Ordered verification receipt; explicit scope limits |
| `ARTIFACT_MANIFEST.json` | SHA-256 hashes of the delivered files |

## Reproduce

Use Python 3.10 or later and NumPy. Only the eleven-variable complete
univariate polynomial degree check requires NumPy; the other checks use
the standard library. No network or ProveIt checkout is required.

```sh
python3 verify.py
make pdf
```

The driver verifies source and coefficient hashes, reconstructs the finite
coefficient recipe in a temporary directory, rebuilds all circuits, and runs
the support, liveness, exact-degree, and independent norm audits. It writes
`VERIFICATION.json`. Run without Python's `-O` option, since some inherited
finite auditors use assertions. A normal run takes under a minute on the
creation environment; speed is machine-dependent.

The release manifest identifies the supplied bytes. After deliberately
editing files or rebuilding a PDF with new timestamps, use
`python3 verify.py --skip-release-hashes`; inherited source and coefficient
hashes remain mandatory, and all mathematical finite checks still run.

The PDF build needs a standard pdfLaTeX installation with AMS, Latin Modern,
microtype, hyperref, geometry, fancyhdr, enumitem, booktabs, and related
standard packages. `make clean` removes only TeX auxiliary files and Python
caches; it preserves the PDF and all delivered mathematical data.

## Integration

Copy the complete directory into a new source directory under
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/`.
Assign its collection number at intake. Preserve the active tuple, source
ledgers, and inherited notices. No existing repository files, remote branch,
or pull request were changed by this work. Historical paths inside verbatim
sources remain meaningful at their own pinned commits.

New material is supplied under the root MIT-0 license. Inherited material
retains its original notices and licenses; see `NOTICE.md` and `provenance/`.
