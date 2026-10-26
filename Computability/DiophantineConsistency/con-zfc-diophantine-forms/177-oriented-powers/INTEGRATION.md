# Additive integration into ProveIt

Suggested intake title: **Oriented power pooling and polynomial root centering**.
This packet was prepared from ProveIt commit
`0c48d332df6b0e50d4e5b6251c531898f5682c72` for later integration.
No remote repository change is needed to use the supplied artifacts.

## Placement

Place the complete folder as a new contribution under
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/`, assigning
the next directory identifier according to the repository's current intake
procedure. A descriptive suffix such as `oriented-powers-root-centering`
keeps its two mathematical components clear. Preserve the existing numbered
contributions and source identities. The archive may first be staged under
`docs/incoming/` by the repository integrator.

Keep the relative layout of `report/`, `compact/`, `code/`, `sources/`,
`equations/`, `certificates/`, `proofs/`, and `verification/`. The article
includes the compact section using a relative path; the generators and
checkers resolve their own package root. The report needs all TeX inputs
supplied alongside it.

## Suggested catalog entry

Record twelve unrestricted-integer profiles, with the 87-variable profile
explicitly paired with **degree 8,388,612**. Its 24 residuals and 2,447 binary
operations do not make it the lowest-degree or uniformly simplest form.
Useful smaller-degree profiles include **137/12**, **121/16**, **111/32**, and
**99/128**, where the pair means variables/exact degree. The README contains
the complete table and the strict expanded-coefficient bounds.

Record the compact companions in a separate **strictly positive integer**
domain row: **10 variables, degree 224, 90 operations**, and two
**10-variable, degree-232, 85-operation** circuits. Preserve all four fixed
numerical payloads, their finite recipe and their constructor. These are not
ten-unrestricted-integer claims.

Credit sources **158, 168, 152, 163, 164 and 167** as specified in NOTICE.md.
In particular, package 168 suggested oriented weights; the completed
five-base theorem and its literal instances are the present contribution.
Do not describe the coordinate-elimination method itself as new.

## Integration checks

From the extracted package root, with Python 3.10 or later:

```sh
python3 -B verify.py
python3 -O -B verify.py
python3 -B code/build_projections.py --check
```

The profile inventory must include `integer87_degree8388612` and all eleven
other direct profiles. Verify the complete current inventory, not only an
earlier 88-variable receipt. The top-level checker also covers the compact
circuits and the article's generated finite definitions.

Compile the main TeX file twice from `report/` using pdfLaTeX. Preserve the
supplied report sources even when the PDF is regenerated. TeX metadata may
change PDF bytes without changing mathematical definitions.

The two inherited wrapped documents, `proofs/CALIBRATION_AUDIT.md` and
`sources/PARENT_NOTICE.md`, retain their original historical scope. Keep
their editorial wrappers; do not silently promote historical replay claims
to new verification claims of this packet.

## Proof boundary and next formalization target

The new source establishes explicit zero-existence equivalences to the
frozen 225-variable parent. The integral unit-pivot steps have acyclic
restoration maps. The unbounded pooling and positive-domain steps have
their own completeness proofs; they are not merely finite symbolic tests.

Compose with the identified inherited C222/ZF/ZFC calibration for the
ordinary ZFC-provability statement. The full historical proof closure and
Lean import tree are not bundled or freshly compiled by this packet.
If repository policy requires a new formal-kernel theorem, a suitable first
target is the oriented-pooling interface with temporary zero bases, followed
by its seventeen-request instance and the finite unit-pivot certificates.
The compact branch requires a separate positive-domain lift theorem.

Preserve exact metric distinctions: degree is exact; the reported H is a
strict upper bound exponent for expanded coefficients; the circuit-literal
bound is 256; operation counts are binary arithmetic counts. None is a
proof of global minimality or literature-wide novelty.
