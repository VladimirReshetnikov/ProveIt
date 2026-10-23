# Smaller explicit Diophantine forms for Con(ZFC)

**Ten unrestricted integer unknowns, exact degree 69,554,088,184, and
1,333 binary arithmetic operations.** A secondary construction has twelve
strictly positive unknowns: one equation of degree 938 in 122 operations,
or three equations of maximum degree 929 in 117 operations.

This research package supplies ordinary mathematical proofs, literal
arithmetic circuits, the complete fixed coefficient data, and offline
verification programs. For its primary polynomial `F10`, it establishes

\[
\mathrm{ZFC}\vdash
\left(\neg\exists(f,g,h,k,l,w,x,y,z,m)\in\mathbb Z^{10}\;
F_{10}(f,g,h,k,l,w,x,y,z,m)=0\right)
\ \longleftrightarrow\ \operatorname{Con}(\mathrm{ZFC}).
\]

The secondary equation and system have the analogous equivalence over
`Z_{>0}^12`. These are equivalences for the repository's fixed proof
predicate, not assertions that either side has been decided.

The source snapshot is ProveIt commit
`22e75dd6b87b1b199bb08c778d7cf075ae5aae08`, in
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms`.
The report and appendix explain all mathematical dependencies explicitly.

## Main result and comparison

The direct comparison is with the pinned `31-sun10` ten-integer equation.
Both use the same complete source quartic and fixed coefficient tuple.

| Construction | Domain | Equations | Exact degree | Binary operations |
|---|---|---:|---:|---:|
| Source 31 baseline | 10 unrestricted integers | 1 | `126496*5^31 + 27064` | 1,442 |
| This package, primary | 10 unrestricted integers | 1 | **69,554,088,184** | **1,333** |
| This package, original Sun finalizer | 10 unrestricted integers | 1 | 1,323,756,220,880 | 1,383 |
| This package, positive equation | 12 strictly positive integers | 1 | **938** | **122** |
| This package, positive system | 12 strictly positive integers | 3 | **929** | **117** |

The primary degree is `113856*610895 + 27064`. The baseline degree is
589,042,901,992,797,851,562,527,064, so the degree improves by approximately
`8.468846582e15`, while the operation count falls by 109, or about 7.56%.
The primary circuit has 484 additions, 25 subtractions, and 824
multiplications. Each binary `+`, `-`, or `*` counts once, including
multiplication by a fixed numeral. Fixed leaves and reuse are free; every
fixed power is expanded into binary multiplication gates.

The secondary equation improves the pinned source-34 degree-1022,
124-operation positive equation. The comparison is within the positive
domain. This package does not improve the existing nine-natural-variable
count, the low-degree quartic frontier, or every operation-count frontier.
The positive forms and the unrestricted-integer forms have different
domains and should be compared accordingly. No global minimum or new
general variable-count theorem is claimed.

## What changes mathematically

### A finite additive code replaces exponentially spaced digit positions

The existing source quartic has 31 variables. Its previous encoding used
positions `5, 5^2, ..., 5^31`. The necessary property is that distinct
monomials of total degree at most four receive distinct exponent sums.
The new construction obtains this property from a classical Bose--Chowla
`B_4` set with 32 elements, one translated to zero for padding. Its largest
weight is only **610895**.

For the source polynomial `P(n)=sum p_alpha*n^alpha`, define

\[
c_\alpha=(4-|\alpha|)!\prod_i\alpha_i!\,p_\alpha,
\qquad e(\alpha)=\sum_i\alpha_iw_i,
\]
\[
D(T)=\sum_\alpha c_\alpha T^{4W-e(\alpha)},\qquad W=610895.
\]

The exact identity

\[
[T^{4W}]\left(1+\sum_i n_iT^{w_i}\right)^4D(T)=24P(n)
\]

replaces the old positional encoding. The full set of 52,360 monomials
of total degree at most four is covered, including monomials absent from
the sparse source. Sun's digit mask already accepts arbitrary positions;
the proofs here check coefficient bounds, carries, positivity, and all
source size conditions for the replacement.

The downstream ten-integer reduction is Sun's theorem. The primary
equation retains source 31's coprime positivity merger, quintic merger,
and separating norm. A second circuit uses Sun's original finalizer,
making the large degree improvement reviewable without those source-31
finalizer refinements. The Bose--Chowla construction and Sun's general
ten-unknown theorem are attributed to their authors.

The final circuit uses shared binary factors to evaluate the required
powers. Every power gate is verified by adding exact integer exponent
labels. This changes evaluation cost without changing the polynomial.

### A smaller separator for twelve positive unknowns

The secondary result combines source 37's coordinate change
`w_old = w + q` with source 34's translated carrier and the new separator

\[
M=k(ik^3+T)^2.
\]

The separator has degree 9. A sharper root bound proves the required
separation and recovers the integer Pell roots in both directions. The
complete formulas and proofs are in `positive/POSITIVE_PROOF.md` and the
report. Its twelve unknowns are strictly positive; the unrestricted
integer interpretation is not asserted.

## Explicit coefficients and identity of the equation

`data/INSTANCE.json` is the authoritative binding for the new primary
equation. `generated/equation10.json` is its division-free arithmetic
circuit. Its SHA256 is

```text
6c80191869b421514b51eaabc28188e438f2b00f44e68606a72f9b439f67dcce
```

There are exactly ten quantified variables and no quantified coefficient
ports. The 79 fixed circuit leaves are numerical constants with complete
finite recipes and supplied data; they are not additional unknowns.

Both constructions retain the **whole source-31 coefficient tuple**. Its
payloads are in `upstream/source31/signed10/data/`. In the positive forms,
the aliases are `beta -> beta`, `K0 -> K`, `MC -> MC`, and
`MF -> MF_source`; the last mask is already shifted. No coefficient is
spliced from source 36 or another tuple. The additional source-coding
constant for the ten-integer construction is `beta_sun = 2^4269882`.

The unchanged source-31 `INSTANCE.json` is retained inside `upstream/`
for coefficient provenance. Its old radix-five positions and old output
pointers do not specify the new polynomial; the top-level
`data/INSTANCE.json` does.

`upstream/SOURCE31_MANIFEST.json` records the pinned source files and
their hashes. Upstream licenses and attribution notices remain alongside
the copied material.

## Reproduce offline

Run the following commands from this package directory. All data required
by the provided verification drivers is included; they make no network
requests and require no surrounding ProveIt checkout.

### Primary result: Python standard library

Python 3.10 or later suffices:

```sh
python3 reproduce.py
```

This checks the coefficient reconstruction, complete tuple and bound,
finite-field and additive-code certificates, literal circuit identities,
power sharing, operation counts, and exact degree certificates. It also
replays the fixed coefficient generation. Results are written under
`generated/`.

To emit the primary circuits directly:

```sh
python3 code/build_equation.py
```

The two emitted circuits are `generated/equation10.json` and
`generated/equation10_sun_finalizer.json`.

### Positive result: Python with NumPy

With NumPy available in the Python environment:

```sh
python3 positive/build_majorant.py
python3 positive/check_majorant.py
```

The secondary checker verifies the supplied tuple, the formal radical
product, the leading expression, and full univariate degree evaluations.
Its receipt is `positive/CHECK_RESULTS.json`. NumPy is needed only for
these secondary polynomial checks; it is not needed by `reproduce.py`.

### Report

A standard LaTeX installation with `latexmk` and `pdflatex` rebuilds the
included PDF:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

## What the checks establish

The finite checks establish concrete arithmetic facts about the delivered
data and circuits. Among them are the exact source reconstruction, all
52,360 additive-code cases, a complete power-label audit, coefficient
hashes, and nonzero leading coefficients proving that the degree upper
bounds are attained. The independent circuit audit compares the emitted
circuits with direct formulas.

The unbounded equivalence uses the **ordinary mathematical proofs**, the
explicit inherited blank-K215 compiler/calibration theorem, and the cited
Sun results. Sun's 2026 result is an external preprint dependency. Neither
the finite computations nor inclusion of the existing endpoint Lean file
constitutes a new end-to-end Lean or Rocq proof. This package does not
search for a ZFC refutation, prove Con(ZFC), or establish two-sided
independence from consistency alone.

## Main files

| Path | Purpose |
|---|---|
| `report.tex`, `report.pdf` | Main mathematical report and compiled version |
| `data/INSTANCE.json` | Binding of the new primary polynomial |
| `data/weights_certificate.json` | Frozen additive weights and finite certificate |
| `generated/equation10.json` | Primary 1,333-operation polynomial |
| `generated/equation10_sun_finalizer.json` | Variant with Sun's original finalizer |
| `code/build_equation.py` | Explicit polynomial circuit generator |
| `code/weights.py`, `code/shared_powers.py` | Additive code and exact shared powers |
| `reproduce.py` | Offline primary verification driver |
| `proofs/` | Detailed coding proof and independent mathematical audits |
| `positive/` | Twelve-positive-variable equation, system, proof, and checks |
| `upstream/` | Pinned source material, fixed coefficient data, and notices |

## Suggested repository integration

Place the complete directory under the existing report, for example as

```text
SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/
  con-zfc-diophantine-forms/38-bose-chowla/
```

`38-bose-chowla` is a suggested new directory name, not a claim that the
repository already assigns that source number. A descriptive name can be
used if the numbering changes. Preserve the package's relative layout so
the offline drivers continue to find their bundled data. Add a catalogue
entry distinguishing the ten-integer result from the twelve-positive
result, and retain the inherited notices when integrating the sources.

See `NOTICE.md` for attribution, licensing scope, and the AI-assistance
notice.
