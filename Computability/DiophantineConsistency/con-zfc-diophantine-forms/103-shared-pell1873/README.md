# An explicit quartic for Con(ZFC), with shared Pell certificates

**The primary deliverable is a fully expanded polynomial in 1,873 unrestricted integer variables, of exact degree four.** Its zeros are equivalent to finite ZFC refutations through the ordinary proof supplied here and the pinned C222 calibration. Consequently that proof establishes, within ZFC,

\[
\bigl[\forall z\in\mathbb Z^{1873},\;P(z)\ne0\bigr]
\quad\longleftrightarrow\quad\operatorname{Con}(\mathrm{ZFC}).
\]

Start with [the report](report/Batched_Pell_1873.pdf), or its editable [LaTeX source](report/Batched_Pell_1873.tex). The coefficient list is [equations/polynomial.json](equations/polynomial.json); [FORMAT.md](FORMAT.md) explains how to read it.

The equation is also supplied as

\[
P(z_0,\ldots,z_{1872})=\sum_{j=0}^{1467}Q_j(z)^2=0.
\]

Every quadratic residual \(Q_j\) is explicitly listed in `equations/residuals.json`. Over integers, this equation is equivalent to all 1,468 residuals vanishing. The independently collected expansion in `polynomial.json` specifies the same polynomial. Neither representation leaves a power, factorial, binomial coefficient, bounded quantifier, unspecified compiler output, or external numerical coefficient unresolved.

## Exact outputs and comparison

| Measure | Primary: `equations/` | Smaller height: `equations_small_height/` |
|---|---:|---:|
| Unrestricted integer variables | **1,873** | 3,292 |
| Exact degree | 4 | 4 |
| Quadratic residuals | 1,468 | 2,887 |
| Nonzero collected monomials | 77,523 | **11,218** |
| Largest absolute coefficient | 1,323,565,948,780,873,728 | **14,869,246** |
| Nonlinear arithmetic wires | 1,153 | 1,153 |
| Retained affine wires | 37 | 1,456 |
| Extra nonnegativity witnesses | 438 | 438 |

Both equations share 245 semantic input slots: 146 receive explicit nonnegativity guards and 99 have unrestricted integer domains. Nonnegativity of 23 of the latter is inferred from their arithmetic equations: three ordinary division quotients, eleven binomial high quotients and nine range/index divisibility quotients. The primary variable count is exactly

```
245 + 1,153 + 37 + 438 = 1,873.
```

The companion retains more affine values before multiplication. Its residuals have at most five monomials, reducing coefficient height and expansion size at the cost of more variables. Both represent the same consistency condition, with exact integral restoration of the added wires.

The inspected ProveIt baseline is commit `b594a5e988e986f695923d068ef3d33ab2ada16f`, including the incoming `ConZFC_Direct_Projection_7617.zip`. The primary improves that direct-calculus quartic from 7,617 to 1,873 variables, a reduction of approximately 75.4%. **The repository also records a native-coefficient quartic with 37 integer variables**, as well as lower-variable equations of higher degree. The present result is therefore a reduction of the direct proof-calculus construction, not an overall variable-count record or a proof of global minimality. Historical priority for the underlying batching idea is not asserted.

## What changes mathematically

Forty positive power graphs now share one bootstrap Pell base, one auxiliary Pell solution, and one CRT comparison base. A common bound replaces forty separate output bounds. Joint completeness is proved by choosing the bootstrap cofinally, then a Pell solution satisfying all divisibilities, and finally a sufficiently large CRT representative; the proof justifies identifying the existential witnesses.

Equal exponents share their Pell coordinates, even across different power bases. There are nineteen exponent expressions. Exact recurrences supply three of them from existing pairs, leaving sixteen seed certificates. A signed index-recovery theorem permits both comparison progression quotients to be unrestricted integers. Removing their sign guards saves 96 integer variables across the sixteen seeds.

The source retains the eight-column direct C222 certificate. It substitutes deterministic rule constructors before bounded-row compilation, evaluates the local polynomial directly with signed arithmetic, and bounds its absolute value using a nonnegative arithmetic circuit. A prime-power CRT lift supplies bounded witnesses. These steps and their domain conditions are described in `proofs/SOURCE_AND_DOMAIN_AUDIT.md`.

## Logical and verification scope

The logical input is the fixed twelve-rule numerical C222 calculus, with contradiction label 1. Its calibration to finite ZFC refutations is inherited from the pinned ProveIt development, including the constructible-choice bridge. `provenance/LOGICAL_SOURCE_PINS.json` records the exact sources and hashes; the logical pin is `9a33342a03d19cf5b061b2083c6b5d3f27f752ed`. This construction uses that calculus directly and does not simulate K215 or specialize Jones's universal polynomial.

The report and proof notes provide ordinary mathematical proofs formalizable in ZFC. The Python checks verify exact finite transcription, source interfaces, domain restoration, arithmetic identities, deterministic generation, and every collected coefficient. **They are not a new Lean proof or an encoded object-language ZFC derivation of the complete endpoint.** Inherited arithmetic and logical theorems remain explicit dependencies. No assumption that ZFC is consistent is used to establish the equivalence, and the package does not prove that this polynomial has no zeros.

## Reproduce and verify

The builders and checkers require Python 3.10 or later and its standard library. No network access, symbolic-algebra package, or proof-assistant installation is needed for the finite replay. From the extracted package directory run:

```sh
python3 verify_release.py
```

The release verifier rebuilds both equations in temporary directories under normal and optimized Python, compares all six JSON artifacts byte for byte, and runs the independent source, batch, signed-index, recurrence, and complete-polynomial checks. It preserves the supplied equation files and writes its receipts to `checks/RELEASE_*.json` and `checks/RELEASE_VERIFY.json`. A failure returns a nonzero exit status.

To build inspectable separate copies:

```sh
python3 build.py --output rebuilt_primary --affine-cap 16
python3 build.py --output rebuilt_small_height --affine-cap 1
python3 verify_polynomial.py rebuilt_primary
python3 verify_polynomial.py rebuilt_small_height
```

To rebuild the report with a standard TeX Live installation containing the packages named in its preamble:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -cd report/Batched_Pell_1873.tex
```

The deterministic SHA-256 of the **primary polynomial JSON bytes**, including its terminal newline, is

```
18d09e54a3d66ed33422560a35724a5073fd1ca1a2a76bfaf16e634cb019ea1d
```

The companion's polynomial hash is

```
1ff012b6236393478112e3ab622f081fba3caf9987dc03c074d2a8cb91124fc2
```

## File map

| Path | Purpose |
|---|---|
| `report/` | Full article, editable LaTeX, compiled PDF |
| `equations/` | Primary polynomial, residuals, DAGs, local source, exact metrics |
| `equations_small_height/` | Complete companion with smaller coefficients and fewer monomials |
| `build.py`, `positive_arithmetic.py`, `signed_backend.py`, `polynomial.py` | Deterministic arithmetic construction and integer quartic compiler |
| `source/` | Literal C222 rule data and projected direct-source builder |
| `verify_release.py` | Complete finite release replay |
| `verify_source.py`, `verify_source_negative.py`, `verify_batch.py` | Independent source/interface and shared-certificate audits with corruption controls |
| `verify_recurrence.py`, `verify_signed_index.py`, `verify_polynomial.py` | Recurrence, signed-index controls, and full coefficient verification |
| `proofs/BATCHED_PELL_THEOREM.md`, `proofs/SIGNED_INDEX_THEOREM.md` | Main arithmetic theorems and domain conditions |
| `proofs/RECURRENCE_REDUCTION_PROOF.md`, `proofs/SOURCE_AND_DOMAIN_AUDIT.md` | Recurrence and direct-source proofs |
| `provenance/` | Pinned logical/arithmetic sources, hashes, and associated licenses |
| `checks/` | Machine-readable verification receipts |

`proofs/INDEPENDENT_BATCH_REVIEW.md` is explicitly marked as a historical checkpoint. The final signed certificate and exact release metrics are given by the current theorem files, the two `metrics.json` files, and the release receipts.
