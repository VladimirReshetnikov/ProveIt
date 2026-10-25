# Three direct consistency quartics from a fused front-sign certificate

The principal deliverable is `equations/integer248/equation.json`. It
defines the integer polynomial

\[
 P_{248}(x_0,\ldots,x_{247})=\sum_{j=0}^{181}R_j(x)^2.
\]

Each explicit residual `R_j` has degree at most two. All variables range
over **unrestricted integers**. The claimed arithmetic theorem, composing
the new proof with the retained parent calibration, is

\[
 \mathrm{ZFC}\vdash
 \bigl(\forall x\in\mathbb Z^{248},\ P_{248}(x)\ne0\bigr)
 \ \longleftrightarrow\ \mathrm{Con}(\mathrm{ZFC}).
\]

This statement proves an equivalence. It does not establish consistency,
does not claim a global minimum, and does not assert that the new
arithmetic proof has been checked by Lean. The ordinary proof is in
`PROOF.md`; `BOOTSTRAP_PROOF.md` is an identical copy retained for the
literal transformation-certificate link.

## Measured profiles

| Profile | Integer variables | Quadratic residuals | Degree | Collected monomials | Coefficient height |
|---|---:|---:|---:|---:|---:|
| Matched Common Remainders parent | 252 | 182 | 4 | 5,340 | 128,446 |
| `integer248` | **248** | 182 | 4 | **5,321** | **128,446** |
| `integer246` | **246** | 180 | 4 | **5,048** | 195,955 |
| `integer245` | **245** | 179 | 4 | 21,845 | 314,701 |

Height means the maximum absolute coefficient after collecting the
entire sum of squares. The three new profiles have the same raw arithmetic
source, with different exact monic projection orders. `integer248`
retains the parent's coefficient height while improving dimension and
term count. `integer246` provides the smaller dimension and term count at
a modestly higher height. `integer245` minimizes dimension among these
three emitted quartics, at a substantial term-count cost. These are
explicit comparison points, not a claim of an exhaustive frontier.

## New arithmetic step

The previous source independently required two factorial-front
remainders `r,s` to be nonnegative. Write

\[
 G(a,b,c)=a^2+b^2+c(c+1).
\]

The new source replaces those two ternary certificates by one row

\[
 (r+1)(s+1)=1+G(a,b,c).
\]

This alone permits both `r,s >= 0` and `r,s <= -2`. The new proof lets
the retained factorial binomial digit reject the second branch. The
required bounds are established first by extending the signed-index
power argument to negative bases. Consequently the proof does not assume
factoriality in order to recover the signs that factoriality needs.

The construction also composes the previously supplied odd-square radix
restriction `q=(2z+1)^2`. That earlier result is reproduced and credited in
`INHERITED_ODD_SQUARE_PROOF.md`. The literal source drops three old ternary
guard triples, inserts one triple and one square-root variable, and
retains both other guards unchanged. Its net saving after projection is
four variables in the principal profile; counting only new raw witnesses
would overstate that saving.

The root-branch argument, signed-base lemma, exact low-digit bound,
completeness parity construction and dependency order are supplied in
`PROOF.md`. An independent scoped mathematical review is included in
`review/FRONT_GUARD_INDEPENDENT_REVIEW.md`.

## Literal format and restoration

In `equation.json`, a term `[c,[i,j,...]]` means
`c*x_i*x_j*...`; the empty index list means a constant. Coordinates are
zero-based. Residual order is part of the artifact. The equation is the
sum of the squares of all those residuals.

Each profile also contains:

- `expanded_polynomial.json`: the complete collected quartic, with no
  symbolic macros or elided coefficients;
- `METRICS.json`: its independently recomputed size measurements;
- `projected.json`: the endpoint immediately before integral translation;
- `projection_certificate.json`: every eliminated coordinate's monic
  polynomial restoration, the retained coordinate and row maps, and all
  unused coordinates restored to zero;
- `translation_certificate.json`: the integral bijection
  `old_coordinate = new_coordinate + shift`.

To lift an endpoint zero, first undo the integral translation, then replay
the projection restorations in reverse order. The source-to-factored
equivalence is separately certified by `source/factorization_certificate.json`.
The raw guard modification preserves existence of solutions; it is not
claimed to give a bijection of every arbitrary old private-witness tuple.

`render.py` creates complete variable maps and readable residual TeX for
each profile. `evaluate.py` evaluates a supplied integer tuple exactly;
it performs no search for zeros.

## Reproduction and finite checks

Only Python's standard library is required:

```sh
python3 -B verify.py
python3 -B -O verify.py
python3 -B verify.py --rebuild
python3 -B build.py --output /tmp/rebuilt_signed_front
python3 -B render.py --output /tmp/readable_signed_front
```

The checker imports the retained **independent** algebra checker, not
`build.py` or an eliminator. It reconstructs the entire raw source change
from the parent bytes, checks the exact factoring identities, replays
every monic projection and translation, expands the complete sum of
squares, checks the live variable census and all five reported metrics,
and rejects five deliberate mutations. It also runs the parent finite
audit by default and checks a byte pin for every retained parent file.
The optional rebuild regenerates all 22 delivered JSON files in a fresh
temporary directory and compares them byte-for-byte.

Finite certificate replay establishes the explicit algebraic connection
between these files. The unbounded Pell, factorial, CRT and logical
semantics are ordinary mathematical proofs and inherited calibration
results; the verifier does not convert them into new proof-assistant
theorems or establish consistency from a bounded search.

## Provenance and scope of inherited material

Repository snapshot:
`VladimirReshetnikov/ProveIt@3ecd6a6cf53d47519228328567f45fb7ee9781d9`.
The exact parent is the `direct` component of
`docs/incoming/ConZFC_Common_Remainders_Radix47_2026-10-25.zip`.
`upstream_common/` is an unmodified copy of that component, including its
proof, arithmetic-source and logical-calibration closure. Every copied
file is pinned by `UPSTREAM_PINS.json`; the parent's own earlier-source
pins remain present.

The underlying route uses the repository's direct C222 proof calculus and
the inherited `KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation` calibration. It does
not substitute a new machine for that calculus. The new contribution is
the fused front-sign proof and its exact emitted quartics; odd-square
radices, common normalized remainders, Pell orientation, Horn factoring,
monic projection, and the underlying C222 calibration are predecessors.

The retained parent files keep their original notices and licenses. The
new contribution is distributed under the accompanying `LICENSE`.
