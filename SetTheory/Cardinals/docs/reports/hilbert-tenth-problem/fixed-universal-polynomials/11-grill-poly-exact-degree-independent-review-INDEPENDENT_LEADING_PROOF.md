# Independent exact-degree verification

## Result

For the unchanged frozen `universal.dag`, with **all 797,141 coordinates** (six external coordinates and 797,135 witnesses) assigned degree one, the total degree is exactly

\[
\boxed{69,339,973}.
\]

The previous 71,731,007 is a syntactic upper bound. Its excess, 2,391,034, comes from an identically cancelling norm term at gate 3,600,240. No witness equation or domain constraint is imposed anywhere in this proof.

The independent verifier `check_leading.py` reads only raw DAG/JSON data; it does not import or execute producer or upstream modules. It verifies the DAG hash, manifest hash and kernel hash, checks all 3,600,546 topological gate records, matches all 67 frozen kernel rows operand-for-operand, and computes the output's highest homogeneous polynomial exactly as a sparse polynomial in an opaque degree-three base form and the other input atoms. This is a symbolic computation, not a random identity test. The checker has explicit 512 MiB address-space, 180-second CPU/wall-check, and 4,096-monomial sparse-polynomial limits. All checks use explicit runtime failures and remain active under Python `-O`; both ordinary and optimized-mode replays pass.

## Notation and base leading forms

Write N=797,011 and D=3N=2,391,033. Let X denote `input_loader__X`; all other variable names below refer to the corresponding `native.` inputs. Set

\[
J_1=\sum_{j=0}^{794975}\mathrm{Shat}_j,\qquad
p=2^{551890}V_{\rm final}(X+Z_0)J_1,\qquad Q=16p^N.
\]

The verifier checks the raw gates defining P and its degree-three homogeneous form p. In particular it traverses the raw addition graph and checks that each of the 794,976 Shat coordinates occurs exactly once. The other terms in the definition of P have degree below three. Symbolic highest-form propagation through the raw DAG independently gives

\[
\operatorname{in}(\mathrm{scale})=p^N,\qquad
Z_*:=\operatorname{in}(Z)=p^{N-4}H_V.
\]

Thus scale has exact degree D, and Z has exact degree D−11.

For the kernel put b=2·odd_half, k=eta+zeta, γ=ga, and τ=tau_gap. In particular,

\[
u_* = wQ,\qquad c_* = kbQ,\qquad a_* = wbQ^2,
\]

where u=wn2, c=R10a, a=R12. Their degrees are D+1, D+2, and 2D+2 respectively.

## The cancellation is an unrestricted polynomial identity

For d=4a+3,

\[
(u+ac+\gamma d)^2-(a^2+d)c^2
=u^2+2uac+2u\gamma d+2ac\gamma d+\gamma^2d^2-dc^2.
\]

The script independently expands both sides in four abstract indeterminates and checks exact equality of sparse coefficient dictionaries. The six degree bounds on the right are

\[
2D+2,\ 4D+5,\ 3D+4,\ 5D+7,\ 4D+6,\ 4D+6.
\]

The fourth term is uniquely highest. Hence R15 has exact degree 5D+7=11,955,172 and leading form

\[
8\gamma a_*^2c_*=8\gamma w^2b^3kQ^5.
\]

This replaces the syntactic bound 6D+8=14,346,206.

## Leading form of the complete fixed output

Exact sparse homogeneous propagation from the raw records gives these four unit-factor leading forms and degrees:

| Factor | Highest homogeneous form | Degree |
|---|---|---:|
| R15 | 8γw²b³kQ⁵ | 5D+7 |
| P17 | 1024w²b²f²Q¹⁰Z_*² | 12D−16 |
| first_unit | 4wb²k(τ−k)Q³ | 3D+5 |
| bs_q | Q | D |

Therefore the native unit has exact degree 21D−4=50,211,689. Among the 86 residual squares, the unique maximum is the square of comparison index 6 (zero-based), `ic22 − R16`, whose residual degree is 4D+10=9,564,142. Its square has leading form

\[
i^4c_*^8=i^4k^8b^8Q^8
\]

and degree 8D+20=19,128,284. Every other residual has a strictly smaller degree bound. Thus the complete fixed output F has highest homogeneous form

\[
\boxed{\operatorname{in}(F)=
2^{138}p^{23113311}\,\gamma w^5\mathrm{odd\_half}^{15}
(\eta+\zeta)^{10}f^2i^4
(\tau-\eta-\zeta)H_V^2.}
\]

The exponent 23,113,311 is 29N−8. The formula has degree

\[
3(23,113,311)+40=69,339,973=29D+16.
\]

The verifier expands the displayed formula into 23 monomials in p and the auxiliary input atoms and checks exact equality with the independently propagated raw-DAG output form.

Each displayed factor is nonzero in the unrestricted integer polynomial ring, so their product is nonzero. More concretely, setting every coordinate to one makes the homogeneous coefficient

\[
-2^{148}(2^{551891}\cdot794976)^{23113311}\ne0.
\]

It is 3 modulo 17 and 53,942,795 modulo 1,000,000,007. Either nonzero residue is a deterministic certificate that the upper bound is attained; no probabilistic inference is needed.

## Scope, assumptions, and secondary review

- The exact frozen DAG SHA-256 is `a07c1ba41e3a18fafd05c19b8ac39211b0475e30ed8a08ddf43c45a9f5f440f2`
- The manifest and kernel JSON pins are checked by the script; all coordinates are independent indeterminates of degree one
- Constant recipes denote fixed integers, not degree-bearing variables or variable exponentiation
- Neither witness positivity nor any residual equality is used as an algebraic rewrite
- This result concerns the total degree of this frozen polynomial; it does not independently establish its universality theorem or an optimum among representations
- No frozen artifact or earlier report was changed

The separate `../check_degree.py` was also reviewed. Its degree-bound/top-coefficient invariant is sound even when an intermediate coefficient vanishes. Its sole degree override is justified by the exact norm identity and raw-kernel match. The modular `geom4` evaluation correctly computes the integer geometric sum. No mathematical defect was found in the streamed certificate logic. The present symbolic raw-DAG check is independent of that modular checker.

## Portable replay

`SOURCE_DIR` must contain the pinned `universal.dag`, `universal.json`, and `native_unit_kernel.json`. The original artifact directory or the `reproducibility/frozen/arithmetic` directory of the extracted Report 23 package both have the same pinned files. Run from the directory holding this checker:

```sh
python check_leading.py --source-dir "$SOURCE_DIR"
python -O check_leading.py --source-dir "$SOURCE_DIR" --output independent_leading_result_optimized.json
```

The required source-directory option makes no assumption about the extraction location. The optional output path is absolute or relative to the checker directory. The source directory is only read.
