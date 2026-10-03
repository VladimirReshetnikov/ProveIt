# Independent source review of the asymmetric complete74 transfer

**PASS. No author change is requested.** All three frozen sources change only X=wq³ to X=wq, keep Y=sq³ and every comparison, and retain the complete paid counts. The full polynomial coordinate identities, exact degrees44/68/68 and ten declared public interfaces pass this independent review.

The reviewed [author source](complete74_asymmetric_scale_transfer.py), [receipt](complete74_asymmetric_scale_transfer.json) and [note](complete74_asymmetric_scale_transfer.md) are pinned by SHA256 in the [independent receipt](review_complete74_asymmetric_scale_source.json), together with all13 declared source/proof dependencies. The [independent helper](review_complete74_asymmetric_scale_source.py) reconstructs the source and proofs without invoking the author's structural, degree or verification helpers. It executes the authenticated author module only to exercise the declared public interfaces. No historical compiler module or suite is imported.

This review covers source arithmetic, maps, degrees, provenance and API behavior. The native positive inverse is separately challenged in the [mathematical review](review_complete74_asymmetric_scale_math.md); it is not re-proved here. The author note accurately limits the positive-zero theorem to admissible fixed compiler slices.

| Mode | Positive supplied witnesses | Equations | Comparison DAG | Complete SOS | Exact degree |
|---|---:|---:|---:|---:|---:|
| raw30 | 30 | 19 | 40M+34A=74 | 59M+71A=130 | 44 |
| positive22 | 22 | 11 | 40M+34A=74 | 51M+55A=106 | 68 |
| signed20 | 20 | 9 | 40M+34A=74 | 49M+51A=100 | 68 |

## Whole-source maps and accounting

Starting from each actual pinned [parent packet](complete74_factored_first_norm.json), I independently replace `wn2=w*n2` by `wn2=w*q`, regenerate the entire SOS, and compare every resulting row. The paid q² and q³ rows remain. The Y operand is still `s*n2`; it is not accidentally changed alongside X. The supplied w has exactly one source consumer and no direct comparison consumer. All fixed numeral names, ordinary input x, witness names, original comparison indices and comparison operands are identical to the selected parent.

For the polynomial forward map, q is supplied in raw30 and computed independently of w in the other forms. Set `w_new=q²*w_old`, fixing all other coordinates. An independent expression normalizer flattens associative products and normalizes linear combinations; it inserts no common-X cut. Running both complete sources proves equality of all336 computed registers, all39 residuals and all three finalized polynomials. In particular,

\[
 F_{\rm new}(v,q(v)^2u)=F_{\rm old}(v,u)
\]

holds over every commutative ring, including q=0. For nonzero q, the rational substitution `u=w_new/q²` gives the inverse polynomial identity. These are coordinate identities, not equality of old and new polynomials at unchanged w.

The independent ledger checks source closure and liveness of every gate and supplied coordinate, and reconstructs every residual subtraction, square and final sum. The comparison schedules remain74 operations. The finalizers cost `3e-1`, giving130/106/100. The first-norm k operand remains supplied k in raw30 and computed eta+zeta in the other two forms. No off-zero equation is silently imposed to replace one by the other.

The forward coordinate map is positive on all positive supplied tuples. The rational inverse is integral only when q² divides w_new. The author's `restore_assignment` checks this condition; the independent native proof establishes it at positive zeros on admissible compiler slices before invoking the symmetric theorem. The `signed20` name does not change its supplied positive-witness domain. This review does not claim an unrestricted signed zero-set bijection, an unconditional integer inverse, or materialized enormous Pell zeros.

## Uniform exact degree

Fixed compiler numeral ports have degree0. Ordinary input and every supplied witness have degree1. Direct propagation gives X degree2, Y degree4 and E=XY degree6.

In raw30, the first-root base is `E*(kY)`, with leading monomial `k*w*s²*q⁷` of degree11. Its norm comparison uniquely reaches residual degree22. The whole SOS therefore has unique leader

`w^4*s^8*k^4*q^28`,

and exact degree44.

In either projected form, the actual c producer has leading form

\[
 c_*=(\eta+\zeta)s\,\mathrm{Bm1}^3J^3.
\]

The auxiliary residual has unique degree34 part `i²*j²*c_*⁶`. Its square yields the full leading form

\[
 \mathrm{Bm1}^{36}J^{36}s^{12}i^4j^4(\eta+\zeta)^{12}.
\]

The helper independently checks all13 binomial coefficients recorded by the author, not merely a specialization eta=zeta. This form is nonzero at every admissible fixed Bm1>0 and has total supplied-variable degree68.

The only competing residual needing cancellation is the input norm. An independent coefficient expansion in W,a,kappa,rho,H verifies

\[
 (W+a\kappa+\rho H)^2-(a^2+H)\kappa^2-1
 =W^2+2aW\kappa+2\rho WH+2a\rho\kappa H
  +\rho^2H^2-H\kappa^2-1.
\]

The literal source ports have weights1,6,13,1,6. The seven terms have degrees2,20,8,26,14,32,0. Thus this residual has degree at most32; every other residual has a direct bound below34. The auxiliary square uniquely supplies the top degree. The complete exact68 claim is consequently distinct from the honest naive source bound76. No numerical degree sampling is needed for this uniform proof.

## Public boundary and replay

All ten declared entry points were exercised: canonical parent, build, rewrite, checked, source export, degree certificate, evaluate, forward assignment, rational pullback and integral restoration. They construct fresh canonical data and reauthenticate all13 dependencies on each call. All130 deliberately changed warm dependency tests reject, as do three changed canonical relative proof paths even with valid flattened fallback copies present.

The review checks malformed source/interface/metadata types, invalid mode and numeric flags, positive-domain violations, q=0 inverse rejection and nonintegral restoration. It also tests27 defensive-copy cases. The old same-coordinate first-norm transformation is correctly archived as historical metadata; the current transformation describes the scale coordinate map. Arbitrary evaluable fixed numbers are not advertised as valid program encodings.

Beyond the formal graph and degree proofs,48 full numerical forward identities,48 rational inverse identities,24 positive forward/restoration round trips and three q=0 forward cases pass. These are algebra/API diagnostics, not accepting compiler witnesses. There are212 rejected calls in total, including the133 dependency-path tests.

```sh
python3 review_complete74_asymmetric_scale_source.py \
  --root /path/to/native-stream-queue \
  --artifacts /path/to/author-trio \
  --expect review_complete74_asymmetric_scale_source.json
```

The writer and a fresh saved-receipt replay from `/` pass exact recursive type/value comparison. The checker receipt includes its own source hash. The author trio remains unchanged. This source completion lowers the three SOS degrees; it does not lower the established universal74 comparison or86 polynomial operation bounds.
