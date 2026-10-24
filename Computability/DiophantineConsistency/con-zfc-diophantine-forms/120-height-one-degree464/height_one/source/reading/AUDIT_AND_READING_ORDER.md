# Direct519 calibration: reading order and scoped review

Prepared on 2026-10-24 during the review of the height-one quartic compiler.
The immediate source polynomial is the centered Direct519 equation with
SHA256 `2a7dec9de97fdf80de1fdef4977b6cdf096bff5fc1dc7a586cdb5fede5333016`.
Its 519 integer coordinates and 321 quadratic residuals are the input to
the new compiler. The source's `section.tex` is retained separately by
that compiler; this folder supplies the most useful earlier mathematical
dependencies for reading it offline.

These are exact copies of selected inherited files. `SOURCE_INDEX.json`
records their original local locations, original archive-relative paths,
sizes, and SHA256 hashes. The set is curated: it is neither the full
Round14 executable pipeline nor the transitive Lean dependency closure.
In particular, relative links in the copied originals can name files not
included in this selection. Original notices and licenses are retained.

## Recommended mathematical reading order

| File | Role |
|---|---|
| The separately retained `section.tex` | The actual signed Direct519 theorem, square frame, orientation bootstrap, 60 guards, Horn factorization, projection, and translation. |
| `proofs/round14_HYBRID_PROOF.md` | The final reciprocal prime-power CRT theorem and the carrier-derived budget `K=2R`; this supersedes earlier range implementations. |
| `proofs/prime_power_AMPLIFIED_CRT_PROOF.md` | The one-sided binomial prime-power range lemma, denominator valuation loss, and precision-`2K` completeness. |
| `proofs/shell_encoding_proof.md` | The bijective square-shell recoding of every natural formula/variable position, fixing truth and falsity. |
| `proofs/reciprocal_moduli_proof.md` | The pairwise coprime moduli `1+(t!)^2/i`, their binomial product, and the original reciprocal architecture. Its old canonical index is superseded by the variable lifted index in Round14. |
| `proofs/shared_radius_proof.md`, sections 1 and 6 | The self-bounding factorial identity and exact norm/product transformations. Its intermediate two-factorial architecture is not the final Direct519 architecture. |
| `proofs/projected_horn_flow.md` | Projected local Horn rules, bounded row coding, accumulator completeness, and proof-tree extraction. |
| `proofs/calculus.tex` and `proofs/COMMUTATIVE_CERTIFICATES.md` | Literal numerical calculus and the single-conclusion nonnegative flow theorem. |
| `proofs/shared_powers.md` and `proofs/shared_indices.md` | Finite common Pell frame, all positive powers simultaneously, and common auxiliary witnesses selected by a finite-unit/CRT argument. |
| `proofs/radix_and_pell.md`, sections 2, 5 and 7 | Low-digit binomial extraction, derived Pell indices, and the bounded-factor carrier degree bootstrap. |
| `proofs/signed_comparison_index_proof.md` | Exact signed comparison-coordinate extension of the Pell index criterion, including endpoint and independent sign cases. |
| `proofs/integer_sign_inference.md` | Legendre guards, ordered sign inference, and exact monic elimination over unrestricted integers. |

The prime-power review is included as a supplementary ordinary mathematical
review, not as a replacement for its proof. The `binding/` files preserve
the actual local-majorant, power-call, domain, factorization, projection,
and translation interfaces that would otherwise be absent from a purely
prose reading bundle. They are selected certificates, not an independently
replayed full source generator.

## Logical and Pell calibration boundary

The numerical-calculus calibration is the composition

1. `KEndpoint.c222_iff_zf_refutation`, identifying `KCode222.C222 Code254.F`
   with a finite refutation of the specified ZF calculus;
2. `ConstructibleChoice.zf_refutation_iff_zfc_refutation`, transporting
   refutability between the specified ZF and ZFC calculi.

The literal source copies are in `calibration/`, together with `Code254`,
`KCode222` and their inherited `CALIBRATION_PINS.json`. That pin is to the
earlier ProveIt commit `08200eb10fde2db408c69dffd840d6920a569b1f`, not to
the current repository head. The incoming Round14 package states its own
public comparison pin `84e16e43092614bae262ca59651cb9d77e31a255`; the
repository inspected for this contribution is pinned to
`45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6`. These are distinct provenance
roles and should not be silently conflated.

`PellRepresentation.criterion_iff_pell` is the exact natural-coordinate
Pell-index interface and calls Mathlib's `Pell.matiyasevic`. The signed
comparison theorem is a further ordinary proof, not literally the statement
of that natural-coordinate Lean theorem. For a signed principal abscissa
`X`, replace it in this theorem's numerical parameters by `abs(X)`, use
`abs(U)`, and replace the comparison abscissa `S` by `sign(X)*S`.
The three norms and needed congruences are preserved, so the theorem gives
`abs(X)=X_k(A)` and `Y=Y_k(A)`. The actual polynomial tuple is not being
asserted to have positive comparison witnesses. The separate power row
then orients the principal root. Keeping this distinction prevents an
invalid direct application of the unsigned theorem to signed coordinates.

The selected Lean files are readable statement-and-proof dependencies.
Their imported modules and the full Mathlib checkout are not included or
rebuilt here. The current review does not claim a new end-to-end Lean
theorem, a sealed object-ZFC proof object, or a fresh formal audit of all
transitive calibration imports. Ordinary finite arithmetic, Pell, CRT,
proof-flow, and syntax-recoding proofs are the mathematical justification
for the new composition; no consistency or arithmetic-soundness assumption
is used in these transformations.

## Critical interfaces examined

No critical mathematical gap was found in the portions read. The following
points are essential to that conclusion and should remain explicit.

* The prime-power range implication is only one-way. Completeness uses
  representatives modulo `d_i^(2K)`, then pays the valuation of `k!`.
  Merely choosing the small residue modulo `d_i^K` would not justify the
  required binomial divisibility.
* The old reciprocal index `C=B-T-1` is insufficient after amplification.
  Round14 keeps a variable positive `C`, the congruence `B | C+T+1`, and
  the additional range `B^K | binom(C,t)`. This matches the final source.
* The squared Pell frame bounds absolute values of the proposed power
  ports before those ports are known to be natural or semantically correct.
  Strictly positive seed exponents are established independently. The
  positive product auxiliary ordinate then proves `abs(U)>=2`, licensing
  removal of its old nonzero guard.
* A base-one request alone cannot orient a signed principal Pell root:
  its unwanted branch allows output `-1`. The raw digit rows first force
  `q>=2`; the `q^t` request orients the `t` pair. The recovered factorial
  numerator forces `F>=1`. For the `K` pair, the companion base
  `N+V+1>=2` excludes the sole remaining `B=1,N=-1` branch. This is the
  noncircular order used in the source.
* Factorial and binomial meanings are recovered before the CRT theorem
  is used. Their low-digit bounds derive from raw ceiling equations,
  the aggregate representative bound, and already recovered powers.
  They do not assume the binomial product currently being validated.
* The square-shell recoding acts on all numerical argument positions,
  including binder labels and schema parameters. Its bundle witness is
  rebuilt arithmetically after recoding; it is not naively recoded as
  an old formula code.
* The flow theorem uses one conclusion per rule and nonnegative rule
  multiplicities. The closure argument handles cycles and repeated
  premises; it would not be valid for arbitrary multi-conclusion rules.
* The Horn optimization preserves the complete polynomial
  `H^2*(D_b^2+G^2)`. Removing that square inside the common sum would
  permit cancellation and is not part of the construction.
* Signed monic projection and integer translation preserve integer
  existence. Their restoring maps need not be nonnegative; the sign
  conversion theorem has already been applied.

The supplied raw majorant ledger records label exponent `2959657` below
the carrier exponent `4194304`, and local exponent `5920693` below the
emitted exponent `8388608`. Round14's carrier argument therefore uses
the actual relation `E<=2*ell`, with `ell=4194304` and `E=8388608`.
This review read those finite interface values; it did not rerun every
ancestor generator or independently reconstruct the entire raw source.

## Separate review of the eleven-variable manuscript

The selected formulas in `report/eleven.tex` agree with the independently
audited construction: `I=2*r*c^2`, `S=s*r*H`,
`D_g=1+D*D_t*s^2`, root weights `(2,1,4)`, and auxiliary center `Q*V`.
The centered graph has 122 binary operations and exact degree 464; its
direct companion has 121 operations and exact degree 488.

The degree certificates have the following nonzero coefficients:

```text
[j^260 w^56 v^64 C^4 s^12 r^24 c^32 h^12] E464
  = 2^484 * 3^318 * beta^260.

[j^248 w^64 v^56 C^8 s^8 r^40 c^64] E488
  = 2^480 * 3^312 * beta^248.
```

In particular the displayed direct-degree-488 monomial has no `h` factor.
The degrees of the two displayed monomials are 464 and 488, respectively.
The current manuscript contains this corrected direct monomial; no further
formula/count mismatch was found in that read-through.
