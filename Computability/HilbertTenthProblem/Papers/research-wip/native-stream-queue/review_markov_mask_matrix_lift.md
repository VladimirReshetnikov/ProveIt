# Independent proof review: integer matrices in positive Markov masks

**PASS; no correction requested.** I read the full final `markov_mask_matrix_lift.md` and independently challenged the construction, frequency separation, positivity, product transfer, zero-family boundary and arithmetic scope. This is a proof-only review. The supplied checker and receipt were hash-authenticated but were not executed, imported or audited as programs; their finite-case counts remain author evidence.

Frozen author pins:

- `markov_mask_matrix_lift.md`: `5dca0ea91dc1d05b7e1a784e2933a67c059e99f3db0dad74f8491849345e69e6`.
- `markov_mask_matrix_lift_checks.py`: `fa74fd6f5fc4519b618034fd164b1f2833268e194e03d99133064035da9c8c29`.
- `markov_mask_matrix_lift_checks.json`: `18ed27b8f3ff2fe4ed7e32056422aa2c92a2ef3c19b6c73ac209ad9c40246c2a`.

The inherited literal Fourier interface was read at lines 368–423 of `holder_zygmund_spectra/holder_zygmund_spectra.tex`, member SHA-256 `98bc2920135319f1d9b72b14c180112fdbae39971d2cdd9698e3dc4aed4b63da`, in `docs/incoming/holder_zygmund_spectra.zip` at commit `e88ed8bf6b349e63c0bb3e3ab146c582275ec0d9`, archive SHA-256 `13ff104b4e3df02b1cd419318a4698e490911460935195cd40da18edfd2983c6`. My preceding bounded triage records that source read and byte authentication: `triage_order_free_e88ed8bf6.md`, SHA-256 `1f6061b53d0a2dc1778bd3a50bf5f2f696a823368266eb197361a51b68cf559d`. No infinite-dimensional spectral theorem is needed for this lift, and none is newly certified here.

## Algebra and domain

For r≥1, set b=2r+1, D=br−1, S=max over the finite nonempty matrix family of the sum of absolute entries, and q=2S+1. The frequencies bk−m, 1≤k,m≤r, lie in [r+1,D]. Equality of two frequencies forces b(k−k')=m−m'; the right side has absolute value below b, so both indices agree. None is a nonzero multiple of b. The mask therefore has exactly the claimed rational coefficients at the distinct positive/negative frequencies and constant coefficient one. Its lower bound is 1−2S/q=1/q>0 for every real x, and the finite Markov normalization follows. If every matrix vanishes, S=0, q=1 and the constant masks remain strictly positive and normalized.

For a positive input character e_m, the desired output coefficient at e_k is M[k,m]/q. A negative output e_(−k) would require a frequency −(bk+m), equal to some −(bk'−m'); that forces b(k'−k)=m+m' between 2 and 2r=b−1, impossible. Constant leakage is excluded because mask frequencies have absolute value at least r+1. All remaining outputs satisfy |(m+j)/b|≤(r+D)/b<r+1, so there are no frequencies outside the declared core. The constant character is fixed by normalization. The negative-frequency block is the matching conjugate block; taking sums or differences of characters yields identical M/q blocks on real cosines and sines. In increasing negative-frequency order the matrix is permutation-conjugate to M/q, as the author correctly qualifies.

The common degree bound gives floor(D/(b−1))=r, including r=1. Individual masks with zero extreme coefficients, including constant masks, may have smaller exact degree; that does not invalidate the common invariant core. Strict positivity of the mask places no entrywise positivity requirement on its signed cosine block.

## Products, observables and cost

Induction gives the stated product order:

    T_(a_sigma_t) ... T_(a_sigma_1) f_v
       = q^(−t) f_(M_sigma_t ... M_sigma_1 v).

The cosine characters are linearly independent, and q is nonzero. Hence zero-vector reachability transfers in both directions. A homogeneous polynomial test of degree h acquires only the nonzero factor q^(−th), so its zero set also transfers; fixed linear tests are a special case. A nonzero target u instead requires the target function q^(−t)f_u. Omitting the duration scale would change the problem. Every full operator fixes 1, so neither it nor any finite product is the zero operator. The theorem correctly concerns the chosen signed invariant block, not full-operator mortality. These statements also cover the empty word and wholly zero families.

For a fixed selected r-by-r matrix with supplied entries, r² multiplications and r(r−1) additions are a valid sufficient direct matrix-vector bound, not a minimum. The lift does not turn evaluating trigonometric functions, integration, coefficient extraction or rational normalization into free integer operations. Writing the block at time t as q^(−t)z_t recovers the original integer evolution z_(t+1)=M_sigma z_t and its original costs. The mask description bounds—at most 2r²+1 nonzero Fourier entries, degree at most 2r²+r−1 and dilation 2r+1—are correct finite representation bounds, not a complete compiler ledger.

A computational interpretation still needs an independently established matrix system, admissible-word selection, ordinary-input binding, output predicates and a charged fixed-arity history mechanism. None is constructed by this note. The positive conclusion is the exact transfer of an arbitrary finite integer-matrix family into strictly positive Markov masks with a common rational scale. It neither establishes universal simulation nor improves an operation bound. It is consistent with the earlier obstruction for exact spectral decisions on arbitrary computable-real coefficient programs, which is a different interface.

No supplied, archived, predecessor or frozen program was executed or imported. No repository or Git mutation occurred. The root author's small rational checks corroborate the proof but are not the basis for these all-size conclusions.
