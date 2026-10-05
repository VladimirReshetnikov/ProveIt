# An exact integer-matrix lift into strictly positive Markov masks

The new spectral report's finite Fourier core can contain an arbitrary finite family of integer matrices, with one common rational scale. This gives an exact bridge from any already specified matrix-product computation to a family of strictly positive trigonometric Markov operators. It neither supplies the matrix system's computational universality nor removes its word-selection, input or history costs. No universal operation bound is improved.

## 1. The source interface and the construction

The immutable spectral source in `docs/incoming/holder_zygmund_spectra.zip` at `e88ed8bf6b349e63c0bb3e3ab146c582275ec0d9` proves, for dilation b and a normalized nonnegative finite mask,

```
T_a e_m = sum_(b divides m+j) a_j e_((m+j)/b),
A[k,m] = a_(bk-m).
```

Here `a_j` are Fourier coefficients, `e_m(x)=exp(2*pi*i*m*x)`, and

```
(T_a f)(x) = (1/b) sum_(ell=0)^(b-1)
               a((x+ell)/b) f((x+ell)/b).
```

The mask is normalized precisely when `a_0=1` and `a_(b*j)=0` for nonzero integer j. The earlier bounded triage read the literal proof at manuscript lines368–423. This note uses only that finite identity, not the report's full spectrum or boundary-Jordan theorems.

Let `M_1,...,M_s` be any nonempty finite family of integer r-by-r matrices, r>=1. Set

```
b = 2r+1,
D = br-1,
S = max_sigma sum_(k,m=1)^r |(M_sigma)[k,m]|,
q = 2S+1.
```

For each matrix use the finite mask

```
a_sigma(x) = 1 + (2/q) sum_(k,m=1)^r
                         (M_sigma)[k,m] cos(2*pi*(bk-m)*x).       (1)
```

All frequencies `bk-m` are positive and at most D. They are distinct: an equality would give `b(k-k')=m-m'`, whose right-hand absolute value is less than b. None is divisible by b, since `1<=m<=r<b`.

Every mask is strictly positive, since

```
a_sigma(x) >= 1-2S/q = 1/q > 0.                              (2)
```

Its Fourier coefficient at each of `±(bk-m)` is `(M_sigma)[k,m]/q`, with constant coefficient1 and all others zero. Thus it satisfies the finite Markov conditions exactly. The zero family is included: then S=0, q=1, all masks are constant1.

## 2. Arbitrary matrices in the real cosine block

Define `f_v(x)=sum_(m=1)^r v_m cos(2*pi*m*x)` for a real r-vector v. Then

```
T_(a_sigma) f_v = f_(M_sigma v/q).                           (3)
```

To prove it, first consider a positive-frequency basis vector e_m. For output k in `{1,...,r}`, the Fourier rule gives the coefficient `(M_sigma)[k,m]/q`. An output at negative frequency `-k` would require a coefficient at `-(bk+m)`. Such a frequency cannot be the negative of `bk'-m'`: it would force

```
b(k'-k)=m+m',        2<=m+m'<=2r<b.
```

The constant output would require a coefficient at `-m`, but every nonzero mask frequency has magnitude at least `b-r=r+1`. Thus there is no constant or opposite-sign contribution. There are no outputs outside the r-core either: `|m+j|/b <= (r+D)/b < r+1`. Negative frequencies give the conjugate block. Taking half the sum of positive and negative characters proves (3).

In particular `span{cos(2*pi*x),...,cos(2*pi*r*x)}` is invariant and its matrix is exactly `M_sigma/q`. The sine block has the same matrix, while constants are fixed. On the full complex Fourier core the matrix is therefore, up to the order of the negative basis, the direct sum of two copies of `M_sigma/q` and the scalar1. The declared degree bound has

```
floor(D/(b-1)) = floor(r+(r-1)/(2r)) = r,
```

so it agrees with the source's guaranteed core. Some individual masks can have smaller exact degree; the common invariant r-core is still valid. No independence of the matrix entries from conjugate Fourier coefficients is assumed: the two matched blocks are required and explicitly retained.

## 3. What transfers to computation

For any finite word `w=(sigma_1,...,sigma_t)`, repeated use of (3) gives

```
T_(a_sigma_t) ... T_(a_sigma_1) f_v
       = q^(-t) f_(M_sigma_t ... M_sigma_1 v).                 (4)
```

Consequently zero-vector reachability and vanishing of any fixed linear functional are preserved exactly. The same holds for any homogeneous polynomial zero test on the coefficient vector. If an independently proved matrix system simulates a computational substrate on a specified language of admissible words, (4) transports its matrix evolution on exactly those words. This note does not construct that word language or prove a new universal simulation.

The restriction to a signed observable is essential. All these operators fix the constant function1, so the whole operator can never be the zero operator. A claim of full-operator mortality would therefore be false. Equation(4) concerns only the specified invariant block (or its chosen input), not mortality on all functions. There is no contradiction between a strictly positive averaging operator and signed cosine coordinates cancelling.

A nonzero target v also needs its scale specified: an integer matrix target u corresponds after t steps to `q^(-t) f_u`. It cannot be replaced silently by the unscaled target function. Zero and homogeneous tests avoid that issue; exact nonhomogeneous target comparisons require a duration-dependent scale.

## 4. Paid arithmetic and unresolved interfaces

The representation is an explicit finite rational Fourier list: at most `2r^2+1` nonzero entries per mask, denominator q, degree at most `2r^2+r-1`, and common dilation `2r+1`. These are finite objects compiled from the fixed matrix family. Cosine evaluation, integration, infinite-function names and exact spectral classification are not introduced as free integer primitives.

For a fixed selected matrix, direct computation of `Mv` has the sufficient ordinary straight-line bound `r^2` multiplications and `r(r-1)` additions when its integer entries and vector coordinates are supplied. Sparsity and particular constants may reduce that bound. The spectral lift preserves the same matrix-vector computation after the formal scale is removed: writing the t-th block vector as `q^(-t) z_t` gives `z_(t+1)=M_sigma z_t`. It does not reduce this arithmetic cost or furnish a cheaper evaluator.

A varying word still requires paid symbol selection and any original admissibility guards. An unbounded reachability representation still needs a fixed-arity history encoding, ordinary-input binding, integer domain/positivity conventions and a complete arithmetic ledger. No such component is supplied by the finite-core identity. The earlier computable-real critical-circle obstruction remains compatible with this rational construction: it concerns a different, exact spectral decision interface on coefficient programs.

The constructive conclusion is therefore narrow but positive: nonnegative Markov masks do not restrict their signed invariant blocks to nonnegative matrices or to the single Rvachev recurrence. An arbitrary finite integer-matrix family embeds with common finite support bounds and a common rational scale. Whether this presentation can help reduce the cost of a particular universal integer compiler remains open.

## 5. Evidence and scope

The companion fresh checks use only finite rational coefficient dictionaries and the literal Fourier rule. They test the constructed blocks, Markov normalization, support/core bounds and a two-step product for small independently selected integer matrices, including zero and negative entries. These finite checks corroborate the symbolic proof; they do not certify an unbounded compiler, whole-function numerical evaluator or imported universality theorem. No supplied, archived, committed or frozen helper is executed or imported.

The source archive SHA256 is `13ff104b4e3df02b1cd419318a4698e490911460935195cd40da18edfd2983c6`; its TeX member SHA256 is `98bc2920135319f1d9b72b14c180112fdbae39971d2cdd9698e3dc4aed4b63da`. The exact interface and predecessor reading scopes are recorded in `triage_order_free_e88ed8bf6.md` (SHA256 `1f6061b53d0a2dc1778bd3a50bf5f2f696a823368266eb197361a51b68cf559d`) and `review_new_analytic_reports_e88ed8bf6.md` (SHA256 `e3ec0f8204bd691766f7a9b190d808824e00918a2fce9cb1db51b104e3f2c9de`). They are inherited only at those stated scopes.

Fresh writer, normal and optimized-Python exact checks from `/` passed before freeze:24 matrix masks at r=1 through6,192 complete core basis images,336 two-step cosine images and separate wholly zero families at all six dimensions. The helper `markov_mask_matrix_lift_checks.py` has SHA256 `fa74fd6f5fc4519b618034fd164b1f2833268e194e03d99133064035da9c8c29`; its saved receipt `markov_mask_matrix_lift_checks.json` has SHA256 `18ed27b8f3ff2fe4ed7e32056422aa2c92a2ef3c19b6c73ac209ad9c40246c2a`. The receipt contains each finite mask and matrix. No post-freeze replay is needed or authorized by this evidence record.
