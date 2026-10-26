# Review of the free carrier and degree-separated source

The reviewed primary target is package 59's separate
[`nine_free_adjunct`](con-zfc-diophantine-forms/59-degree-separated/nine_free_adjunct/PROOF.md),
whose positive-domain circuit has **nine variables, 473 live binary operations,
and exact total degree 1,910,404**. No mathematical defect was found in its
changed source bounds, free-carrier argument, quotient transport, or positive
final witness. This is a review of the supplied mathematical proof and finite
certificates, rather than a new Lean proof of that circuit or its compiler
endpoint.

| Equation | Positive variables | Operations | Exact degree | Coefficient radix bits |
|---|---:|---:|---:|---:|
| Package 52 selected regular source | 9 | 548 | 15,502,748 | 590,069 |
| Package 56 free carrier | 9 | 560 | 4,686,812 | 1,064,921 |
| Package 59 frozen split source, derived carrier | 9 | 476 | 2,676,548 | 1,064,921 |
| Package 59 free-carrier adjunct | 9 | **473** | **1,910,404** | 1,064,921 |

The adjunct's natural-domain translation has 480 operations and the same
degree. These domain translations do not establish an unrestricted-integer
nine-variable theorem. The tuple with radix bit length 1,064,921 has maximum
port length 1,070,004; package 52's matched tuple has maximum port length
592,884. Thus the new point improves degree and arithmetic circuit size while
using larger fixed coefficients. Neither point has a global minimality claim.

## The new arithmetic tail

Free positive `C` removes the old unconditional `Q>0`. The proof repairs
exactly the lost hypothesis with

```
E0 = J*(n+(b*w)^2)+Q
   = J*n+(J-2)*(b*w)^2+3*(b*w)*C+2 > 0.
```

All Pell radicands and strict majorants are positive already at `C=1`.
The four-factor norm, or the existing purely algebraic positivity lemma,
therefore forces the normalized margin `m>0` before root integrality is used.
The identity `8*m = oldMargin` then gives `|C-K*Y|<K/2`.
Since `Y>=64`, `K>=R+P`, and `P>b*w`, this recovers
`C>2*R+1+b*w`. Thus the old nonnegative `phi` is reconstructed rather than
assumed. Conditional separation of the two radicands now applies exactly as
in the checked package-52 finalizer.

The positive input `j` is used as `j0=j-1>=0`. This retains the boundary
`j0=0` and preserves the exact quotient reparameterization. Replacing it by
unshifted positive `j0` would discard witnesses and is not justified by the
existing ratio interface. The final input is also correctly positive:
`W^2<D`, `W*C<D`, and `Q/J<=W*C` give
`W^2+Q/J<2*D<V1`, so the reconstructed `n` is strictly positive.

The generic checked finalizer can be reused with no new norm theorem.
Write the positive final input as `n=nu+1`, with `nu:Nat`, and set

```
Qstar = J*(W^2+1)+Q.
```

The literal shifted norm is then `MarginFinalizer.value ... Qstar ... nu`.
Here `Qstar>0` and `J | Qstar` iff `J | Q`. Its stronger completeness bound
`Qstar<V1` also follows from the actual registers: integrality gives
`W^2+1<=D`; also `Q<3*D`, `J<4*A`, `Tpair>=9*D`, `G>A`, and `H>=1`.
Consequently `Qstar<(4*A+3)*D<9*A*D<=V1`. What remains is the new literal
free-`C` register interface and its elementary bounds, followed by transport
to the existing `NativeNineRatio52` interface after recovering the margin.

## The split source and reduced rank

Degree separation is an exact homogeneous decomposition. The source uses
its original positive coordinates rather than expanding all `y_i=z_i+1`
inside the residuals. After two invertible row additions there are 89
weighted records. The three kernels multiply degree 0, 1, and 2 words
separately. Their finite certificate checks 22,544 same-degree interactions;
collisions between different homogeneous degrees are harmless because they
belong to different products. The coefficient identity is `2*rho_j` at each
selected target. No dummy coordinate or coefficient-dependent search is
present in the equation.

The principal new analytic obligation is positivity of the combined source
word for **all** positive `g`, before ratio soundness gives a bound. The
quadratic kernel has positive leading coefficient at degree 1929,
`Us>=B^116`, and the linear/constant kernels have degrees 2027/1719.
Their negative relative contributions are bounded by `2*M/B^18` and
`2*M/B^442`, each below `1/8`; hence `Gs>0` unconditionally. On the actual
soundness branch `g<4*b*B^116`, the proof uses `Us<6*b*B^116`, rather than
a stronger unproved two-word bound. Its estimates imply
`S+T<B^2279<=L`, including `b=1`.

Deleting the leading binary block and halving `L` changes both rank and
threshold. The new exact identity is

```
pop(R) = u+pop(T)-tau(S,T),
u+pop(T) = 2418*v-30*k-22
         = 2*(17079501+k+1201*v),
v=2134939+2*k.
```

Thus `N=2^17079501*b*B^1201` is the correct square-root threshold.
No parity restriction on `k` is introduced. At `b=1`, the low mask and
positive bounded `g` exclude a zero; completeness still has arbitrarily
large unrestricted powers of two available. The sparse signed-borrow proof
is unchanged once `|h_t|<993*M*b^2<B/4` is established.

`SelectiveQuadraticCoding` already covers the quadratic branch with
`Fin 31` and no dummy input. The smallest algebraic addition is its linear
analogue and the constant-kernel coefficient lemma, followed by addition of
the three identities. The checked `LowMaskCoding` results remain applicable. The sparse `+1`
signed-borrow argument is reusable from the manuscript, but still needs a
Lean proof: the present `SelectiveCarry` theorem uses the dense half-base
bias instead. The reduced-rank binary population identity and unconditional
split-word bounds likewise require new proofs; the old `centralCodeN` formula
cannot be substituted unchanged.

## Source binding must be explicit

The authoritative parent is `data/parent_source.json`, SHA256
`1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287`, with the
**whole original31 tuple**. A retained `source_system60.json` is an auxiliary
comparison and happens to equal the package-52 copy; that does not identify
the authoritative parent with the checked package-52 parent.

The difference is its fifteenth residual (one-based). If `q=beta*J+1` and
`C=q-F-alpha`, the original transport equation is

```
(K0+w)*C+(q-F)-z_old*(q-1)=1.
```

The package-52 normalization instead has
`(K0+w)*C=F+z_new*(q-1)`. Substitution `z_old=z_new+1` identifies the
polynomials, but positivity in the reverse direction needs `z_old>=2`.
The supplied inherited compiler argument establishes `X=w*q=2^R`,
`R>3*q`, and `F<q` on every source zero, hence `w>q>F` and
`(z_old-1)*(q-1)=(K0+w)*C-F>0`. This proves the needed boundary fact.
It is not a consequence of the transport polynomial alone for arbitrary
positive ports and coordinates.

The old tuple's full compiler adapter provides an explicit rank controller
and parity/slack promises; the finite mask hashes alone do not supply that
unbounded semantic bridge. This remains a separate formalization obligation,
as does the corresponding native calibration for the package-52 tuple.
Port-parametric algebraic results transfer after the exact transport adapter;
no fixed port should be mixed between tuples.

## Independent replay and exact degree

The extracted incoming package 56's full `verify_all.py` passed in optimized
Python in this review; the root review separately ran its ordinary mode.
For package 59, both `nine_free_adjunct/independent_review.py` and
`check_source_independent.py` passed in normal and optimized Python, with
byte-identical outputs between modes. The scripts import neither builder
nor authored main verifier. They checked 97 exact local register identities,
five universal identities, 43,945 reduced-rank binary fixtures, calibration
including `b=1`, and the actual tuple's nonzero diagonal leading coefficient.

The independently reconstructed operation ledger is 162 additions,
22 subtractions, and 289 multiplications. The exact leading coefficient is

```
2^186 * a^954792 * c^400 > 0,
```

and its residues modulo 101, 1009, and 1,000,003 are 96, 469, and 114598.
Together with the multivariate upper bound this certifies degree 1,910,404,
including the leading norm cancellation. The finite fixtures supplement the
universal proof; they do not establish consistency or replace the inherited
compiler theorem.

The recommended new nine-variable target is package 59's 473-operation
adjunct. Preserve the now-checked package-52 equation as a completed
port-parametric baseline while adding the split-source, reduced-rank, and
free-carrier bridges separately. The exact fixed coefficient binding and
refutation semantics remain explicit in either route.
