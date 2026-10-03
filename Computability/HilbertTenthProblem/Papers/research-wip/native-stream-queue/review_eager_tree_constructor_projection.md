# Independent review of the finite eager Tree constructor projection

**PASS; no correction requested.** The source removes exactly the five supplied constructor fields per row, preserves the full polynomial on their restoration graph, and gives a bijection of natural zero fibers with the frozen triangular parent. All constructor arithmetic remains paid. The complete saving is `15N` operations, while exact degree rises from four to ten.

I read the full frozen [author source](eager_tree_constructor_projection.py) and [note](eager_tree_constructor_projection.md), the actual triangular source/proof, the occurrence-flow parent, and the relevant corrected original kernel. The [independent checker](review_eager_tree_constructor_projection.py) and [receipt](review_eager_tree_constructor_projection.json) authenticate the author trio, both parent trios and the placed kernel. It uses its own coefficient arithmetic, graph restoration, degree calculation, source inspection and bounded eager evaluator. No author verification routine or historical broad suite is run.

## Exact graph and domain

In each row the removed fields are

```
d=F(a,b), e=F(a,y), q=F(0,b), j=F(2a+1,b), k=F(d,c),
F(u,v)=(u+v)(u+v+1)+2v+2.
```

These definitions are unconditional in the actual parent. They have a triangular dependency order: k uses the already restored d. For every retained natural tuple, each right side is a natural number, indeed at least two. No tag selection, pointer condition or polynomial-zero hypothesis is needed. The resulting map uniquely restores all five fields, without changing any retained coordinate or external parameter.

The implementation aliases each field to its existing paid right-side register and then removes the private defining subtraction and its residual. In the k computation it substitutes d's existing register. The symbolic audit checks the complete parent after this restoration against the complete child: every deleted definition is the zero polynomial, every retained residual agrees, and both literal paid finalizers give the same full polynomial. This identity holds over arbitrary commutative rings.

At a natural child zero, restoration remains natural and the full identity supplies a parent zero. At a parent natural zero, the sum of squares forces each constructor definition, so coordinate deletion and restoration are inverse. This is a bijection with the **entire triangular parent's natural zero fibers** at the same N. It is stronger than the earlier root-normalization slice statement, because the constructor values are already uniquely forced in every parent zero.

Composition with the triangular theorem preserves represented triples of the original finite height/flow certificates. It does not create a bijection with all their unnormalized witnesses. N remains external; there is no new fixed-arity universal bound, ordinary-input decoder or uniqueness claim for complete computation certificates. Signed and rational checks here are algebraic; no computation theorem outside the natural domain is added.

## Independent complete-source identities

For both cleanup schedules and every `N=1,...,8`, the checker reconstructs the actual parent and child and compares them to their authenticated saved full packets. It verifies the exact free-coordinate difference, the 5N removed definitions, and the full paid SOS tail. Independent multivariate coefficient dictionaries establish:

- 16 whole-polynomial graph identities;
- 1,272 retained residual identities;
- 360 identically zero restored definition rows;
- 16 exact complete degree certificates.

The audit separately reconstructs the handwritten constructor graph rather than deriving it from the author's alias table. Ninety-six rational full-source evaluations supplement the coefficient proofs. Every emitted gate and supplied field is live and source operands are closed, typed and acyclic.

## Paid counts and exact degree

Only the 5N defining subtraction gates disappear from the certificate. Its multiplication count stays unchanged. The finalizer has 5N fewer squares and 5N fewer additions, so the complete saving is exactly

```
5N multiplications + 10N additions = 15N operations.
```

The old right-side arithmetic is neither deleted nor duplicated. The independent recount verifies both the literal parent differences and the formulas

```
witnesses = (3N^2+23N)/2,
residuals = 17N+3,
M = (9N^2+91N+6)/2,
A = 6N^2+(51-cleanup)N+17,
operations = (21N^2+193N+40)/2-cleanup*N.
```

Here cleanup is zero or one and refers only to the inherited static `0+b` simplifications. The projection itself saves 15N in either schedule. At N=1 the full totals are 127 and 126; at N=8 they are 1,464 and 1,456. All 16 emitted complete sources together contain 11,516 live paid gates.

Restored d,e,q,j have degree two. Restored k has degree four and highest part `(a+b)^4`. In the retained local input-constructor equation, multiplication by t4 produces highest part `-t4*(a+b)^4`, of degree five. Every other retained residual has degree at most three. The entire degree-ten homogeneous part is therefore

```
sum_i t[i,4]^2*(a[i]+b[i])^8.
```

The independent full expansion matches this entire polynomial, not only a numerical leading coefficient. Its coefficient of `r0_t4^2*r0_a^8` is one. This proves exact degree ten uniformly for all N>=1 and both schedules. In particular, N=1 does not reduce formal degree by using separate zero equations that force recursive tags to vanish on its natural zero set.

## Natural fixtures and guarded APIs

An independent bounded five-rule eager evaluator and row constructor provide 11 genuine applications. A separate DFS orders the resulting shared premise DAG strictly forward, and each certificate receives zero, one or two dummy rows. In both schedules these give 66 complete natural zero-bijection checks: actual parent and child outputs, exact projection and exact restoration. All five root rules occur. These tests do not use the author's evaluator or triangular normalizer to construct the fixtures.

Forty-eight additional arbitrary natural assignments test the stronger assertion that restoration is natural even away from zero; every removed field is at least two. The public project function rejects nonzero parent assignments rather than silently treating them as valid certificates.

The checker exercises 74 malformed-call rejections, six packet-copy checks, explicit signed polynomial evaluation/restoration, and all seven warmed source/proof/receipt/kernel pin mutations. A preloaded fake kernel module is replaced by authenticated source during the build and the exact caller module object is restored. Optimized Python is rejected. Unlike the older root-only projection's narrower companion-pin boundary, this constructor module authenticates all six parent artifacts and the kernel on every public build or check; the tests verify that stronger contract.

No general protection against a caller modifying Python module globals or the interpreter itself is claimed. The advertised complete canonical packet, assignment, copy and provenance contracts are the audited boundary.

## Reproduction and frozen inputs

```
python review_eager_tree_constructor_projection.py \
  --repo /path/to/Proofs \
  --root /path/to/frozen-parent-trios \
  --subject-root /path/to/constructor-author-trio \
  --expect review_eager_tree_constructor_projection.json
```

`--output FILE` writes a deterministic receipt. The standard-library checker records its own source hash and all input hashes. It makes only private temporary pin-mutation fixtures, with no repository or Git changes.

Frozen author source: `a4c09cc720ac0d5b7f884e8636900a93ba6c17a7040a0f01c83b94f6f469bc81`.

Frozen author receipt: `26bf1f948751f94e77e5716fddc0668c8d8c910bcb2ac6237b50ece7a9090852`.

Frozen author note: `c5a65687c3756f220e11210525e9bc6ce7968ec2def7348a9dcf5d2cb69d8fc7`.
