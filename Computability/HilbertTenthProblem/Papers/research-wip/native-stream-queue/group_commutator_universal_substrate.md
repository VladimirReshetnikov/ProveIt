# An ordinary-input universal substrate from group commutators

> Concrete substrate check: the [literal Tseytin table](tseytin_group_completion_obstruction.md)
> gives a universal word reduction but has trivial universal group. A direct
> invertible-matrix interpretation therefore fails; paid rewrite histories
> and compressed/existential word loaders remain separate open routes.

For every computably enumerable set `S` of positive integers, one can
compute a finite list of integer matrices generating a subgroup of
`SL(4,Z)` whose membership problem, along a fixed quadratic matrix curve
in the **ordinary input x**, is exactly membership in `S`. The finite
subgroup depends on the program enumerating `S`; the curve can be chosen
independently of that program.

This is a computational-substrate theorem. It supplies no fixed-size
Diophantine certificate for a variable-length product of the subgroup
generators, and does not improve the complete75 comparison or89 polynomial
operation bounds. In particular, an arbitrary product is not a primitive
arithmetic operation. The finite-presentation compiler below uses an
external effective embedding theorem; its enormous output has not been
materialized for a universal machine here.

The proof has four interfaces: an exact two-generator recursive
presentation, an effective finite-presentation embedding that preserves
two named letters, a finitely generated fibre-product subgroup, and a
faithful integer-matrix representation. The first three are proved below
apart from the stated external embedding theorem. The
[matrix interface and its paid input loader](group_unipotent_input_loaders.md)
are audited separately.

## 1. Exact recursive group presentation

Use the convention `[g,h]=g h g^-1 h^-1`. Define

```
a_i = b^(-i) a b^i,
r_n = [a_n,a_0],
G_S = <a,b | r_n=1 for n in S>.
```

**Claim.** For every positive integer `x`, `r_x=1` in `G_S` if and only
if `x in S`.

Here is a presentation proof that controls both implications. Let
`Gamma_S` be the graph group with generators `c_i`, one for each integer
`i`, and the relations

```
[c_i,c_j]=1 whenever |i-j| in S.
```

Translation of the indices preserves the edge relation, so
`theta(c_i)=c_(i+1)` defines an automorphism of `Gamma_S`. Form the
semidirect product `K=Gamma_S semidirect Z` with multiplication

```
(g,m)(h,n) = (g theta^(-m)(h), m+n).
```

Its subgroup `Gamma_S x {0}` embeds directly. With `b=(1,1)`,
`b^-1 (c_i,0) b=(c_(i+1),0)`. The assignment `a -> (c_0,0)` and
`b -> (1,1)` therefore defines a surjection `G_S -> K`: all relators
hold and every `c_i` is a conjugate of `c_0`.

Conversely, map `c_i -> b^(-i) a b^i` and map the stable generator to
`b` in `G_S`. The graph relations hold because, as literal free-group
identities, for `i>j` and `i<j` respectively,

```
[a_i,a_j] = b^(-j) r_(i-j) b^j,
[a_i,a_j] = b^(-i) r_(j-i)^(-1) b^i.
```

The shift relation holds as well, so this defines `K -> G_S`. The two
maps fix their indicated generating sets under composition and are
inverse isomorphisms.

If `x in S`, the word `r_x` is a defining relator. If `x>0` and
`x not in S`, the distinct vertices `c_x,c_0` have no edge between them.
Send `c_x` and `c_0` to the two generators `p,q` of a free group, and all
other `c_i` to the identity. Every graph relator maps to the identity:
the only possibly noncommuting pair would be precisely the absent edge.
This defines a retraction onto the free subgroup on those two vertices.
The image of `[c_x,c_0]` is the nonempty freely reduced word
`p q p^-1 q^-1`. Consequently `r_x` is nontrivial in `Gamma_S`, hence in
`K` and `G_S`. This proves the claim for arbitrary, including infinite,
sets `S`. The argument does not infer nontriviality from finite sampling.

The positive-input restriction matters: `r_0` is always the identity.
For a negative index `x`, the same construction detects `|x| in S`.

## 2. Effective finite presentation and named free letters

An enumerator for `S` effectively enumerates the relators `r_n` on the
two-letter generating set. Thus `G_S` is recursively presented. Higman's
embedding theorem supplies an injective homomorphism into a finitely
presented group. We use its effective form, with both a finite presentation
and words giving the generator images as outputs. A primary explicit
source is Mikaelian, [*An explicit algorithm for the Higman Embedding
Theorem*, Algorithm1.1 and Section2.1](https://arxiv.org/abs/2507.04347v8).
Algorithm1.1 also permits a two-generator finitely presented output.
The existence criterion alone is stated in [Mikaelian's modified
Higman proof, Theorem1.1](https://arxiv.org/abs/1908.10153).

Write the computed finite presentation as `H_0=<Y | R>` and the embedding
images of the original generators as the words `A_0(Y),B_0(Y)`. Adjoin
**fresh named generators** `a,b` and relations

```
a=A_0(Y),  b=B_0(Y).
```

Eliminating those fresh generators gives back `H_0`, so the resulting
finite presentation `H` still contains an isomorphic copy of `G_S`.
In particular, `r_x=1` in `H` if and only if `x in S`.

Crucially, `a,b` are now separate basis letters in the **ambient free
group** on the finite generating alphabet of this presentation. Their
images in the quotient `H` obey the defining relations, but the ambient
free group has no such relations. A later faithful representation of
that free group may therefore assign fixed free matrices to `a,b`.
Assigning those matrices directly to quotient elements of `H` would be
an invalid replacement of this step.

If the optional two-generator output of the embedding algorithm is used,
`H` has exactly four presentation generators: the two original output
letters and the fresh `a,b`. No bound on the number or lengths of the
relators is claimed. All of these finite words depend on the enumerator,
not on the varying numerical input `x`.

## 3. Fibre-product membership and a fixed conjugation

Write `H=F_N / <<R_1,...,R_m>>`, where `F_N` is free on `z_1,...,z_N`.
Define

```
M(H) = {(u,v) in F_N x F_N : u=v in H}.
```

It is a subgroup, generated by the finite list

```
(z_i,z_i),  i=1,...,N;
(1,R_j),    j=1,...,m.
```

For completeness, every listed generator lies in `M(H)`. Conversely,
if `(u,v) in M(H)`, then `u^-1 v` belongs to the normal closure of the
relators. Write it as a finite product of `g R_j^epsilon g^-1`, with
`epsilon in {1,-1}`. Each such pair has the factorization

```
(1,g R_j^epsilon g^-1)
  = (g,g) (1,R_j)^epsilon (g^-1,g^-1).
```

Multiplying these factors after `(u,u)` gives exactly `(u,v)`. This
proves the assertion without any special condition on the presentation.
It is also the introductory construction in [Bogopolski--Ventura,
*A recursive presentation for Mihailova's subgroup*, Section1](https://arxiv.org/pdf/0810.0690).
The additional concise/Peiffer-aspherical assumptions in that paper's
later Theorem1.1 concern a different, recursive-presentation result and
are not hypotheses of the finite-generation fact used here.

The straightforward target `(1,r_x)` works, but computing a whole
commutator is unnecessary. Conjugate the subgroup **once**, setting

```
M_a = (a,1) M(H) (a^-1,1).
```

This has the explicit finite generators obtained by applying that fixed
conjugation to the displayed list. Now

```
(a_x,a_x) in M_a
iff (a^-1 a_x a,a_x) in M(H)
iff a^-1 a_x a = a_x in H
iff [a_x,a]=1 in H
iff x in S.                                                    (1)
```

The first equivalence is actual subgroup conjugation in the free direct
product; the middle equivalence is equality in the quotient. This
separation retains the undecidable relation while keeping the varying
target exceptionally simple.

## 4. Faithful matrix target and ordinary input

Let `rho:F_N -> SL(2,Z)` be a faithful representation assigning matrices
`B` and `A` to the named basis letters `b` and `a`. The componentwise map

```
(u,v) -> diag(rho(u),rho(v))
```

is faithful into `SL(4,Z)`. Let `K_S` be the image of `M_a`. Equation(1)
becomes

```
x in S iff diag(L(x),L(x)) in K_S,
L(x)=B^(-x) A B^x.                                              (2)
```

The subgroup's finite generator matrices and their inverses are integer
matrices, computable from the finite presentation. Include those inverses
in a finite alphabet if membership is to mean a finite **positive word**
in the alphabet. An empty word may be permitted; it does not alter (2).
This conversion does not remove the need to certify an arbitrarily long
selected word.

A faithful representation with a unipotent `B` makes (2) a quadratic
polynomial curve. Its elementary free-group proof and the exact scalar
DAG are supplied by the matrix-loader companion packet. For example,
one uniform choice for arbitrary finite rank is

```
U = [[1,4],[0,1]],  B = [[1,0],[1,1]],
a -> U B U^-1 = [[5,-16],[1,-3]],
b -> B,
remaining basis letters -> distinct U^i B U^(-i), i>=2.
```

Then, putting `t=4x-1`,

```
L(x) = [[1-4t,-16],[t^2,1+4t]].
```

The six binary operations `4*x`, `4*x-1`, `t*t`, `4*t`, `1-4*t`,
and `1+4*t` evaluate all entries. More precisely the computed registers
are reused, so the count is **6=3M+3A**, without witnesses. Duplication
into the two diagonal blocks and loading zero or fixed entries cost no
arithmetic operations. Every numeral multiplication has been charged.
The target is independent of `S`; only the subgroup changes.

Using the two-generator finite output in Section2 permits the fixed
four-generator free embedding with basis images

```
a -> U^3, b -> B, z_1 -> U B U^-1, z_2 -> U^2 B U^-2.
```

The companion proves their freeness through the index-three subgroup
of the free group on `U,B`. In this choice `A=[[1,12],[0,1]]` and

```
L_5(x) = [[1+12x,12],[-12x^2,1-12x]].
```

Compute `q=12*x`, `r=q*x`, `s=0-r`, `1+q`, and `1-q`. This is
**5=2M+3A** with no witnesses and only nonnegative literal numerals.
The intermediate lower entry is signed, as allowed for a computed
integer-matrix coordinate. An alternative schedule has3M+2A using the
fixed signed numeral-12. Thus the same fixed curve
`diag(L_5(x),L_5(x))`, independently of `S`, works for every computably
enumerable positive set after applying the stated effective
two-generator embedding. More generally the companion gives the same
five-operation bound with coefficient `4(N-1)` for an arbitrary
presentation rank `N>=2`. Neither count includes membership
certification.

An equally faithful choice improves the program-prefix composition below.
Conjugate the preceding free matrices by `S=[[0,1],[1,0]]` and interchange
the named basis letters `a,b`. Conjugation by this integer invertible
matrix preserves SL2 and freeness, even though `det S=-1`. With

```
U_*=[[1,1],[0,1]], V_*=[[1,0],[4,1]],
a -> U_*, b -> V_*^3,
z_1 -> V_* U_* V_*^-1, z_2 -> V_*^2 U_* V_*^-2,
```

the new `A=[[1,1],[0,1]]`, `B=[[1,0],[12,1]]` give

```
L_*(x) = [[1+12x,1],[-(12x)^2,1-12x]].
```

The scalar schedule is `q=12*x`, `r=q*q`, `s=0-r`, `1+q`, `1-q`:
again **5=2M+3A**, with no negative literal numerals. Choosing this
representation in (2) changes only the fixed subgroup generator matrices.

The [affine-input obstruction](group_affine_input_obstruction.md) shows
that degree two is necessary for this paired-SL2 subgroup interface.
Even two independent affine SL2 blocks have a subgroup-membership
preimage that is empty or a coset of a subgroup of the integers. This
does not imply an arithmetic-operation lower bound and does not extend
to arbitrary affine SL3 or SL4 curves.

## 5. Universality, evidence, and remaining arithmetic work

Choosing a universal computably enumerable set `S` gives a fixed finite
matrix alphabet that recognizes it via ordinary positive input and
(2). More strongly, the construction works effectively for every such
`S`. This is a reduction with a prescribed algebraic input curve, rather
than an inference from the bare undecidability of matrix membership.
It uses recursive enumerability and group embedding; it does not appeal
to a prior Diophantine representation of `S`.

There is also a useful version with **one subgroup and one finite matrix
alphabet for all programs**. Fix an effective enumeration `S_p`, `p>=0`,
of the computably enumerable subsets of the positive integers, and set

```
U = {2^p (2x+1) : p>=0 and x in S_p}.
```

Dovetailing the enumerators proves that `U` is computably enumerable.
For positive `x`, the integer `2^p(2x+1)` has exact two-adic valuation
`p`. Thus equality of two such codes first forces the same `p`, then
the same `x`. Construct `K_U` just once by the preceding theorem. For
program `p`, precompute the two positive numerals

```
kappa_p=2^(p+1), lambda_p=2^p.
```

Then, with `y=kappa_p*x+lambda_p`,

```
x in S_p iff y in U
         iff diag(L_*(y),L_*(y)) in K_U.                       (3)
```

The numerical argument is still the original ordinary positive integer
`x`. Fold the fixed coefficient into the two program numerals,
`alpha_p=12*kappa_p`, `beta_p=12*lambda_p`. The six scalar instructions are

```
t=alpha_p*x, q=t+beta_p, r=q*q, s=0-r, u=1+q, v=1-q.
```

The target consists of two copies of `[[u,1],[s,v]]`. Thus full
program/input loading costs **6=2M+4A**, with no supplied witnesses,
and every subgroup generator is independent of both `p` and `x`.
The program numerals are computed when fixing the program, just as in
the existing complete75 compiler. The circuit does not compute an
exponentiation on a varying program coordinate. The companion audits
this composed loader, together with the earlier seven-operation
composition through `L_5` as a reference.

The companion [checker](group_commutator_universal_substrate.py) and
[receipt](group_commutator_universal_substrate.json) check literal
free-word identities, finite graph/retraction instances and constructed
fibre-product factorizations. Those tests neither execute the general
Higman compiler nor establish the universal theorem by enumeration.
The parametric argument above and the named external theorem provide
those logical steps. The matrix companion separately verifies the
polynomial identities, determinant and operation ledger. These are
mathematical proofs and exact audits, not Lean formalizations.

To turn this substrate into a competitive Diophantine equation, one still
needs a uniformly bounded set of positive integer witnesses certifying
that the target is a product of an arbitrary finite sequence of the fixed
generator matrices. A word length bound, a chosen-word digit stream,
matrix-product recurrence or tree of merges is not free. A construction
must pay for selection, order, length, signs and ordinary arithmetic,
and prove both soundness and completeness for the full unbounded
history. The quadratic loader solves the input issue only. No size
claim for that missing certificate follows from this packet.
