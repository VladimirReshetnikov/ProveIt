# Independent source and uniform-degree review of the 85-operation polynomial

**PASS; no source correction requested.** The [author construction](complete85_auxiliary_bezout_projection.md) emits a complete universal polynomial in **85=48M+37A operations**, with **18 positive witnesses** and **exact degree175** on its inherited valid fixed-program slices. This review independently checks the saved arithmetic, the full off-zero correction and the degree. The positive-zero proof is also examined separately in the [mathematical review](review_complete85_auxiliary_bezout_math.md).

The [checker](review_complete85_auxiliary_bezout_source.py) reads frozen JSON and imports no author or historical Python. The [receipt](review_complete85_auxiliary_bezout_source.json) authenticates the author trio, the immediate parent trio and all twelve declared proof/source dependencies. Existing mismatched files fail authentication. This is a bounded audit of the actual saved source, not an independent execution audit of every author API branch or a formal proof in Lean.

## Complete instruction reconstruction

Starting from the literal normalized transport-shear86 parent, the reviewer reconstructs the expected definitions independently. It removes the supplied coordinates o,j, supplies `auxiliary_quotient=T`, replaces the two-gate `V=of-c` construction by

```
Tf=T*f; Tf_minus_one=Tf-1;
cbase=c*Tf_minus_one; Rf2=R*f²;
V=cbase-Rf2,
```

and removes the three gates of the coupled linear factor plus its final multiplication. The existing paid `f²` is reused. The final subtraction of1 consumes the full remaining seven-factor product. Each actual definition, all retained free coordinates, fixed numerals, witness names and the ordinary input must match this independent reconstruction. All85 rows and all declared input leaves are live. The exact count is48 multiplications and37 additions/subtractions; the parent has one more addition. The two removed supplied coordinates have no consumers outside the proved cones.

There are79 unchanged old instructions, five new instructions and the changed final subtraction. The first, main, input, auxiliary, index, transport and strong factors all remain. In particular there is no unpaid power, comparison, positive-domain guard or input conversion in the count.

## Exact correction, including both finalizers

Write c,f,i,R,Delta for the actual computed/supplied ports, and K for `index_difference`. The reviewer expands independent integer-coefficient polynomials for

```
o=cT-Rf,
j=Tf-R*Delta*i²*c³-1,
Ns=f²-Delta*i²*c⁴, Nk=K-R.
```

It proves `of-c=V` and

```
V-jc+K = Nk+R*(1-Ns).
```

The retained instruction identities and private consumer checks extend the proved V substitution through every remaining factor. The checker separately expands both actual source finalizers at their complete factor ports. Their exact all-value relation is

```
Fparent(restored)+1 = (Fchild+1)*(Nk+R*(1-Ns)).
```

The reviewer also checks the divisibility correction

```
of+R = c*(j+1)+R*(1-Ns).
```

These are polynomial identities over every commutative ring. They do not imply equality of the two polynomials on unchanged tuples, nor positivity of the restored o,j on arbitrary positive data. The mathematical proof must first recover Ns=Nk=1 and the two positive coordinates. It does so before invoking parent universality.

Twenty-four complete source evaluations, including eight rational assignments, independently check the correction and168 retained-factor values. These are off-zero algebra checks, not numerical halting witnesses.

## Uniform exact degree, with fixed numerals kept symbolic

Every supplied witness and ordinary input has degree1; the six fixed-program numeral ports have degree0. The checker guards the literal main/input norm cones and proves the all-value cancellation

```
(X+a*c+gamma)²-(a²+H)c²
 = (X+gamma)*(X+gamma+2a*c)-H*c².
```

It then propagates homogeneous leading polynomials with exact integer coefficients, retaining all six numeral ports symbolically. The seven attained factor degrees are22,18,32,60,7,2,34. Their sum is175. The uncorrected graph bound185 is recorded separately.

Put `Q=(B-1)J`, `k0=eta+zeta`, `g0=rho+sigma`, and

```
C1=Q-F-Z-alpha-twice_cell_bits*x,
Ttransport=w*C1-transport_quotient*Q.
```

The entire top form is independently expanded into168 integer-coefficient monomials and agrees exactly with

```
32*Q^103*h*g0*delta²*i⁴*k0^13*w^16*s^29
   *Ttransport*T²*f².
```

This proves uniform attainment, rather than inferring it from numerical specializations: on every admissible fixed-program slice B-1 is positive, and Ttransport has the nonzero coefficient `-(B-1)` at `transport_quotient*J`. The other displayed factors are nonzero polynomials in independent retained supplied coordinates. No equality holding only at zeros is used to lower the formal degree.

## Scope and replay

The source review supports the literal85 ledger,18-witness interface, exact full correction and uniform exact degree175. The source and mathematical reviews together support the author's full positive-zero bijection to the established universal86 parent, with its unchanged valid fixed-program numeral recipe. No enormous complete Pell tuple is materialized. The theorem is not an unrestricted circuit optimum, a numerical universal matrix table, or a whole-positive-orthant coordinate bijection.

Checker SHA-256: `8c3095f10067bfd5bebfd86914698add2871f8b3b5b4005d284db6840a4eda69`.
Receipt SHA-256: `6d746da58a1a0bc116db453bad4767f50fe8841485abb7c0bc29b650ac3f635c`.

```
python3 /absolute/path/review_complete85_auxiliary_bezout_source.py \
  --root /absolute/path/native-stream-queue \
  --expect /absolute/path/review_complete85_auxiliary_bezout_source.json
```

The writer and a fresh exact typed replay from `/` pass. `--author-root` may point to a separate directory containing the frozen author trio; it defaults to `--root`. Optimized Python is rejected. Only the new checker runs; no historical builder or verification suite is repeated.
