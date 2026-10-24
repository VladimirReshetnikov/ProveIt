# Closed mixed-radix reconstruction of the existing BFS tuple

The current436-symbol seed has2594 bits. Its decoder provides a636-bit
merged mask N,216 old targets packed in fixed base216, and71 exceptional
four-bit row flags E. Let ν_j be its discovery bit and
σ_j=sum_(0<=k<j)ν_k, for0<=j<=430. There are214 discoveries and216
old-target actions. Every previously discovered active target lies in
[0,σ_j]. The only exception is the halt target215: it occurs once, at
j=125 while σ_125=80. Thus radix σ_j+1 without an exception is invalid.

## Generic formulation

For0<=j<=430 define the finite product

```
P_j=product_(0<=k<j) (σ_k+2)^(1−ν_k).
```

An old active target t uses digit t; the halt uses digit σ_j+1. A new
state uses no stored digit, and its radix is one. All stored digits are
strictly below their radices. Put T=sum_(j<430) digit_j*P_j. Then
0<=T<P_430. With the same old flag stream E define the literal integer

```
A=N+2^636*(T+P_430*E).
```

From this one printed literal recover N=A mod2^636, S=floor(A/2^636),
E=floor(S/P_430), and

```
a_j=floor(S/P_j) mod(σ_j+2),
u_j=ν_j*(1+σ_j)+(1−ν_j)*(a_j+(214−σ_j)*floor(a_j/(σ_j+1))).
```

For an active old target a_j<=σ_j, the last floor is zero. For the halt,
a_j=σ_j+1 and the corrected value is215. New targets are the ordinary BFS
discovery number1+σ_j. This exactly recovers every target.

For any old position j, P_j divides P_430, and P_430/P_j is a multiple
of the actual radix. The sum of all earlier mixed-digit contributions is <P_j;
every later contribution is divisible by P_j times that radix. The term
P_430*E is also divisible by it. Thus the quotient/remainder really
extracts the intended digit. Extracting E is valid because T<P_430.
There is no recursive decoder or execution of the underlying machine.

## Two fixed-halt formulations

One can instead declare u_125=215 and, at all other positions, use

```
P_j=product_(0<=k<j) (σ_k+1)^(1−ν_k),
u_j=ν_j*(1+σ_j)+(1−ν_j)*(floor(S/P_j) mod(σ_j+1)).
```

The unused digit at125 is zero. All ordinary active old targets now use
the tighter radix σ_j+1. The same A=N+2^636*(T+P_430*E) formula packs
and recovers all fields. Alternatively omit k=125 from the product,
removing its unused factor81 and gaining another six bits, while adding
the exception to the displayed product's bound. The unused extraction at
that position is never used to define u_125. Both formulas have fixed
finite ranges and a fully printed literal; neither reads a target table.

All products are positive and at most216^216. N<2^636 and E<16^71 give
an explicit finite bound on A as well. Actual exact product, target and
packed-integer bit lengths are recorded in each FIELDS.json. The products
are computed only from the printed literal's low mask bits; the definition
of A is its explicit positional base62 numeral, so there is no circular
specification. Empty products are one.

## Entire coherent coefficients and comparison

The old flag-mask and prefix-count formulas remain unchanged; only E's
arithmetic extraction changes. The flag v_j,d_j and all430 complete
transition records are therefore exactly the current BFS records. The
checker independently constructs the BFS permutation from the complete
original transition JSON and verifies every record, including fixed
start0 and halt215.

The same explicit tile union consequently gives all943 existing compact44
tiles, including constructor(3,436,4,4). The pinned closed verifier then
reconstructs every floor rank, Phi coefficient, reciprocal K, both masks
and beta, and compares all295388 raw coefficient bytes with the current
page's coherent tuple. Its66062 basis/convolution checks, carry threshold
and three controller units also pass. There is no new numeral binding of
the polynomial: all four coefficients are exactly the existing ones.

The complete-page constant section changes only its decoder and literal.
The product, target quotient, halt rule, field extraction, entire alphabet,
seed and empty-product convention are included in the measured recipe.
The resulting target streams save221–233 packed bits, but their printed
decoder overhead is64–72 characters while their seed saving is37–39.
The total recipes are therefore26–35 characters longer. This is a finite
negative comparison for these formulations, not a lower-bound theorem
against every possible mixed-radix decoder.
