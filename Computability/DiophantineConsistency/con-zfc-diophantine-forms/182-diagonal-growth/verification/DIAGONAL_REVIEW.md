# Independent review of the 214-integer diagonal-power quartic

**Result: the new local mathematical reduction and its literal coefficient
implementation pass this review, conditional on the identified inherited
C222/Pell/refutation calibration.** The result is an ordinary proof using
those inherited theorems. This review is not an end-to-end proof-assistant
build, external human peer review, or a proof of consistency.

The independently inspected equation has SHA-256
`7ffda8ff6f609918dc3d1824a28ff7188ec8c3ea2be83abb1e4bc5d465fd7894`.
Its principal parent has SHA-256
`8d919a1e5d6a802765b6d010c0140fb1d83c3d36d211b209b7a8d2fb3f3fb6f6`,
the 215-integer equation in ProveIt package 173 at commit
`02a78a08603cbae248c19c23a75907c6c6bd6443`.

## Scope and inspected material

I read the complete new producer `direct/build_diagonal.py`, its
exact source delta, the principal parent residuals and variable metadata,
the parent's C-anchor and label-separation arguments, and the relevant full
sections of package 173's report. I also read source 170's earlier diagonal
growth proof. The verification program supplied with this review imports
none of the producer's code: it reconstructs all five edited rows, the
complete square frame, and every coefficient of the collected quartic.
Its separate positive-expression evaluator transcribes the nine C222
constructors and computes the exact diagonal label bound.

The five altered rows are 96,97,128,130,152; row 153 and coordinate 214
are deleted. Every other coefficient in every retained residual is identical
to the authenticated parent. The new equation has 214 unrestricted integer
variables, 153 quadratic residuals, 1,040 residual monomials, and 5,656 collected
quartic monomials. Its exact degree is 4, residual height 464, and collected
polynomial height 219813. Every variable occurs.

## The mathematical change

In the parent's final chart let t=x0,F=x2,K=x93,A=x132. The old
relations were

```
t=128+4z^2,  T2=t^2,  K=T2^2,  F=t^K.
```

The replacement is

```
c=464,  t=c+z^2,  K=c*t^2,  F=K^K.
```

The final equality is the interpretation of the retained polynomial Pell
power certificate; no variable-exponent operation occurs in the final
polynomial. The existing K-index pair is reused with base K. The square
frame now contains K in both its base and index roles. This removes one
quadratic wire and its defining row. It is a new arithmetic construction;
no pointwise equality or zero-preserving map with the old t^K polynomial
is asserted.

## Exact label growth

Let J(a,b,c,d) be the source sum of the nine axiom labels together with
a,b,I(a,b),A(a,b),1. All coefficients of this polynomial are nonnegative.
The independently computed axiom degree vector is

```
16,8,8,8,8,32,16,8,524288.
```

Thus the exact degree of the diagonal polynomial J(u,u,u,u), abbreviated
J(u), is 524288. For c=464 and D=3c^2=645888 the exact integer evaluation
gives

```
bit_length(J(464))=5692913,
bit_length(464^645888)=5721264.
```

The first bit length is smaller, so J(464)<464^645888. The full evaluated
J(464), encoded as minimal unsigned big-endian bytes, has SHA-256
`b6cdb458ca0dcfc1ae23a3cb3bfad0a6cbe9729c77e176605506939900140dd4`.

This one finite inequality proves the unbounded bound needed here. Write
J(u)=sum a_j*u^j with a_j>=0 and j<=D. For integers t>=c,
c^D*t^j<=t^D*c^j. Sum these inequalities and use J(c)<c^D to obtain

```
J(t)<t^D.
```

Every permitted local parameter is in [0,t-1], so positivity of the
coefficients gives J(a,b,c,d)<=J(t,t,t,t)<t^D. The exact diagonal check
therefore supplies a uniform bound, not just empirical growth evidence.

For integers t>=c>=3, c^t>=t^c. One elementary proof starts with equality
at t=c and notes that (1+1/n)^n<3<=c for every n>=c; this follows from
the binomial expansion bounded by sum(1/j!)<3. Multiplying the induction
hypothesis by c then advances from n to n+1. Consequently

```
(c*t^2)^(c*t^2)
 = c^(c*t^2)*t^(2*c*t^2)
 >= t^(c^2*t)*t^(2*c^2*t)
 = t^(D*t).
```

The inherited sharp separation lemma therefore applies with L=t^D:
every local label is at most L, and F>=L^t. Its proof first recovers the
equal factor counts, then uses positive elementary symmetric coefficients
to retain the strict difference bound even when F=L^t. The unchanged
Horn-flow argument handles repeated premises and cycles.

## Power request, frame, and optimized chart

The new first power request is exactly

```
T_K=2*A*K-K^2-1,
F-K*Y_K+T_K*quotient-(X_K-A*Y_K)=0.
```

These are rows96 and97 with base t replaced by K. The same canonical
K-index Pell pair remains in rows 126, 127; its K term remains in the pooled
orientation row 141, and its ordinate remains in the cap row 144. Thus
neither the index authentication nor its orientation has been removed.

I independently reconstructed all 35 actual square-frame atoms. Row 128 is
precisely W-2 minus their squared sum. Replacing one old base occurrence
of t by K changes the row by +t^2-K^2. Its old K-index occurrence remains,
so the K^2 coefficient becomes-2. This checks the whole frame, including
the aliases and translated actual representatives, rather than inferring
its correctness from the changed coefficient alone.

The final optimized chart preserves the local semantic interface. The
power divisor coordinate 139 occurs only in rows 96, 97; its quotient 140
occurs only in 97. Their displayed shapes identify exactly the isolated
power certificate. The deleted coordinate 214 occurs only in the two
old growth-definition rows 152, 153. The horizon root 185 occurs only in 130.
All other retained rows, including every C222 local row, normalized
remainder, binomial range, CRT index condition, and pooled power block,
are byte-for-byte coefficient-identical to the parent. No hidden
dependence on an eliminated growth coordinate or horizon root is left.

The proof nevertheless re-establishes soundness and completeness at the
semantic interface; a hash or this occurrence audit alone would not prove
the inherited unbounded arithmetic theorem.

## Parity, sign recovery, and binomial coverage

The new horizon can be odd. This causes no gap: K=464t^2 is always even,
and the first authenticated power has positive nonunit base K. It gives
F=K^K>0 and

```
v2(F)=K*v2(K)>=K>2*t.
```

This supplies every old use of the even growth value:

* The actual index C is even, so B divides the odd integer C+F+1 and
  B cannot vanish. The self-radix multiplier H is still2 modulo4, so
  the first radix power has |BH|>=2.
* The unchanged beta endpoints exclude exponent x=0. The q block then
  recovers y>=F; the endpoints give x>=F+1 and x>=2+(t+1)y. In
  particular |q| is already large before the q+1 block is interpreted.
* The new F is at least t^t, so all former lower growth estimates,
  local-polynomial bounds, and strict binomial-remainder estimates
  remain valid.
* For 1<=i<=t, v2(F+i)=v2(i); hence binomial(F+t,t) is odd.
* Since v2(F)>v2(t!), multiplying F by a sufficiently large odd multiple
  of the odd part of t! supplies y with t! dividing y, as required by
  the beta CRT construction.

Source170 used an even-t prime-count argument for its weaker radius
F=t^t. That particular proof must not be imported unchanged. Here the
much stronger growth makes the parity-free elementary estimate sufficient:

```
lcm(1,...,t)^2 <= (t!)^2 <= t^(2*t) <= F.
```

Thus both directions of the retained generalized binomial-selector theorem
hold, including coverage at every full prime power of B. No assertion that
F itself is a factorial or is divisible by every integer up to t is used.

## Completeness and the cofinal C anchor

Given a finite C222 refutation, the horizons 464+z^2 are cofinal; truth
steps pad it to any chosen sufficiently large horizon. Fix t,K,F and the
finite pending-state products first. Choose the odd beta multiplier and
cofinal beta code x exactly as before. This fixes B,N and the CRT moduli
before the actual representative C is selected.

Because N^2 is odd, each prescribed class has cofinally many positive
even representatives. Choose the other eight representatives first, then
choose C even and greater than all other requested indices, including K.
Only afterwards define H,q and the actual square frame. This order is
acyclic. Enlarging C cannot alter B,N or any previously fixed CRT
modulus, and it strengthens the self-sized radix estimates.

The canonical C-index Pell ordinate again dominates the retained finite
sum, and its even-index parity gives the same odd auxiliary quotient.
All remainder slacks have the same nonnegative ternary representations.
This supplies every private witness of the changed source. Conversely
the common frame, anchor, signed power argument, range recovery,
new label bound, and retained Horn-flow extraction give a finite
refutation from every integer zero.

The named inherited C222/ZF/ZFC refutation calibration then yields the
stated ZFC-provable equivalence after negating the existence statement.
Neither direction assumes Con(ZFC).

## Prior work and limits

The general diagonal growth idea F=t^t already appears in source 170.
The C-index semantic anchor and sharp finite-product separation come from
source 173. These are prior ingredients, not new claims. The contribution
reviewed here is their precise combination with the independently bounded
large source labels, quadratic diagonal index K=464t^2, and the literal
214-integer low-height endpoint.

Against source 173's principal 215 equation this removes one variable and
one residual, with polynomial height increasing from 91679 to 219813.
Against its 214-variable companion, it sharply lowers height from
1099511627852 while using 170 more monomials (5656 versus5486).
The repository also has a 213-variable quartic with much larger height.
Therefore this is a concrete tradeoff, not a general minimum-variable
record or a proof of global simplicity.

The separate compact experiment in this review session was rejected as
noncompetitive: source 59 already has stronger operation/degree tradeoffs,
and sources 74/81 already use the proposed Pell centerings. It is not
counted as a new result.
