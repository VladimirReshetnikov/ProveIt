# Independent ordinary review: ten-positive quadratic projection

**The new unbounded arithmetic argument is sound.** I read the entire
`ten-positive-quadratic-projection/PROOF.md` against the frozen
`ten-positive-scaled-norm-reuse/source/original-proof.md`, particularly
its Sections 3--6 and 8. I found no missing main-Pell assumption in the
three-root recovery, the transport bootstrap or the new height argument.
This review does not certify the separately produced 106-gate literal
artifact. Its count, binding and complete circuit/degree receipts remain
the producer's independent-check obligation.

## The omitted root is recovered before it is used

For f=chi_A(m), the unit alpha^(2m) has coordinates
2f^2-1 and 2f*psi_A(m), hence equals -1 modulo f in the integer
quadratic ring. Consequently signed integer indices reduce modulo 2m
with an overall sign. Reflection t->2m-t preserves the psi coordinate
modulo f. This gives an index p in [0,m] independently of whether the
original auxiliary index is huge or negative.

The positive auxiliary Pell pair is (S*abs(V),y). Its index must be odd:
an even chi_S coordinate is plus or minus one modulo S, whereas S>=2
divides this coordinate. The polynomial odd-index identity and
S^2=1-A^2 modulo f then give psi_A(v)=plus or minus c modulo f.
Folding bounds psi_A(p) by I. Since f>2I and 0<c<=I, the negative
residue cannot occur, and the positive residue cannot wrap. Thus
c=psi_A(p), p>=1, with no input main-Pell radical or circular rank
assumption. Here c<=I follows directly from I=i*mu*c^2 and positive
inputs. The proof handles both signs of the initial V.

The three retained radicals have the inherited strict separation, so
the character argument makes each rational. The two integer-square
radicals are integral, and the independently justified adjacent-norm
descent makes y integral. This licenses the folding argument. First-Pell
classification and recovered main classification exclude the first
index n0=1. That yields the early size of c before proving b>=1 and
V>0. None of those steps needs the old fourth signed radical.

## The quadratic congruence has no primewise branch gap

Removing the mu^2 denominator is valid because it is coprime to
q^3(q-1)H; H need not be coprime to q or q-1. Multiplying the remaining
integer relation gives H|q^3(q-1)Kquad without cancellation. The Pell
projections imply

```
2^R*Kquad = (X-2^R)(2^R*X+1) modulo H.
```

At q>=32, r>=30, X>=q and R=2r+1,

```
X^(r-1) >= q^4*32^(r-5) > q^4*2^(2R+2),
```

because 5r-25>4r+4. The proof's actual r>=48 has ample margin.
Both factors have absolute value at most 2^(R+1)*X, and q^3(q-1)<q^4.
Thus the entire divisible product has absolute value strictly below H.
It is zero; its second factor is positive, so X=2^R. No selection of a
root independently at each prime, or division by a possibly nonunit
factor, has been smuggled into this inference. Only afterwards does odd
H make 2^R a unit and imply H|Kquad.

## Both maps preserve strict positivity

For a new zero, kappa0=Kquad/H>0. Also
Dm-(A-2)c=2c-psi_A(R-1)>c>X, so the integer
g=(Dm-X-(A-2)c)/H is positive. Therefore replacing only n by
n+kappa0+g gives a positive old zero, and the displayed centers differ
by exactly Dm/H.

For an old zero, all recovered s0,t,rho are integers with
s0>=1,t>=0,rho>=1, and u0=y-V>0. The crucial strict inequalities are
tau>s0 and

```
0<kappa0<X+cX/2<Xc<f.
```

They make the proposed n_new=Wt+rho+tau+f+u0-s0-kappa0 strictly
positive. Only n changes; all inherited kernel equations and fixed
ports are retained. Thus this is equivalence of positive-zero
existence, not equality of the two polynomials or a bijection of all
their zeros.

## Degree and scope

The changed projection summand has degree 17, below the unchanged
degree-27 leading part of Z-MV. Hence omega has degree 102 with the
same nonzero leading form. In the centered octic norm,
`s-sigma1=omega-u-v`, the squared inner expression has degree 204 and
the remaining `64*sigma3*s` has degree at most 394. The unique top
part is omega^4, proving exact degree 408 for positive beta. This is
an unbounded upper/lower argument; line tests alone would not suffice.

The adjoining Python file independently checks signed folding, selected
auxiliary recoveries, strict minimal height bounds, Pell projections and
an exact sparse polynomial congruence reduction. These finite controls
supplement the ordinary proof and do not establish it by enumeration.
They import no candidate builder or checker. Their receipt pins the
reviewed proof bytes. The original whole native tuple and ordinary
source/refutation boundary are inherited unchanged. No Lean,
internal object-ZFC equivalence, consistency proof, or absence-of-zero
claim is supplied by this peer review.
