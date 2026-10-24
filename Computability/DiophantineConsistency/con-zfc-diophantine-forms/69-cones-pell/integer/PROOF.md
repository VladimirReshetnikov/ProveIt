# A canonical-anchor cone for Diophantine consistency equations

## 1. Result and comparison scope

This construction starts with the literal 41-integer quartic in package 64
of ProveIt, pinned at commit
`9cca523d9f27ad39d52993f4065cbd7e58f8bdd4`. It uses that source's entire
`mixed-parity-unrounded-1064921` native coefficient tuple. Its four ports
are `beta`, `K0`, `MC`, and the already shifted `MF`. They are never mixed
with another tuple.

The new polynomials are:

| File | Domain | Unknowns | Residuals | Exact polynomial degree |
|---|---|---:|---:|---:|
| `quartic38.json` | Unrestricted integers | 38 | 25 | 4 |
| `sextic32.json` | Unrestricted integers | 32 | 19 | 6 |
| `octic27.json` | Unrestricted integers | 27 | 14 | 8 |

Each single polynomial is the sum of the squares of its listed residuals.
The constant registers are abbreviations for fixed integers, not further
unknowns. Exact coefficient recipes and compressed actual integer bytes
are provided. The source and two new weights together require 881,696 raw
minimal unsigned bytes. The original four native ports alone require
532,479 bytes. The variable reduction therefore comes with a larger fixed
coefficient representation.

At the inspected pin, package 64 supplies the 41-integer quartic, while
package 62 supplies a 35-integer sextic and a 30-integer octic. The new
construction saves three unrestricted integer unknowns in each of these
degree slices. This does not lower the nine-positive or ten-integer
high-degree variable bounds. It is not a claim of global optimality.

The theorem proved here is an **existence equivalence**, using canonical
native witnesses in the completeness direction. It is deliberately not a
bijection between every source zero and every new zero. The subsequent
polynomial eliminations from the new quartic to its two companions are
actual bijections of integer zero sets.

## 2. The two old guards and the new guard

Write

    Pos(u,v,t) = 1 + u^2 + v^2 + t(t+1).

Every value of Pos on integers is positive, and every positive integer is
a value of Pos. For the latter claim, apply the three-square theorem to
`4n-3`, which is positive and congruent to 1 modulo 4. Its representation
has one odd and two even coordinates. Writing them as `2t+1,2u,2v` gives
`n=Pos(u,v,t)`.

The old quartic has the two quadratic rows

    F*alpha = Pos(FA1,FA2,FA3),
    F*C     = Pos(FC1,FC2,FC3),
    C = beta*J + 1 - F - alpha.

They enforce that F, alpha, and C have one common nonzero sign. They use
six private integer unknowns. They do not by themselves choose which of
the two common signs holds; the inherited source proof recovers the sign
of the radix only after its Pell argument.

Set the following fixed positive integers:

    rho = 2^121,
    beta = rho^8801 - 1 = 2^1064921 - 1,
    A = rho^3296 = 2^398816,
    H = rho^2196 = 2^265716,
    T = D_C + D_R + 1 = K0 - beta*rho + 1,
    Walpha = 2*T*A,
    WC = T*beta.

Here `D_R=rho` and `K0=D_C+(beta+1)*D_R`, so the displayed recipe for T
uses the authentic source K0. H occurs only in the proof and audit; it is
not a new coefficient in the polynomial.

For the three linear polynomial abbreviations

    x = beta*F,
    y = Walpha*alpha,
    z = WC*C,

define

    Cone(x,y,z) = 2(xy+xz+yz) - x^2 - y^2 - z^2.

Delete the two old guard rows and their six private coordinates. Add the
single quadratic row

    Cone(beta*F, Walpha*alpha, WC*C)
      = Pos(cone1,cone2,cone3).

All other rows, including the separate eta*zeta guard, are unchanged.
Thus the new system has `41-6+3=38` unknowns and `26-2+1=25` rows. Every
row remains quadratic. In the sum of their squares, the coefficient of
`tau^4` is exactly 1, so the polynomial degree is exactly four after all
fixed coefficients are specialized to their actual values.

## 3. Two elementary cone lemmas

### Lemma 1: the cone forces a common sign

If real numbers x,y,z satisfy `Cone(x,y,z)>0`, then they have the same
strict nonzero sign.

To prove this, suppose that they do not. Permuting them and simultaneously
changing all signs allows the mixed or zero case to be written with
`x>=0`, `y>=0`, and `z<=0`. Then

    Cone(x,y,z) = -(x-y)^2 + 2z(x+y) - z^2 <= 0,

a contradiction. The zero-coordinate cases are included. Since all three
fixed weights in the new guard are positive, this lemma applies directly
to F, alpha, and C.

### Lemma 2: a factor-two box lies inside the cone

If `L>0` and each of x,y,z belongs to `[L,2L]`, then

    Cone(x,y,z) >= 3L^2 > 0.

For a direct proof, permute the coordinates so that `x<=y<=z`. Since
`z<=2L<=2x` and `z>=y`,

    -x <= z-x-y <= x-y <= 0.

The identity

    Cone(x,y,z) = 4xy - (z-x-y)^2

therefore gives `Cone>=4xy-x^2>=3x^2>=3L^2`.
Equivalently, separate concavity reduces the box minimum to its eight
vertices. After division by L^2 their values are 3,4,4,7,4,7,7,12.

These are universal real-algebraic lemmas. Finite tests in the supplied
checker are diagnostics, not their proofs.

## 4. Why the authentic canonical witnesses satisfy the new guard

This is the main point of the construction. The native compiler already
puts a large **fixed anchor** in every occupied cell. Consequently its
three data coordinates are much more tightly located than arbitrary
positive numbers. Different fixed weights put their canonical values into
one factor-two box.

### 4.1 Native cell bounds

The source-34 tuple uses radix `rho=2^121`, block length 8801, and four
anchor positions

    1095, 1096, 2195, 3296.

Its canonical tiling word is occupied in every cell. This can be seen
directly from its canonical tiling construction; the shared compiler
proof also derives it from propagation of the horizontal occupancy bit
from Start through the entire cyclic word. In every occupied cell all
four anchor digits are exactly 1. The other native positions consist of
the selector and copy tracks and the two controller dummies. Every one
of these other positions is at most 1064. Their digits lie between 0 and
3. The rank controller changes only the allowed dummy choices, so it
preserves these facts.

Let a native cell value be c_i. Its top fixed anchor contributes
`A=rho^3296`. Below it, the anchor at 2195 and all remaining digits give

    0 <= c_i-A <= rho^2195 + rho^1097 - 1 < rho^2196 = H.

The middle upper bound simply allows every digit below 1097 to be as
large as rho-1; it therefore covers the actual much sparser digits,
including the value-3 dummy. No carry assumption about a newly invented
code is being made.

For N cells put

    B = rho^8801, q = B^N, J = (q-1)/(B-1).

As usual `J=1+B+...+B^(N-1)` is a positive integer. Summing the cell
bounds gives

    A*J <= C < (A+H)*J < 2*A*J.                  (1)

A whole-cell cyclic rotation preserves exactly the same bounds.

### 4.2 The output coordinate F has the same fixed-anchor normalization

Let U be the canonical one-cell spatial rotation of C and V the
canonical temporal rotation. Both satisfy (1). The spatial rotation is
represented by multiplication by B modulo q-1. The canonical native
controller proves

    R = d*width (mod d*N),   d=1064921.

The source scale is `w_source=2^(R-t)`, where `t=d*N`, and `R>t`.
Therefore multiplication by w_source modulo q-1 is a whole-cell cyclic
rotation. This establishes the required property of V using the actual
controlled rank, rather than introducing an independently selected
rotation exponent.

The source transport identity is literally

    (K0+w_source)*C = (q-1)*z_transport + F.

With `K0=D_C+B*D_R`, this says that F is the residue modulo q-1 of

    D_C*C + D_R*U + V.

All terms are nonnegative, and their cell bounds imply

    T*A*J <= D_C*C+D_R*U+V < T*(A+H)*J,           (2)

where `T=D_C+D_R+1`.

The following fixed integer inequality holds:

    2*(T+1)*(A+H) < beta.                        (3)

Its proof is given in the next subsection, and the actual integer bytes
are checked independently of any toy coefficient values. In particular
the quantity in (2) lies strictly between 0 and `beta*J=q-1`. Thus it is
already the canonical residue F, without another wrap or an offset.
Combining (1)-(3),

    T*A*J <= F < 2*T*A*J,
    1 <= F+C < beta*J/2,
    beta*J/2 < alpha=q-F-C <= beta*J.             (4)

For the last upper bound use the positive integer inequality `F+C>=1`.
The stronger fact `F+C>1` is also available but unnecessary.

### 4.3 Proof of the fixed numeral inequality

The coefficient recipe has 989 native support positions. Every clause
coefficient c_e is less than `2^97`: its binary weights run from
`2^10` through `2^96`, and their geometric sum plus 1 is still below
`2^97`. The largest exponent occurring in D_C is 5495. There are four
bare monomials and two reflected copies of all clause coefficients.
Consequently the total coefficient mass of `T+1=D_C+D_R+2` is at most

    7 + 2*989*(2^97-1) < 2^109 < rho.

Thus

    T+1 < rho^5496.

Also `A+H < 2*rho^3296`, and hence

    2*(T+1)*(A+H) < 4*rho^8792 < rho^8801-1 = beta.

The final inequality follows already for rho>=2, since the remaining
exponent gap is nine. Our rho is much larger. These deliberately loose
bounds avoid dependence on a particular accepting tableau.

### 4.4 Completion of the cone argument

Set the positive number

    L = T*A*beta*J.

The three inequalities (4) imply that each of

    beta*F,   2*T*A*alpha,   T*beta*C

lies in `[L,2L]`. Lemma 2 therefore proves

    Cone(beta*F,2*T*A*alpha,T*beta*C) >= 3L^2 > 0.

This value is a positive integer, so it has a Pos representation. Supply
that representation as the three new cone variables. Every other
canonical source coordinate is retained unchanged.

## 5. Soundness, completeness, and the logical conclusion

**Soundness.** Any integer zero of the new quartic makes the new cone
equal to a positive Pos value. Lemma 1 therefore makes F, alpha, and C
have one common nonzero sign. In particular `F*alpha>0` and `F*C>0`.
Represent these two positive integers separately by Pos. Supply the six
old private guard coordinates. All 26 old quartic rows now vanish exactly.
The inherited Q41 theorem then gives a finite ZFC refutation. This step
uses neither canonicality of the new zero nor an early assumption that
q is positive.

**Completeness.** A finite ZFC refutation gives a canonical accepting
native tableau through the inherited calibrated K215 interface. The
source-34 compiler and package-64 witness construction supply canonical
zeros of Q41 with the exact native cell and rank properties used in
Section 4. That section supplies a Pos representation of the new cone.
Delete the six old guard coordinates and use the three new coordinates.
The result is an integer zero of the new quartic.

Both implications are ordinary arithmetic and finite-computation arguments
formalizable in ZFC. Composing them with the explicitly cited source
theorem, then negating, yields

    ZFC proves: quartic38 has no integer zero iff Con(ZFC).

The same conclusion follows for each companion below. Here Con(ZFC) is
syntactic consistency of the repository's specified recursive ZFC proof
calculus. No coefficient depends on assuming consistency, searching for
a refutation, or using an oracle for that search.

This package does **not** supply a new end-to-end Lean or Rocq certificate
or a derivation inside the repository's object-language ZFC calculus.
The universal native compiler, Pell rank, and K215/refutation calibration
results are inherited, and their formalization status is not changed by
the finite algebra checks in this package. The new cone argument is
proved above, rather than asserted on the basis of numerical samples.

## 6. The sextic in 32 integers

Start with the new quartic, put `q=beta*J+1` and `k=eta+zeta`, and make
the simultaneous restoration

| Eliminated source coordinate | Polynomial restoration |
|---|---|
| N | `q*(L+1)` |
| X | `4*w_scale*q` |
| C2 | `c^2` |
| F2 | `f^2` |
| Baux | `I^2` |
| P | `k+E*(c-eta)` |

In addition, use the integral change of the retained root coordinate

    tau_old = tau_new + E*(c-eta).

Writing `u=E*(c-eta)`, the first Pell residual becomes exactly

    (tau_new+u)^2 - (k+u)^2 + (k+u)*k - 1
      = tau_new^2 + (2*tau_new-k)*u - 1.

The cancellation leaves degree three. All other residuals also have
degree at most three after the six definitions are substituted. Their
six definition rows vanish identically and are deleted. There remain
`38-6=32` coordinates and `25-6=19` rows. Their sum of squares has degree
exactly six: its coefficient of `I^4*g^2` is 1, coming from

    -I^2*g+y^2-1.

The displayed maps are integral polynomial maps. Forgetting the six
defined coordinates and replacing the old tau by `tau_old-E*(c-eta)` is
their inverse on zero sets. This is a bijection, unlike the initial
canonical-cone restriction.

## 7. The octic in 27 integers

Instead set

    q = beta*J+1,
    k = 1-V+j*c+h*E

and restore the following eleven coordinates:

| Eliminated source coordinate | Polynomial restoration |
|---|---|
| L | `q^2-1` |
| N | `q^3` |
| X | `4*w_scale*q` |
| C2 | `c^2` |
| F2 | `f^2` |
| Baux | `I^2` |
| g | `y^2-V^2` |
| zeta | `k-eta` |
| P | `k+E*(c-eta)` |
| D | `4*w_scale*q+a*c+gamma*(4*a+3)` |
| Delta | `a^2+4*a+3` |

The source row for V and the index quotient is now an identity, and
supplies the definition of k. Every right-hand side uses only retained
coordinates. Each of the eleven eliminated definition rows is identically
zero after simultaneous substitution. The other fourteen rows have
degree at most four, so their sum of squares has degree at most eight.
The auxiliary row is

    I^2*(V^2-y^2)+y^2-1.

Its square contributes `I^4*V^4` with coefficient 1, and the exact checker
verifies that no other row changes that coefficient. Thus the degree is
exactly eight, also after specializing all coefficient ports. There are
`38-11=27` unrestricted integer unknowns. Forgetting and restoring these
eleven coordinates are inverse integer-polynomial maps on zero sets.

## 8. Reproduction and evidence

Run the Python standard-library driver:

    python3 reproduce.py
    python3 -O reproduce.py

It reconstructs the complete authentic native tuple from the literal
K215 transition table and checks the exact ordered 943-tile list. It
then checks the new fixed numeral bound, emits both new fixed weights,
and emits the three complete polynomial packets. Exact sparse polynomial
arithmetic verifies all 17 deleted definitions, the cancellation in the
sextic root change, every residual degree, every variable's occurrence,
and the three uniform leading-coefficient certificates. Its checks do
not rely on Python assert statements.

The cone vertex calculation is exact. Finite mixed-sign examples and
6,372 small native-word/rotation examples are explicitly labeled as
diagnostics. They are not substitutes for the universal proofs above.
`CHECKS.json`, `coefficients/COEFFICIENT_BINDING.json`, and the sparse
expansion certificates record the completed finite checks.

The fixed payloads are gzip streams of minimal unsigned little-endian
integer bytes. For bytes b_0,...,b_(m-1), the integer is
`sum(b_i*256^i)`. The manifest records both raw and compressed hashes.
Gzip headers may vary with runtime versions; the raw integer hashes are
the mathematical coefficient identities.

## 9. Sources and attribution

The pinned repository is
<https://github.com/VladimirReshetnikov/ProveIt/tree/9cca523d9f27ad39d52993f4065cbd7e58f8bdd4>.
The literal parent and its proofs are package 64's
`integer41/quartic41.json`, `PROOF41.md`, and `PROOF44.md`.
The canonical source and actual coefficient recipe are package 34's
`coefficients/COEFFICIENT_PROOF.md` and `build_coefficients.py`.
The shared occupancy and anchor theorem is in its retained
`coefficients/sources/WANG943_LANGUAGE_AND_COMPILER.md`, Section 4;
the mixed tuple's changed positions and controller are specified in
`COEFFICIENT_PROOF.md`.

Copies of these texts, the literal source system, the source coefficient
builder, the 943 tiles, the machine input, and original licenses/notices
are retained in `upstream/`. The imported material remains distinguished
from the new construction. The weighted cone and its use of the fixed
canonical anchor are new to the inspected proposals; priority over all
external mathematical literature has not been established. Independent
AI-assisted review is not external human peer review.
