# Frame compression and the final integral quartics

This note describes the last semantic source change and the exact algebraic
pass from the common modular numerator source to the two delivered equations.
It supplements `MODULAR_PROOF.md`, `PROOF.md` for the fixed-growth source, and
`TWO_SQUARE_CENTER.md`. All variable domains in the delivered equations are
the unrestricted integers. A variable's descriptive name or `kind` field does
not impose an extra condition.

## 1. The retained bounded interface

The fixed-growth source begins with eighteen power requests. Eleven numerator
requests of the form `(q+1)^e` become modular Pell evaluations. Their outputs
therefore leave the magnitude frame. The old request for `q^(t+1)` becomes the
literal quadratic equation `D_(t+1)=q D_t`; it also leaves the exact-power
interface. The six remaining exact requests are

    R = 16^t,       N = B^x,       q = (BH)^x,
    D_t = q^t,      D_y = q^(y+1), M = q^x.

Every nominal index used for a Pell pair remains bounded, whether its semantic
value will be positive or negative. This distinction matters for the eleven
signed global CRT representatives in the modular construction.

Originally the frame was `W=2+sum a^2`, with one occurrence for each distinct
affine base, index, or output of the eighteen requests. The modular source has
already deleted the eleven numerator output squares. We now remove five more
square atoms:

    16, t+1, q+1, R, D_(t+1).

There are twenty-one distinct square atoms left. In particular, `t`, `R+t`,
and `q` remain. No source row other than the frame and the cofinal-center
constructor changes in this step.

## 2. Why the smaller frame suffices

The cofinal horizon constructor is the exact equation

    t=16+h^2.

Consequently `t>=16` and `W>=t^2+2>=258`. Every retained atom `a` obeys
`|a|<W`, since `W>=a^2+2`. The omitted atoms needed by the bounded interface
have the following uniform bounds, valid before recovering any sign of R or q:

    16<W,
    t+1<t^2+2<=W,
    |q+1|<q^2+2<=W,
    R^2=((R+t)-t)^2
       <=2((R+t)^2+t^2)
       <=2(W-2)<W^2.

Thus `|R|<W`. These inequalities do not use the truth of `R=16^t`; they are
available in the initial signed-power recognition argument and avoid a circular
bootstrap. Every remaining exact request's base, exponent, and output still has
strict absolute value below W. Every modular numerator's nominal index also
does. The value `D_(t+1)` requires no frame bound: after recognizing `D_t=q^t`,
its retained multiplication row proves `D_(t+1)=q^(t+1)` directly.

All later common-frame estimates can therefore use the smaller W. The lower
bound `W>=258` is stronger than the lower bounds required by the retained Pell
orientation and pooled error estimates. Completeness recomputes the frame from
the already selected semantic values and then chooses its independent Pell
witness, so shrinking the frame causes no congruence obstruction.

## 3. Replacing the three-witness center by two squares

The modular source first used

    A=L^2+u^2+v^2+w(w+1).

Its role is to ensure `A>=L^2` while allowing A in a specified congruence class.
The special class in this problem permits the smaller constructor

    A=L^2+u^2+v^2.

This change is justified by the two-square cofinal-center theorem; it is not a
general assertion that every residue is a sum of two squares.

Here `Omega=NM` is positive and odd, every prime dividing Omega divides q,
`n=q+1` is a unit modulo Omega, and the required center class is

    A0=(n^2+1)/(2n)=1+q^2/(2(q+1)) mod Omega.

Let `D=W(W+2)` and let `epsilon=(W+1)+sqrt(D)` be the norm-one unit in the
finite quadratic ring modulo Omega. If the order of `epsilon^W` is `2^r k`
with k odd, choose the frame index `Wk` and set

    L=X_(Wk)(W+1).

Then the image of `epsilon^(Wk)` has order a power of two. For each prime power
`p^a` dividing Omega, there are two cases. If `L` is not `+1` or `-1` modulo p,
then `A0-L^2` is a unit modulo p. If `L=delta` modulo p with `delta=+1` or `-1`,
the norm-one relation and the power-of-two order force the whole quadratic-ring
unit to equal delta modulo p. This includes the ramified case `D=0 mod p`:
a nonzero nilpotent part would have odd p-power order. The kernel of reduction
from the quadratic ring modulo `p^a` to that modulo p is a p-group; hence the
power-of-two-order unit already equals delta modulo `p^a`. Thus `L^2=1 mod p^a`
in the second case, and

    A0-L^2 = q^2/(2(q+1)) mod p^a

has even p-adic valuation, or is zero modulo `p^a`.

Every unit modulo an odd prime power is a sum of two squares. One proof starts
modulo p: the two sets of squares, one translated by the target, have sizes
`(p+1)/2`, so they intersect; at least one coordinate is nonzero, which permits
successive lifting. A residue of even valuation is obtained by multiplying
the representing coordinates by the appropriate power of p. Zero is represented
by zero. We therefore obtain a two-square representation of `A0-L^2` modulo
each prime power; the ordinary CRT combines these into u and v modulo Omega.
Replacing u by `u+j Omega` makes `A=L^2+u^2+v^2` arbitrarily large without
changing the congruence.

The frame parity condition also survives. The quotient
`Y_W(W+1)/W` is odd. For W even this follows from
`Y_(2m)=2X_m Y_m` and the oddness of every `X_m(W+1)`; for W odd it follows
directly from the recurrence modulo two at the even center W+1. Multiplying
the index by the odd number k multiplies this quotient by
`Y_k(X_W(W+1))`, which is odd. Thus the selected L belongs to the exact same
frame relation as before. Its absolute size exceeds `W^W`, and the new
constructor still implies the required very large positive A.

The choice of L is essential: an arbitrary smaller Pell index may make the
target fail to be a sum of two squares. The completeness proof chooses the
odd multiple k before filling u and v. Soundness merely uses `A>=L^2` and
does not require this special selection for an arbitrary zero of the source.

## 4. Exact integral algebra after the semantic change

The signed Horn factoring pass is an identity of its external polynomial
boundary. Its internal gate coordinates can be reconstructed in both
directions. The inherited independent checker validates all eighteen literal
edits, each affine square root, the protected product chain, the guarded
bundle identity, and the fact that no protected internal wire escapes.

Next, the monic elimination certificate has 208 steps. Each step proves an
actual equation of the form `v-f=0` or `f-v=0`, with integral polynomial f
independent of v. Substituting f and deleting this equation gives a bijection
of integer zero sets after restoring v=f. The checker verifies every row
after substitution, the continued quadratic degree, and the complete
coordinate map. It also verifies that 128 removed unused coordinates have
no surviving occurrence. The result has 232 coordinates and 178 quadratic
residuals. Sixty-nine integral translations then center inherited constants.

The final refinement uses only these zero-set-preserving operations:

* Integral translations `old_v=new_v+c`.
* Unit triangular coordinate shears `old_v=new_v+sum c_i v_i`.
* Elementary row operations `R_i <- R_i+k R_j`, with i different from j.
* Monic affine elimination, with its explicit restoration formula.

Each translation and shear has an integral inverse. The row operations are
invertible because the source row is retained, so their common zero sets
are identical. The affine eliminations have integral inverse restorations.
All resulting residuals have degree at most two. The source A coordinate
receives a final shift by six; the radix progression parameter receives no
additional shift. The inherited projection of `base4.T` is intentionally
skipped because it is no longer affine after adding the common modular root.
Its omission is recorded in each certificate.

The balanced endpoint uses 46 recorded operations, including two affine
projections; the compact endpoint uses 49, including three. The latter
eliminates one additional coordinate at the cost of a much larger collected
support. The files contain every residual and every coefficient:

| Endpoint | Integer variables | Quadratic residuals | Quartic monomials | Quartic height | Residual height |
|---|---:|---:|---:|---:|---:|
| Balanced | 230 | 176 | 4,482 | 7,968 | 64 |
| Compact | 229 | 175 | 12,006 | 7,968 | 64 |

In either case the final single equation is the sum of the displayed residual
squares. Over the integers this sum vanishes if and only if every residual
vanishes. There are no additional inequalities, sign restrictions, congruence
conditions, exponentiation operators, or unlisted parameters in the delivered
polynomial definition.

## 5. What the checks establish

`check_fixed_growth_source.py` independently reconstructs every raw fixed-growth
source row and all eighteen request-manifest ports from the pinned parent.
`audit_modular_interface.py` independently checks the intervening modular
source delta. `check_final.py` checks the entire frame and center delta,
independently audits the Horn factorization, replays every monic restoration,
translation, shear, row operation, and affine projection, and independently
collects every coefficient of both quartics. All occurence counts and claimed
metrics are recomputed from the literal files.

Normal Python and optimized Python (`-O`) both pass. Seven deliberate
corruptions are rejected: for each endpoint, a changed affine restoration,
a changed row-operation multiplier, and a changed collected coefficient;
and, in the factoring certificate, a changed square root. Explicit
exceptions perform the checks, so disabling Python assertions does not
disable validation.

These finite checks establish the literal algebra and source-interface
claims. The unbounded arithmetic equivalence is the separately stated
ordinary proof, composed with the pinned C222/ZF/ZFC calibration. The package
does not claim a new proof of Con(ZFC) or an independently compiled proof
assistant formalization of that entire chain.
