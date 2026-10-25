# Independent review of the two centered product-square polynomials

This review was performed by a separately tasked agent in the same
AI-assisted workflow. It is not an external human endorsement or a new
proof-assistant verification. The reviewer did not import the new producer
or its verifier. The accompanying `independent_lower_center.py` independently
checks both new literal circuits, their fixed coefficient payloads, the
exact cancellation identities, and the complete leading homogeneous forms.

## Outcome

Both constructions are correct as ordinary arithmetic reductions relative
to the specifically retained package-133 calibration:

| Equation | Domain | Variables | Binary operations | Exact degree |
|---|---|---:|---:|---:|
| Lower center `(A-1)UE` | strictly positive integers | 10 | 87 | 323 |
| Upper center `AUE` | strictly positive integers | 10 | 88 | 318 |

The upper center and its strict transport argument were suggested by this
reviewer after checking the lower-center proof. The two shears in fact give
bijections of the full positive zero sets with the retained 85-operation,
degree-328 parent. They are not merely existential reductions.

This result is an operation/degree tradeoff in the ten-positive-variable
family. It is not a ten-unrestricted-integer equation, and it does not
dominate the existing 89-operation, degree-288 point. The larger task's
height-one integer quartics constitute a separate construction.

## Soundness and the order of signs

For either center d, the carrier identity is the polynomial identity

    n+V(d-bB) = (n+dV)-bVB.

Consequently `N_new(n)=N_85(n+dV)`. The proof correctly avoids assuming
`V>0` at an arbitrary positive input. Such an assumption would be false:
the signed expression `b=c(T+alpha)-R` can initially have either sign.

At a positive zero of the new equation, package 133's Sections 2--4 still
apply because they require only the unchanged positive inputs and the
product-square equation with a rational carrier. They recover G=g^2, the
adjacent-Pell equation, the doubled strong pair, and the odd main index.
The estimate b>c and hence V>0 is obtained before the transport sign and
does not use the old carrier's center. Both new centers are positive.
Therefore n+dV is a positive integer, and the exact shear gives an actual
positive zero of the old polynomial. Its soundness theorem can then be
applied without circularity.

## Completeness of the lower center

The exact identity

    G-[(A-1)UE]^2 = E+2(A-1)U^2E^2 > 0

gives g>d on calibrated witnesses. Both quantities are integers, so
g-d>=1. The parent supplies y>V>0, b>c, Fsqr>3, and hence V>2c.
Moreover H>3X and X>1 imply

    0<kappa=[X(3c-2X)+2]/H<c,
    0<s=Y/q^3<Y<c.

For the parent's positive-root witnesses, the inverse shear is

    n_new=(g-d)V+g(y-V)+(1+(q-1)bV)t+rho-kappa-s.

Here t,rho>=0, so n_new>V-kappa-s>0. This establishes the stated
constructive completeness argument without needing to choose an arbitrary
old carrier coordinate freely.

## Why the upper center is also complete

The inequality g>d no longer holds for d=AUE. Its replacement is a strict
property of every fully decoded old positive zero, not a new premise on
arbitrary inputs. The old source projection gives

    X=2^R, R>3q, w=X/q, C>=1, 0<F<q.

Since q>=32, `2^(3q)>q^2`, so w>q>F. Thus

    B=(K0+w)C-F>0.

The integer B is at least one. Parent Section 6's fifth-index estimate gives
b>4g. The identity

    4G-(AUE)^2 = 4E+(3A^2-4)U^2E^2 > 0

gives d<2g. Therefore bB-d>2g>0. With `(q-1)t=B`, the inverse shear is

    n_new=gy+t+rho-kappa-s+V(bB-d)>V-kappa-s>0.

This proves completeness of the upper-center sibling. All uses of the
decoded B and source projection occur in the old-zero-to-new-zero
direction; they are not used to justify new-zero-to-old-zero soundness.

## Stronger full-zero-set bijection

The final Section 8 of the component proof was independently checked.
For an arbitrary old positive zero, its integral carrier can have either
sign, so write it as epsilon*g*y. The inverse shear is

    n_new=epsilon*g*y+V(bB-d)+t+rho-kappa-s.

The decoded first index gives `k=2 psi((R+1)/2)>=R+1`, so rho>=0.
Both centers satisfy d<=AUE<2g, and the previous bounds give B>=1,
b>4g, `y<3V/2`, `kappa+s<2c<V`. Also g>2: E and F0 are positive
integer squares greater than one, so their positive square roots are
each at least two. It follows that

    n_new > (g/2)V-kappa-s > V-kappa-s > 0.

This handles both values of epsilon. The forward and inverse maps change
only n, while d and V are independent of n. They are therefore mutually
inverse on the full positive zero sets.

## Exact degrees and literal circuits

Let Z0 be the old uncentered carrier. The common exact identity is

    N = -M^2[Q(G-d^2)+d^2]V^2
        +2(Q-1)MdVZ0+(Q-1)Z0^2+M^2G.

The literal prefix has degree bounds Q:86, M:13, G:56, V:80, d:28,
and Z0:99. The defect degree is 51 for the lower center and 46 for the
upper center. Thus the four final summands have degree bounds
323/306/284/82 or 318/306/284/82, respectively.

The independent checker propagates highest homogeneous components through
the actual unchanged DAG prefix, including all ten input variables and
the fixed ports with degree zero. It verifies the complete leading forms

    -2^11 (beta J)^153 w^33 Y^77 i^14 (eta+zeta)^44 (beta J-F)^2,
    +2^10 (beta J)^150 w^32 Y^76 i^14 (eta+zeta)^44 (beta J-F)^2.

The selected coefficients are respectively `-2^11 beta^153` and
`2^10 beta^150`, nonzero for the supplied actual beta. These certify the
claimed exact degrees, rather than only generic-coefficient or sampled
degree bounds.

The checker independently compares every parent and new gate. The lower
center replaces exactly three old gates by five; the upper center adds
one further addition. Topology and complete liveness are checked, giving
52 multiplications, 20 or 21 additions, and 15 subtractions. There are no
dead gates, additional unknowns, or altered mathematical coefficient ports.

## Coefficients and verification scope

The complete four integer payloads were opened and independently checked
against both the new circuit bindings and the parent's raw identities.
Their bit lengths and raw SHA-256 hashes agree with the retained parent.
The current gzip files agree with their current gzip hashes. Gzip metadata
can differ from a historical container while the decoded integer remains
the same, so the coherent-tuple comparison uses the raw byte identities.
The checker also verifies

    beta=2^(67*8807)-1,
    K0>0, 0<MC<beta<MF<2beta.

Both the ordinary and optimization-enabled Python runs passed. The exact
new algebra and the unbounded shear arguments above were checked here.
The retained package-133 product-square, Pell folding, and native-to-ZFC
refutation calibration remain inherited theorem dependencies. This review
does not assert consistency or inconsistency and does not replace those
unbounded arguments with finite arithmetic tests.
