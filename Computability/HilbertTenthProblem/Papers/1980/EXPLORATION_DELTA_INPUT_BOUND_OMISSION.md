# Removing the raw-input term from the discriminant bridge gives a false76

The raw bound in the [77-operation certificate](FIXED_RAW_UNIVERSAL_77_PROOF.md)
cannot be weakened from

    C+alpha+d*x=q

to `C+alpha=q`. That deletion saves one addition, but the resulting
**76=42M+34A** system has a full strictly positive false input for the fixed
machine accepting exactly the positive even integers. It retains **32 positive
existential coordinates and 20 equations**, including the input Pell gap and
the period divisor.

The [checker](../verification/explore_delta_input_bound_omission.py) and
[receipt](../verification/explore_delta_input_bound_omission.json) verify every
weakened source residual and an exact algebraic map of all20 equations from
a genuine input2 witness to a false odd input. The argument below establishes
the positivity of the changed coordinates at the actual compiler/kernel
parameters. It does not rely on choosing an unrelated small Pell parameter.

## 1. The precise weakened source

Delete only the adapter instruction

    raw_bound=bounded+d*x,

where the existing register bounded=C+alpha and the separately paid scaled
input d*x remain. Replace the comparison raw_bound=q by bounded=q. The marker,
mask, transport, kernel and all four input equations are retained. In
particular, with the77 notation

    A0=aP+2, Delta=A0^2-1, Hpell=4aP+3,
    u=d*x+b,

the bridge still imposes

    kappa=u+delta*Delta,
    c=kappa+phiP,
    muP^2=1+Delta*kappa^2,
    muP=W+aP*kappa+rho*Hpell.                            (1)

The compiler still has b odd, d even, Start in the native unit position,
End in the R position, and the necessary odd packed index. No marker or
parity constraint is weakened. After the deletion, the only source equation
containing raw x is the first equation of (1).

| Part | M | A | Total |
|---|---:|---:|---:|
| Retained outer source |10|10|20|
| Retained fixed-minus kernel |25|18|43|
| Adapter after deleting the raw-bound addition |7|6|13|
| **Weakened, false system** |**42**|**34**|**76**|

## 2. A uniform positive bound on the discriminant quotient

For any A0>=2, write Delta=A0^2-1 and, for odd n>=1, put

    delta_n=(psi_A0(n)-n)/Delta.

The odd-index congruence from the77 proof makes this an integer. The standard
Pell identities give

    psi_A0(n+2)-psi_A0(n)=2chi_A0(n+1).

Since n+1>=2 and chi_A0(2)=1+2Delta, it follows that

    delta_(n+2)-delta_n
      =2(chi_A0(n+1)-1)/Delta >=4.

Starting with delta_1=0 proves the uniform lower bound

    delta_n>=2(n-1), n odd and positive.                 (2)

This is an exact inequality for every parameter A0>=2. It does not assume
an asymptotic regime or any particular choice of the other kernel witnesses.

## 3. Fix one actual even-input machine and a genuine witness

Choose the fixed normalized machine accepting precisely the positive even
raw inputs. Concretely, after its required stationary first step at Q, it
scans the remaining unary ones leftward, toggling between two residue states.
At the blank it halts exactly when the total unary length is even; otherwise
it enters a permanent loop. Its initial unary length is x+2, so this is
equivalent to x being even. This is one fixed machine, independent of all
later witness choices.

Apply the effective77 compiler to that machine. Input x=2 is accepted, so
the complete77 positive converse supplies a genuine tuple with its actual
fixed compiler numerals, packed word, packed index and all kernel/input
coordinates. Keep one such tuple. Its input index is

    u0=2d+b, kappa=psi_A0(u0), delta=delta_(u0).

Because b>=1 is odd and d is even, u0 is odd and u0>=2d+1. By (2),

    delta>=2(u0-1)>=4d>d.                              (3)

Also aP is even at this actual kernel: its source equation is
aP=Y*(X+1), and Y=s*q^3 is even because q=B^N is a power of two. Hence

    Delta=(aP+2)^2-1 is odd.                            (4)

These claims hold at the actual enormous kernel parameter. No freely chosen
small-parameter example is substituted for it.

In fact the same map works from every positive77 witness at x=2: the proved
input bridge forces kappa=psi_A0(2d+b), and the source equations force aP
even. The canonical positive converse is needed only to guarantee that at
least one such starting witness exists.

## 4. Map the full tuple to a false odd raw input

Change exactly the following values:

    x' = 2+Delta,
    delta' = delta-d,
    alpha' = alpha+2d = q-C.                            (5)

Keep every fixed compiler numeral and every other existential coordinate
unchanged. The new raw input is positive and odd by (4), so the chosen fixed
machine does not accept it. Both changed existential coordinates are positive:
delta'>0 by (3), and alpha'=q-C>0 by the original word bound.

The weakened bound now holds as C+alpha'=q. The only remaining occurrence
of x is in the first bridge equation, whose right side is unchanged:

    d*x'+b+delta'*Delta
      =d*(2+Delta)+b+(delta-d)*Delta
      =2d+b+delta*Delta
      =kappa.                                          (6)

The input norm, gap and exponent equations are unchanged because their
coordinates have not changed. The same is true of every outer and kernel
equation. The original packed word and its odd index remain exactly the
same; the new index expression d*x'+b is still odd. Thus the necessary
parity condition does not prevent this alias.

All32 positive coordinates and all20 weakened equations are therefore
satisfied at a raw input rejected by the fixed machine. This is a full
arithmetic false positive, not merely a failure to recover a size bound
on one auxiliary witness.

The deleted bound would indeed exclude it. The actual kernel has aP>q,
so Delta>q and d*x'>q. No positive alpha can then satisfy
C+alpha+d*x'=q. The original77 source remains sound.

## 5. Source checks and evidence boundary

The checker imports the77 source and changes only its raw-bound residual
and one comparison. It confirms the exact76 ledger. More strongly, it
substitutes (5) into every weakened source residual and checks that all20
become precisely the corresponding original residuals at x=2. This includes
the unchanged kernel equations; their acyclic norm correction is checked
separately in the schedule audit.

Finite Pell calculations verify (2), its exact consecutive-index increment,
and positive instances of the bridge/bound transformation. Those numerical
instances explicitly use illustrative parameters and do not claim to be
full packed-kernel tuples. The actual full compiler instance is obtained
from the fixed even-input machine and the proved77 positive converse, with
the exact witness transformation (5).

The machine check verifies its scan/loop transition structure and bounded
examples of both parities. Its unbounded even-input characterization follows
from the two-state counting invariant. Full astronomical Pell coordinates
are not numerically materialized, and no source file of77 is modified.

This rejects the particular raw-bound deletion. It is not a lower bound on
all possible input bridges or all76-operation universal certificates.

Review status: author and independent complete proof/source reviews pass.
Fresh default verification matches the saved receipt. Dependency hashes
normalize CRLF to LF so Git's line-ending conversion does not invalidate
an otherwise identical source state.
