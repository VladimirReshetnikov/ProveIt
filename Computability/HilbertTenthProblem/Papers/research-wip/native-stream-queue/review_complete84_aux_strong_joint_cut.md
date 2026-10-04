# Independent review of the complete84 joint-factor cut

**PASS in the declared four-independent-port model.** The entire frozen
[proof](complete84_aux_strong_joint_cut.md) and source were read. The saved
complete regrouping computes exactly the existing 84-operation polynomial.
The five-gate lower bound applies to its isolated joint factor at the four
stated ports, not to the complete polynomial or all zero-equivalent sources.

| Frozen author file | SHA-256 |
|---|---|
| complete84_aux_strong_joint_cut.py | `ce72fff7d178326f30214154a263bc14534ed0c50a56d1a2c94e1451d9f5f58f` |
| complete84_aux_strong_joint_cut.json | `c293e1e2683b8b7f32b57d1e2196b8644ce8329a6dd975f2d7665e6e85e6a594` |
| complete84_aux_strong_joint_cut.md | `4d67db790448fbfaf16082c904d89143f5f35152913015c55e576597160204e7` |

## Complete-source integration

The authenticated parent has 77 factor-producer gates and a seven-gate
finalizer. The new source retains every producer literally, including the
four paid ports `scaled_f_square`, `R16`, `H2`, and `aux_y2`. Reassociating
the factor product introduces the auxiliary/strong joint product and
removes the old intermediate four-factor product. The final subtraction
is still of the same computed Delta. Thus all 84 gates remain live, with
47 multiplications, 37 additions/subtractions and the same 25 supplied
ports, including 18 positive witnesses.

The all-ring identity follows from associativity and commutativity alone.
It does not replace the scaled-strong factor by a unit or infer individual
unit equations from a product equal to Delta. All signed and positive
zero tuples are identical. The complete degree 187 is consequently
unchanged; the grouped factor has degree 60+46=106 because its nonzero
leaders multiply in a polynomial integral domain.

The full finalizer and cut identities are proved by exact coefficient
arithmetic in the helper. Literal equality of the retained producers
lifts them to the complete source. Root checked its closure/liveness and
consumer logic as well as the source's exact parent comparison.

## Lower-bound challenge

Write the four independent ports as a,q,v,y. The joint polynomial is

    P=(a-q)*(q*(v-y)+y),
    P3=q*(a-q)*(v-y).

The five displayed gates give the upper bound. Degree excludes at most
one multiplication. With at most one addition, every later expression
is a monomial times a power of the one available binomial, so its Newton
support lies on an affine line. Three of P's surviving monomials already
give two independent support differences. This rules out every remaining
four-gate budget except two multiplications and two additions.

For that case, the first multiplication must have degree two. Before
the second multiplication, every quadratic leader is proportional to
its leader. Two quadratic operands would produce an uncancelable quartic
term: there is only one multiplication capable of producing degree four,
and subtracting a scalar copy of its output removes the entire output.
Therefore the second multiplication has one quadratic and one affine
operand. The cubic leader is a product of three linear leaders.

Unique factorization forces these leaders to be q, a-q and v-y, up to
scalars and order. Both distinct noncoordinate leaders require additions.
A genuinely nonlinear addition cannot supply either missing affine
operand. Canceling the first product to leave a new affine remainder
would first require another register with that product and a different
remainder; making that register uses one of the same two additions.
Both additions would then supply at most one new affine leader, leaving
the other unavailable. The two additions must instead be spent in the
affine part, leaving the entire output a product of three affine forms.

But q*v+(1-q)*y is primitive as a polynomial in v over k[q,y], since
gcd(q,(1-q)*y)=1. It is irreducible over the fraction field and hence in
the polynomial ring. P therefore has an irreducible quadratic factor,
contradicting the three-affine-factor conclusion. This argument covers
arbitrary scalar constants, reuse and cancellation. It is not an
enumeration bounded by coefficient size or intermediate values.

The actual four producer polynomials are not assumed independent when
discussing the complete source. Independence is expressly a hypothesis
of the local lower-bound model. Additional paid ports, source-specific
relations and changed coordinates remain outside it; local bounds cannot
be added to assert a global 84-gate minimum.

## Fresh replay and scope

Installed exact receipt replays from `/`, both normal and `python3 -O`,
pass. They authenticate six immediate predecessor files without executing
them, and reproduce the full regrouped array, coefficient identities,
32 signed/rational whole-source evaluations and exact ledger. Explicit
checks survive optimization; JSON comparison preserves exact types.
These arithmetic checks supplement the unrestricted proof above.

No predecessor Python, archived program or historical suite ran. This
review does not re-establish the parent's whole compiler ancestry, use
diagnostic numerals as valid programs, or claim a new universal bound.
