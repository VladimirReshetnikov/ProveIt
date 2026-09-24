# Life preimages: a finite existential problem with unbounded periods

The promising one-layer problem is existence of a **periodic preimage**
of a periodic target. This note audits the quantifiers and gives its
exact finite witness formulation. It supplies no arithmetic operation
count or universal certificate below 90.

## 1. Primary-source distinctions

Salo and Torma's [2025 paper](https://www.utupub.fi/bitstream/handle/10024/188843/1-s2.0-S0304397525001756-main.pdf?sequence=1)
distinguishes these problems:

| Target | Allowed preimage | Result | Location |
|---|---|---|---|
| Explicit finite pattern | One-cell larger finite pattern | NP-complete existence; coNP-complete orphanhood | Theorem 6, p.15 |
| Finite-support configuration | Arbitrary infinite configuration | NP-complete existence | Theorem 5, p.15 |
| Totally periodic configuration | Arbitrary infinite configuration | Pi^0_1-complete existence | Theorem 8, pp.15-16 |
| Totally periodic configuration | Totally periodic configuration | Sigma^0_1-complete existence | Theorem 9, p.16 |

Theorem 9 also gives undecidability when an unrestricted preimage is
promised. Theorem 4 proves **semiweak**, not strong, block-map universality;
strong universality remains a stated question. The finite-support
dynamical simulation mentioned in the introduction is a separate claim.
The gadget proofs depend on their SAT verification, as the authors state.

The earlier [2022 accepted manuscript](https://www.utupub.fi/bitstream/handle/10024/185782/GOLGOE-submission.pdf?isAllowed=y&sequence=1)
proves that a four-cell zero padding reduces finite-support-target
preimage existence to a finite local check (Theorems 1-3). The preimage
may be infinite and semilinear. It explicitly leaves open whether every
finite-support target having any preimage has a finite-support preimage,
and asks whether finite-support-preimage existence is decidable
(manuscript pp.13-14). Thus these cited results do not establish
undecidability for that stricter finite-support witness problem.

Jeandel's [periodic domino theorem](https://members.loria.fr/EJeandel/publis/undec.pdf),
Theorem 5, is the primary tiling result used for the periodic branch.
It effectively associates tiles with a Turing machine so that nonhalting
can give an aperiodic tiling system, whereas one halting outcome admits
a periodic tiling. This explains why replacing arbitrary preimages by
periodic ones changes the relevant quantifier, rather than merely
choosing a convenient representation of the same witnesses.

## 2. Exact finite witness formulation

The rest of this note is our deduction for certificate design.

Suppose the input is a Boolean rectangle p of width a and height b,
specifying the target configuration

    x(i,j)=p(i mod a,j mod b).

Define a predicate by the following finite existential data:

    M,N>=1 with a dividing M and b dividing N;
    a Boolean rectangle z of width M and height N;
    for every 0<=i<M, 0<=j<N,
       Life(z on the M-by-N torus)(i,j)=p(i mod a,j mod b).       (1)

Both horizontal and vertical coordinates in the Life neighborhood are
reduced modulo M,N. In particular, the nine positions retain their
multiplicities if a period is one or two; they are the nine positions
in the infinite periodic extension, not a set of distinct torus cells.
One can instead repeat any witness until both dimensions exceed two.

Condition (1) is equivalent to existence of a totally periodic preimage.
One direction periodically extends z to the plane. Every neighborhood
then has exactly the wrapped values checked in (1), so its image is x.
For the other direction, choose rectangular periods u,v of a periodic
preimage and repeat it over M=lcm(a,u), N=lcm(b,v). These are also
periods of the target. Its restriction to this common rectangle gives
a witness of (1). A full-rank period lattice always contains some
horizontal and vertical period, so using rectangular periods loses
no totally periodic configurations.

This is an unbounded finite witness. The preimage period is not required
to equal the supplied target period. Restricting M=a,N=b would make
the search finite with a computable size bound and would define a
different, decidable problem. The same issue applies to any proposed
computable bound on witness dimensions.

There is only one Life update in (1). The second spatial coordinate
can carry the constraints of an entire simulated computation. Therefore
the predicate itself requires no separately existential duration of
Life evolution, initial Life row, or Life halt-event pattern. This is
the genuine interface advantage over a forward-history proposal.

## 3. Why the other quantifiers do not substitute for (1)

For arbitrary infinite preimages of a fixed computable target, the
compactness formulation is

    for every finite radius R, there exists a preimage of the
    target restriction to that radius.                            (2)

Each individual finite search is decidable. Nevertheless, a successful
finite patch need not extend to the whole plane, and no one such patch
witnesses (2). A finite existential Diophantine system has a recursively
enumerable set of positive instances, because its integer tuples can
be enumerated. Thus the Pi^0_1-complete positive problem cannot simply
be substituted as that system's semantics.

Taking its complement changes the issue: failure of extension has a
finite obstruction, but certifying that a patch has no preimage requires
a proof of a finite unsatisfiability claim. It is not the same task as
supplying one local Life assignment. A construction using that route
would have to account for its proof or verification mechanism.

Likewise, a finite target patch in a single inverse layer has a witness
whose domain is bounded by the input patch plus one-cell halo. Increasing
an unrelated ambient rectangle cannot create an unbounded computation
in that fixed predicate. The needed unboundedness in (1) comes from
the existential periods and their exact seam identifications.

## 4. Arithmetic obligations still outstanding

A certificate based on (1) would need all of the following in one
counted system:

* Encode the raw numerical query into a periodic target block p, or
  encode a proved reduction to such a block. Computability of that
  reduction does not make its arithmetic implementation free.
* Construct the variable rectangle geometry and enforce the required
  divisibility by the target periods. Literal constants may describe
  a fixed compiled program, but variable repetition lengths still cost
  operations and constraints.
* Prove Booleanity and ranges of the preimage and all auxiliary planes.
* Check all nine neighborhood positions at every cell, including both
  torus seams and their corner interactions, and compare the result
  with the repeated target word.
* Prove positive witnesses for auxiliary fields that can be zero in a
  valid periodic configuration.

The zero-first-column condition of the current Rule 110 components
cannot be carried over as a replacement for periodic boundaries. It
would impose a different local problem. Similarly, a simple cyclic
shift of a row-major word connects the end of one row to the next row,
not to that row's beginning. One must prove the intended two-dimensional
torus alignment rather than treat these different seams as equivalent.

Life's local rule is fixed, so a finite Boolean circuit for one
neighborhood can be compiled once. However, ordinary multiplication
of packed words remains a convolution, not a coordinatewise Boolean
operation. The existing mask, gate-splitting and geometric techniques
may help compress these local checks, but their costs have not been
established for this nine-cell torus problem.

The next concrete target is consequently an exact, counted torus
inverse-layer verifier with a faithful periodic target interface.
The source result gives this direction a valid existential acceptance
semantics; it does not yet give a shorter straight-line certificate.
