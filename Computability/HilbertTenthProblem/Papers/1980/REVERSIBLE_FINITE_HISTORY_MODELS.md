# Reversible finite-history models: a bounded arithmetic audit

Status: research only. The proved universal certificate remains 90 operations.
Fixed numerals are free; arithmetic on packed words is counted. The useful new
component below is a six-operation Toffoli relation, not a universal certificate.

## 1. Three concrete models and their actual interfaces

| Model | What the primary source establishes | Consequence for this project |
|---|---|---|
| Morita's two-dimensional partitioned CA `P3` | Four ternary ports per cell, hence 81 states; a reversible counter machine can be embedded in a finite configuration. | The strongest finite-input starting point found in this bounded search. The counter value is spatial displacement, and the 81-state transition still needs an arithmetic compiler. |
| Fredkin--Toffoli billiard-ball/conservative-logic model | Reversible gates and circuit simulation using moving signals, collisions, and reflectors. | The cheap local gate is useful, but circuit universality alone does not supply the required fixed-machine, finite-input halting interface. |
| The one-dimensional Toffoli CA in Arrighi--Nesme--Werner | A four-symbol, radius-half reversible CA over finite configurations, with local rule `(a,b),(c,d) -> (b XOR ac,c)`. | Its rule has the cheap relation below. The cited paper proves structural properties, not computational universality; it cannot be substituted for the existing universal machine on that evidence. |

For `P3`, the original source gives 13 rotation schemes representing all 81
transitions and embeds the two-state rotary element in this CA. Its conclusion
explicitly distinguishes the finite counter-machine embeddings from earlier
small reversible gate lattices requiring infinite configurations.
See Morita, *A Simple Universal Logic Element and Cellular Automata for
Reversible Computing* (2001), sections 4--5 and Figure 9
([primary paper](https://www.cs.auckland.ac.nz/~cristian/UMCreadings/revcomputCA.pdf)).
The author's later presentation illustrates the movable counter markers and
the finite control layout
([institutional primary presentation](https://hiroshima.repo.nii.ac.jp/record/2000032/files/Univ_RCA_Morita.pdf)).
The diagrams on presentation pages 5--6 were inspected directly; the exponent
in `3^4` must not be read as the number 34 by PDF text extraction.

Fredkin and Toffoli explicitly discuss the role of an indefinitely extendible
tape or quiescent environment in supplying blank resources and receiving
garbage. A finite conservative circuit is not by itself this unbounded store.
Their billiard-ball construction appears in section 6; the resource distinction
is in section 4
([*Conservative Logic*, 1982](https://www.cs.princeton.edu/courses/archive/fall05/frs119/papers/fredkin_toffoli82.pdf)).
The third model is Definition 12 and Figure 5 of
[*One-dimensional quantum cellular automata over finite, unbounded configurations*](https://arxiv.org/pdf/0711.3517).
No universality theorem for that particular CA is asserted here.

One tempting alternative should be excluded early: Morita's 24-state
one-dimensional RPCA and the associated 96-state number-conserving CA use
infinite ultimately periodic configurations in the universality construction,
even in the direct finite-Turing-input simulation described in section 3
([Morita 2012](https://arxiv.org/pdf/1208.2760)). A finite witness rectangle would
have to verify the background generator as well as the input.

## 2. A six-operation local relation that really packs

The following is our arithmetic derivation. Let `A,B,C,Cprime,U,V,W` be
nonnegative integers with only digits zero and one in base four. Impose

    A+B = V+2U,
    U+C = Cprime+2W.

Every raw coefficient on either side is between zero and three. Thus equality
of integers is exactly equality at every digit position, with no carries.
For single digits the first equality gives `u=ab` and `v=a XOR b`; the second
gives `cprime=c XOR u` and `w=uc`. These are precisely a Toffoli gate's target
update, with the controls unchanged. The Toffoli gate convention is also
described in [Toffoli's original reversible-computing paper](https://cqi.inf.usi.ch/qic/80_Toffoli.pdf).

The primitive schedule is

    ab_sum=A+B; two_u=2*U; rhs1=V+two_u;
    uc_sum=U+C; two_w=2*W; rhs2=Cprime+two_w;

with the two free comparisons `ab_sum=rhs1`, `uc_sum=rhs2`.
This is **six operations: two multiplications and four additions**.
It is one operation below our current seven-operation Rule 110 local
relation. This is a component comparison, not a net whole-history saving.

All Boolean hypotheses matter. For example, the second equality accepts
`U=4,C=0,Cprime=0,W=2` if the Boolean condition on `W` is omitted, although
the correct target word is four. Positivity or an ordinary upper bound does
not repair this carry alias. Zero Boolean planes are also allowed here;
turning them into positive supplied witnesses may cost arithmetic.

For comparison, a single Fredkin gate has the scalar four-operation formula

    t=s*(b-a); x=a+t; y=b-t.

It does **not** lift to packed integers: multiplication convolves different
positions. For `S=1,A=0,B=4`, the formula swaps a bit at a position where the
control is zero. A valid packed construction instead computes the two
digitwise ANDs through

    S+A=P+2U, S+B=Q+2V,
    X=A+(V-U), Y=B-(V-U).

With Boolean planes this costs **nine operations: two multiplications and
seven additions/subtractions**. Neither figure includes wiring or the shared
Boolean predicate.

The accompanying exact regression checks all 128 assignments of the seven
Toffoli bits, all 512 three-position inputs, all scalar Fredkin inputs, and
the two explicit packing obstructions. It establishes these local claims
only; it does not verify a universal automaton or a history boundary.

## 3. A candidate history interface and the obligations it leaves

A rectangular Toffoli history could store aligned control words `A,B` and
target word `C`, with `Cprime` obtained from the next time slice. Apply the
two displayed equalities to every gate occurrence at once. The unchanged
control outputs can be identified with the corresponding next inputs.
For a fixed partitioned lattice, this replaces the transition table by six
primitives independently of the number of gates or time steps.

The following work is still necessary before this becomes a faithful
finite-halting certificate.

1. **Uniform wiring and time alignment.** A witness cannot freely choose which
   gate receives which previous output. The partition phase, spatial shifts,
   and next-row relation need explicit arithmetic equations. `Cprime` can be
   a derived shifted view of `C`, reducing independent masked planes, only
   after those equations have been proved. A list of arbitrary gate records
   could manufacture an accepting circuit unrelated to the program.
2. **A strongly universal finite layout.** Morita's `P3` supplies the right
   finite-counter simulation, but no six-operation realization of its full
   local rule has been obtained. Conversely, the cheap Toffoli CA above has
   no established universality interface in the cited paper. A compilation
   from a reversible machine to a repeated programmable Toffoli lattice must
   retain unbounded blank workspace and verify its initialization.
3. **The raw integer input.** Encoding a counter initially equal to `x` by a
   marker at spatial displacement `x` introduces a term such as `4^x` in a
   positional configuration code. That conversion is not a free numeral.
   A possible alternative is a binary loader inside the simulated machine.
   At the arithmetic interface, `x=I0+2I1` reads the two binary digits in
   each base-four place using two operations, provided both input planes are
   Boolean. This is only an input representation, not a constructed loader.
4. **Unbounded but finite boundaries.** A radius-one finite run can be enclosed
   in a rectangle whose zero halo grows with the witnessed time. The
   equations must prevent incoming signals and wraparound. The rectangle
   cannot have an a priori height bound computable solely from the raw input
   unless such a bound is compatible with the intended universal semantics.
5. **Halting observation.** Reversible dynamics should expose a distinguished
   halt signal or state. Requiring the entire configuration to become a fixed
   point cannot express first arrival there under an injective transition.
   Initial zero ancillas and the observed halt flag must both be checked;
   arbitrary garbage cannot be allowed to impersonate an initial flag.

The best next experiment is therefore narrow: compile one finite-input
reversible machine into a fixed partitioned Toffoli layout with an explicit
binary loader, then count its packed wiring and boundary equations together
with these six local operations. `P3` is the source to use if the finite-input
semantics prove harder than the local arithmetic. No sub-90 claim follows
from this audit.
