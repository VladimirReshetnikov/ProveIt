# Arithmetic machines as an alternative to the 90-operation compiler

This bounded research note compares three concrete machine families by the
cost of an existential certificate for a **finite halting computation**.
It changes no published certificate and claims no bound below 90. Fixed
numerals are free; multiplication by a fixed numeral, input conversion,
digit extraction, divisibility, and variable powers still require counted
arithmetic. The conclusions about prospective certificate cost below are
our analysis, distinguished from the cited universality results.

## 1. The three strongest candidates

### FRACTRAN, with its formalized Diophantine translation

A program is an ordered finite list of rational fractions. At a positive
integer state it uses the **first** fraction producing an integer, and it
halts when none does. Conway constructs a fixed universal interpreter;
its universality uses encoded inputs, not a promise that the queried raw
integer is already the simulated register value. See
[Conway, FRACTRAN (1987), Theorem 3 and Sections 6--10](https://www.cs.cmu.edu/~cdm/resources/Conway1987-fractran.pdf).

The most directly reusable modern source is
[Larchey-Wendling and Forster, Hilbert's Tenth Problem in Coq, LMCS 2022](https://arxiv.org/pdf/2003.04604).
Theorem 6.3 preserves finite halting under a prime-power encoding of
Minsky configurations. Sections 7 and 2.4 separate a short Diophantine
one-step predicate from the difficult reflexive-transitive closure;
the latter explicitly uses exponentiation and bounded universal
quantifier elimination. Its code is linked in the paper. This gives a
formal source from which to extract arithmetic, but not an operation
count competitive with our current certificate.

Our assessment: FRACTRAN is the cleanest reference semantics for a new
history compiler. Its single numerical state is helpful, but the priority
tests, terminal condition, and prime-power input conversion are costs to
retain. Simply multiplying the chosen fractions forgets their order.

### Strongly universal counter/register machines

[Korec, Small universal register machines (1996), Main Theorem and Definition 2.3](https://www.cs.cmu.edu/~cdm/resources/Korec1996-small-universal-RM.pdf)
distinguishes strong universality from versions allowing total input and
output recodings. In the strong version, an effective program code is a
fixed first input and the second input is the actual queried natural
number. The paper constructs a strongly universal 32-instruction machine
using increment, decrement and positivity tests; smaller counts use
different instruction bases or weaker coding conventions. The 14-instruction
result must not be identified with a 14-operation arithmetic verifier.

Our assessment: this is the best starting point if avoiding a new
exponential conversion of x is the priority. Counter changes are only
0,+1,-1, so entire histories have particularly simple linear transport
equations. Zero tests and control-state synchronization remain nonlinear
conditions on the digits of those histories. A two-counter simulation is
not automatically better: numerical input coding and a larger control
table can erase the saving in the number of history columns.

### Generalized Collatz / residue-affine maps

[Kurtz and Simon, The Undecidability of the Generalized Collatz Problem (2007), Sections 1--3](https://people.cs.uchicago.edu/~simon/RES/collatz.pdf)
uses maps whose rational affine formula depends on the input's residue
modulo a fixed modulus. The machine simulation supports finite reaching
of a designated value on encoded inputs. Their principal strengthened
result instead concerns **all** initial values eventually reaching 1,
a Pi-2 complete property. That global statement is not the existential
finite-history predicate needed here.

Do not conflate residue partitions with finitely many ordinary intervals.
[Ben-Amram, Mortality of iterated piecewise affine functions over the integers, STACS 2013](https://drops.dagstuhl.de/storage/00lipics/lipics-vol020-stacs2013/LIPIcs.STACS.2013.514/LIPIcs.STACS.2013.514.pdf)
distinguishes these settings: the integer one-dimensional polyhedral
piecewise-affine mortality problem is decidable, whereas the relevant
undecidability appears in dimension two. A superficially similar update
syntax therefore need not supply the same universal machine.

Our assessment: affine branches make useful history identities, but a
large residue modulus is not a free table lookup. Enumerating every
residue can turn a short fraction list into many arithmetic branches.
No verified two-branch universal Collatz map with the required raw-input
interface has been obtained in this audit.

## 2. A precise obstacle to dropping FRACTRAN priority

For reduced positive fractions a_i/b_i, one permitted selected transition
must satisfy

    b_i*y=a_i*x,
    b_j does not divide x for every j<i.

The terminal state must make every fraction inapplicable. A single
equation b_i*y=a_i*x costs two generic constant multiplications, but
this is only the arithmetic update. For example, the list [3/2,1/3]
at x=6 must go to 9; selecting the integral later update 6->2 is wrong.

There is a structural reason not to replace the ordered program by
arbitrary fraction choices. With finitely many primes, its prime-exponent
vectors then form a vector-addition/Petri-net system: enabling requires
the resulting exponents to be nonnegative, and a fraction adds one fixed
integer vector. Ordinary reachability in that model is decidable, as
established by
[Mayr's general Petri-net reachability algorithm](https://epubs.siam.org/doi/10.1137/0213029).
This observation does not rule out useful specialized representations;
it rules out treating the lost priority/zero-test mechanism as harmless.

## 3. A concrete history identity worth testing

Here is a direct algebraic idea, not a complete certificate. Consider a
finite run of a counter machine with counter values z_0,...,z_h. Let its
increment and decrement indicators at time t be I_t,D_t in {0,1}, so
z_(t+1)-z_t=I_t-D_t. Define polynomials

    Z(T)=sum_(t=0)^(h-1) z_t*T^t,
    I(T)=sum_(t=0)^(h-1) I_t*T^t,
    D(T)=sum_(t=0)^(h-1) D_t*T^t,
    Q=T^h.

Telescoping gives the exact identity

    (T-1)*Z(T)+z_0=T*(D(T)-I(T))+z_h*Q.       (H)

Every coefficient of (H) is exactly one local counter-update equation.
There is no multiplication of two history polynomials in this transport
identity. At an integer radix B, with Q=B^h supplied, its direct generic
schedule costs six operations per counter after the shared B-1:

    A=(B-1)*Z, L=A+z_0, N=D-I,
    P=B*N, E=z_h*Q, R=P+E, test L=R.

For a machine arranged to halt with that counter zero, E and the last
addition disappear, leaving four operations; a counter also initialized
to zero needs only three. These are exact transport counts, not counts
for a complete halting certificate. Arranging terminal cleanup changes
the machine and its control obligations; it is not silently free.

The same idea for a FRACTRAN run separates its histories by branch:

    X_i(T)=sum_(t: branch i used) n_t*T^t,
    Y_i(T)=sum_(t: branch i used) n_(t+1)*T^t.

It gives

    b_i*Y_i=a_i*X_i for every i,
    T*sum_i Y_i+n_0=sum_i X_i+n_h*Q.           (F)

For m fractions the straightforward transport-only schedule is 4m+2
operations: 2m coefficient multiplications, 2m-2 summation additions,
two boundary multiplications, and two boundary additions. Coefficients
equal to 1 can lower that particular count. At m=22 even this generic
transport already consumes 90 before any validity conditions; this is
an accounting observation, not a lower bound on every circuit.

Four obligations remain before either identity is an existential
arithmetic verifier:

1. Each supplied integer must encode the claimed bounded nonnegative
   coefficients; interpreting arbitrary integer digits as arbitrary
   signed polynomial coefficients permits carry cancellation.
2. Increment/decrement or instruction selectors must be Boolean,
   synchronized in time, and compatible with the finite control graph.
3. Zero tests, nonzero decrement guards, or FRACTRAN priority must hold
   at every selected time, with a genuine terminal state.
4. The histories must have a common finite end. Writing Q=B^h does not
   make that variable exponent a free operation.

There is an interesting possible way to address the last obligation
together with control. For a one-hot state-occupancy polynomial G and a
halting-selector polynomial H, coefficientwise flow satisfies

    (T-1)*G(T)=T*H(T)-1.

With the correct Boolean/support constraints this forces a finite
contiguous computation and a final halting marker; one need not start
by supplying its length. Establishing those constraints cheaply over
the integers is the missing theorem. The displayed scalar identity
alone permits arbitrary carries and is not a replacement for a power
predicate or a history-validity proof.

## 4. Recommended next bounded experiment

Extract a fixed strongly universal counter machine with an unencoded
input interface and normalize its halting state. Build the transport
equations (H), then work on one shared arithmetic certificate for the
selector/zero-test/control constraints. Count that shared verifier before
optimizing the machine's instruction count. In parallel, FRACTRAN is a
good formal specification against which to test equivalent priority
constraints, using the formalized transition relation rather than a
handwritten informal simulation.

A credible route below 90 would eliminate or substantially specialize
the existing exponent/binomial history machinery. Feeding a smaller
machine into the existing fixed-index coefficient compiler only changes
large constants and support sizes; those are already free in the user's
metric. The primary sources establish that the alternatives are sound
models of computation, but none of the sources audited here supplies a
complete below-90 straight-line certificate under that metric.
