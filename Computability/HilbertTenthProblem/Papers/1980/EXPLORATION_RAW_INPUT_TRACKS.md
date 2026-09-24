# A counted raw-input interface and two concrete obstructions

This bounded investigation concerns variable input conversion for a
Boolean history verifier. It gives an exact parallel-track interface
and explains why two apparent free conversions do not work. It does
not supply a complete universal local rule or improve the published
universal certificate. Numerals are free; operations on a variable
input are counted.

## 1. The relevant primary-source input contracts

Korec defines strong universality by a fixed register machine receiving
an effectively chosen program index and the original numeric query,
with no query transformation. Registers initially contain those two
inputs and zeros elsewhere. His Main Theorem includes a strongly
universal 22-instruction machine with increment and conditional
decrement instructions. This is a suitable source contract for a
verifier that must accept the raw number x.
[Korec, 1996, pp.267-268 and Definition 2.3](https://www.cs.cmu.edu/~cdm/resources/Korec1996-small-universal-RM.pdf).

Neary's binary-tag simulation uses fixed-length objects for the
simulated symbols. A further boundary matters: in the displayed
halting modification, Table 2 stores the simulated input in a track
of the production word u, and the length of u also depends on input
length. Consequently that displayed reduction does not make u a
fixed numeral independent of a varying query. It is not a theorem
that no fixed binary tag system can have a useful alternative input
contract; it is a limitation of using this particular construction
as a cost-free input loader.
[Neary, STACS 2015, Section 3.1, Lemma 9 and Table 2, pp.652-656](https://drops.dagstuhl.de/storage/00lipics/lipics-vol030-stacs2015/LIPIcs.STACS.2015.649/LIPIcs.STACS.2015.649.pdf).

Conway's FRACTRAN semantics uses the first fraction that produces an
integer and stops when none applies. Its universal interpreter uses
encoded numerical inputs. The obstruction in Section 4 below is our
deduction about this stopping predicate, not an extra claim made by
Conway's universality theorem.
[Conway, FRACTRAN, 1987, pp.4-5](https://gwern.net/doc/cs/computable/1987-conway.pdf).

## 2. An exact raw-number interface using parallel Boolean tracks

Fix R=2^k with k>=2. Supply k nonnegative words I0,...,I(k-1), each
proved Boolean in radix R, and impose the single integer equation

    x=I0+2*I1+4*I2+...+2^(k-1)*I(k-1).                 (1)

This is a unique representation of every nonnegative integer x.
Writing its ordinary binary expansion as x=sum_j epsilon_j*2^j,
the unique words are

    Ii=sum_l epsilon_(kl+i)*R^l, 0<=i<k.               (2)

To prove uniqueness from the source equation, every raw radix-R
coefficient on its right is between zero and
1+2+...+2^(k-1)=R-1. Hence there is no radix-R carry. Each digit of
x is exactly the binary number formed by the k corresponding track
bits, and those k bits are unique. Formula (2) proves existence.
Padding all tracks with high zero digits changes none of their
values. If x<q=R^m, each Ii<q automatically.

The source equation costs k-1 multiplications by fixed numerals and
k-1 additions, followed by a free equality test. In particular:

| Radix | Tracks | Input-link operations |
|---|---:|---:|
| 4 | 2 | 2 |
| 8 | 3 | 4 |
| 64 | 6 | 10 |
| 128 | 7 | 12 |

This is an existential integer relation, not an instruction sequence
that computes the witnesses by extracting bits. Booleanity, track
alignment and any overall input bound must be provided by the
surrounding history system. In particular, the counts in the table
exclude a fresh independent Boolean mask.

Zero tracks are possible. A generic strictly positive representation
Ii=ai-1 costs k additional subtractions. If the surrounding system
instead already certifies native fields Fi=J+2Ii with all digits one
or three and J=(q-1)/(R-1), their direct input relation is

    F0+2*F1+...+2^(k-1)*F(k-1)=(q-1)+2x.             (3)

When q-1 is already computed by the geometry, (3) costs 2k
operations: the 2(k-1) weighted-sum operations and two operations
for the right side. It uses the native positive fields directly.
The global shifted mask, individual field bounds and the construction
of any missing geometric registers remain separate costs.

### A concrete machine convention that can use these tracks

Place the k track bits for one radix-R input digit at the same
physical tape position. An ordinary binary-tape machine can be
represented on such a grouped tape by adding a finite offset
i in {0,...,k-1} to its control state. Reading or writing a virtual
bit selects track i. Moving to the next bit changes i; at a block
boundary it also moves the physical tape head by one position.
Thus the initial grouped tape given by (1) represents exactly the
ordinary binary input x, with no external dilation. Any preparation
of a register representation or of a fixed interpreter format can
take place inside the finite computation being verified.

This is a concrete finite-state compilation convention. It does not
mean that the current Rule 110 or inverse-Life verifier already has
those input tracks. A full candidate must supply and count the
grouped machine's control/state constraints, its initial head and
program, its boundaries, and a finite halt event. In particular,
appending these tracks to the current 80-operation Rule 110 relation
would not prove that its single-stream initial configuration simulates
the grouped machine. The useful result is the exact small interface
(1), which is available when choosing a suitable local machine.

## 3. Scalar digit dilation is not a fixed arithmetic computation

For comparison, define the usual dilation

    delta_k(x)=sum_j epsilon_j*(2^k)^j,
    x=sum_j epsilon_j*2^j.

No fixed straight-line computation using only numeral constants,
x, addition, subtraction and multiplication computes delta_k(x)
for every nonnegative integer x when k>=2. Indeed, its output would
be a polynomial f(x). For every n>=0,

    f(2^n)=delta_k(2^n)=2^(kn)=(2^n)^k.

The polynomial f(x)-x^k has infinitely many roots, so f=x^k. But
delta_k(3)=2^k+1<3^k, a contradiction. The same argument even
excludes a fixed rational-function computation defined on all these
inputs: clear its denominator before using the infinite roots.

This is a lower bound only for direct functional arithmetic circuits.
It does not exclude short existential Diophantine relations with
additional witnesses, a counted digit mask, or a supplied variable
exponent. Parallel tracks avoid this obstruction by changing the
machine's input layout; they do not compute the missing single
dilated word.

## 4. Bare FRACTRAN halting cannot provide a raw scalar loader

Let a fixed FRACTRAN program contain reduced fractions a_i/b_i,
and let S be the finite set of primes occurring in their numerators
or denominators. The complete chosen-fraction sequence and its
halting behavior depend only on the vector

    (v_p(n):p in S)                                   (4)

of the starting integer n. To see this, write n=n_S*u where n_S
has only primes in S and u is coprime to every prime in S. A
denominator b_i divides n precisely when it divides n_S. The
selected fraction changes only n_S, while u is preserved. Induction
proves the assertion for the whole computation, including the first
time no fraction applies.

In particular, direct initialization n=x cannot give every raw-input
halting language. If it halts at x=1, it halts at every positive x
coprime to the finitely many primes in S, so it cannot recognize
the singleton {1} by bare halting.

The obstruction persists for an arbitrary fixed polynomial loader
n=F(x) produced by a finite arithmetic circuit, where only positive
values are valid initial states. If F(x0)>0, put

    M0=product_(p in S) p^(v_p(F(x0))+1).

For every x=x0+M0*t, polynomial congruence gives
F(x)=F(x0) modulo each p^(v_p(F(x0))+1). Thus the valuations (4)
are unchanged whenever F(x)>0, and the program has exactly the
same halting behavior. An infinite accepted language requires F to
be positive eventually; otherwise a nonzero polynomial is positive
at only finitely many positive integers. Every sufficiently large
accepted point therefore lies in a whole infinite accepted arithmetic
progression. The constant-polynomial cases have the same conclusion
or accept nothing.

For example, such a loader and a bare FRACTRAN halt test cannot
recognize exactly the positive powers of two: every infinite
arithmetic progression contains integers that are not powers of two.
Consequently this architecture cannot be strongly universal on raw
numeric inputs, even though FRACTRAN with its encoded inputs is
universal. The claim allows a different fixed program and polynomial
for the desired set; their finite prime set still gives the argument.

The scope is important. A separate terminal-value test, extra input
witnesses, or an exponential loader such as n=2^x changes the
architecture. Those mechanisms can distinguish inputs that bare
halting ignores, but their arithmetic must be counted. This is an
obstruction to a specific cheap replacement for input encoding, not
to all FRACTRAN-based Diophantine verifiers.

## 5. Why the existing exponential cannot simply be tied to x

The retained kernel proves U=2^(2r+1), with r determined by the
packed word and its length. In the existing history interfaces it
also gives q^d dividing U for a fixed positive d. Replacing its
exponent by a fixed affine expression in the query x would impose
a computable upper bound on q for each fixed x. The packed word,
its row geometry and all bounded Boolean traces would then range
over a finite computably bounded collection. For these proved
interfaces, whose Pell witnesses have explicit positive converses,
one could decide acceptance by enumerating that collection. It
cannot provide an arbitrary recursively enumerable input predicate.

Leaving an additional unbounded term in the exponent avoids that
finite bound, but it does not by itself recover a separate value
2^x. For example, separating 2^(x+h) into its x-dependent factor
requires a relation defining the h-dependent factor, or a justified
modular extraction. Reduction modulo q-1 only reads the exponent
modulo log2(q), whose numerical value is not supplied by the implicit
power geometry. This is a precise missing interface, rather than
a new zero-cost use of U.

## 6. Focused verification and status

`../verification/explore_raw_input_tracks.py` verifies complete small
track decompositions and their uniqueness, the native-field input
identity, the explicit operation counts, direct dilation examples,
and finite FRACTRAN trajectories with unchanged outside prime
factors. It also checks polynomial-loader arithmetic progressions
against the program's prime valuations. The general proofs above
establish the unbounded assertions; the finite checks only corroborate
them. No complete local universal-machine certificate is claimed.
