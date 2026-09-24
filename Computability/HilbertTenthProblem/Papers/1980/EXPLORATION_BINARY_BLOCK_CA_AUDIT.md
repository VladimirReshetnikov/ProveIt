# Two-state block automata: exact tables and the finite-input gap

Status: bounded primary-source audit, not a new universal certificate. The
published universal bound remains 90 operations. A local circuit or a finite
history relation does not establish universality for a fixed finite initial
configuration with unbounded running time.

## 1. Two exact 16-case tables

Number a block by `a+2b+4c+8d`, with positions

    a b
    c d

Both models alternate the two usual Margolus partitions, whose origins differ
by `(1,1)`. The order and phase of these partitions belong to the global model.

The **billiard-ball cellular automaton (BBM)** has table

    input:  0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15
    output: 0  8  4  3  2  5  9  7  1  6 10 11 12 13 14 15

Thus it interchanges `(1,8)`, `(2,4)`, and `(6,9)` and fixes the other ten
blocks. Single particles move to the opposite corner; the two occupied
diagonals interchange. It is an involution, conserves the number of occupied
cells, and fixes the empty block. This table was transcribed from the original
rotational cases in Figure 4, printed page 86, of Margolus,
[*Physics-like Models of Computation* (1984)](https://fab.cba.mit.edu/classes/862.22/notes/computation/Margolus-1984.pdf).

The raw **Critters** table is

    input:   0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15
    output: 15 14 13  3 11  5  6  1  7  9 10  2 12  4  8  0

Blocks of weight two stay fixed. Blocks of weight zero, one, or four are
complemented. Blocks of weight three are complemented and rotated by 180
degrees. This is a permutation, but not an involution. It maps weight `s` to
weight `4-s`. Consequently its raw empty background alternates between all
zero and all one; the source's particle convention also alternates. This
phase must be represented when adapting the model to a quiescent-background
history interface. The table was transcribed from Figure 1.5, page 12, of
Margolus, [*Crystalline Computation* (1998)](https://arxiv.org/pdf/comp-gas/9811002).

The companion checker verifies all entries against these explicit case rules,
rotation covariance, bijectivity, and the stated population properties. This
finite verification checks the transcription and our arithmetic, not a
universality theorem.

## 2. What the universality sources actually supply

Margolus's 1984 sections 7--8 construct collision gates, reflectors, delays,
and circuit layouts in BBM. The argument translates billiard-ball circuits
into the cellular model. The 1998 section 1.5 similarly implements BBM logic
with Critters gliders and mirrors. These constructions do not themselves
provide a uniform finite-support initial configuration with an unbounded
blank store and an observable halting event. Conservation alone is not a
proof that such an interface is impossible: finite particles can in principle
store unbounded values in their separation. A new construction would have to
establish that interface.

The stronger-looking primary reference is Durand-Lose,
[*Computing Inside the Billiard Ball Model* (2002)](https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2002_BBM_book.pdf).
Its section 1.4 really does prove a two-counter simulation and then Theorem 2,
BBM universality. However, section 1.4.2, internal page 16, uses an infinite
line of logical register units. Each counter has unary form `1^n 0^omega`,
with both Boolean values represented by tangible dual-rail signals. The
register hardware and the blank tail are therefore not a finite perturbation
of the empty BBM configuration. This resolves the apparent shortcut without
disputing the paper's theorem. Its later intrinsic-simulation statement about
finite *simulated* configurations likewise does not assert that their BBM
encodings have finite support.

For **Salt**, Miller and Fredkin,
[*Two-state, Reversible, Universal Cellular Automata in Three Dimensions*
(2005)](https://arxiv.org/pdf/nlin/0501022), page 10 explicitly conditions
Turing-complete computation on infinite memory. Pages 11--12 use constant
signal streams; pages 14--15 discuss a non-exhaustible glider supply and do
not claim a completed universal-constructor proof. Salt also fails the
requested 16-case format: its three-dimensional, six-phase rule performs
controlled diagonal swaps, including a conflict guard, using cells beyond
one four-cell block. It is not a single permutation of four input bits.

This audit therefore did **not** locate the conjunction we need: a two-state,
four-cell permutation together with a proved strong finite-configuration
halting reduction. BBM and Critters supply the exact inexpensive state space;
the audited proofs leave the finite-support machine interface missing. Salt
adds neither the required interface nor the desired local format. This is a
source-boundary finding, not a theorem that no such two-state construction
exists.

Morita's `P3` remains the already-audited alternative with a finite
counter-machine embedding: four ternary ports, 81 states, and 13 rotational
schemes representing its table. See the separate
[reversible-model audit](REVERSIBLE_FINITE_HISTORY_MODELS.md) and Morita's
[2001 primary paper, sections 4--5](https://www.cs.auckland.ac.nz/~cristian/UMCreadings/revcomputCA.pdf).
Its stronger boundary theorem does not automatically make its arithmetic
table inexpensive.

## 3. A reproducible arithmetic baseline, not an optimized compiler

Here is a deliberately general local relation that does pack correctly. Let
the eight input/output bit planes and sixteen selector planes `E_k` be
Boolean digit words. Let `J` be the all-one word on the selected update
positions. For either permutation `f`, impose

    sum_k E_k = J,
    a+2b+4c+8d+16a'+32b'+64c'+128d'
        = sum_k (k+16f(k)) E_k.

In base 4096 the coefficients on the right sum to 2040, the left side is at
most 255 per position, and the selector sum is at most 16. There are no
carries. The first equation chooses exactly one table row per position; the
second then gives precisely that row's input and output. This is a linear
Boolean-auxiliary relation, not a use of integer multiplication as pointwise
Boolean AND.

An explicit, unoptimized schedule costs:

| Model | Multiplications | Additions | Total |
|---|---:|---:|---:|
| BBM | 22 | 36 | 58 |
| Critters | 23 | 37 | 60 |

The eight-term left side costs seven scalar multiplications and seven
additions. The selector sum costs fifteen additions. BBM has fifteen nonzero
table coefficients, costing fifteen multiplications and fourteen additions;
Critters has sixteen, costing sixteen and fifteen. Numerals are free. The
two comparisons are free. These totals exclude Boolean certification,
alignment between the alternating partitions, boundary conditions, raw-input
loading, and the halting observation.

This compiler is not competitive with the current kernel: its BBM local
cost alone plus the retained 43-operation Booleanity kernel already totals
101 before geometry. This is an upper bound for a particular compiler, not
a lower bound on the rule. No optimized short relation was proved in this
bounded audit. Any next attempt should address both the finite-input theorem
and the Boolean-auxiliary relation; a small permutation table by itself
settles neither.

Companion reproducibility files:
[checker](../verification/explore_binary_block_ca_tables.py) and
[receipt](../verification/explore_binary_block_ca_tables.json).
