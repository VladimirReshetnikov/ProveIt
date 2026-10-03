# A fully enumerated finite mode closure and numerical quadratic step packet

## Result and boundaries

The least ordered-label closure of the literal 114-label, 445-rule, 18-particle
machine contains **49,700 modes and 80,501 event branches**. The work queue was
exhausted. This is not a finite-depth sample; the largest shortest graph depth
is 321. There are 65,557 one-collision and 14,944 two-collision branches.

This is the exact closure for the stated *mode-only* transition relation. It
is a finite overapproximation of modes numerically reachable from the encoded
loader. Different edges of a mode path can require incompatible geometries;
we do not assert that every graph path is realized by a single input. Every
actual encoded execution, including all simultaneous events, is preserved.
The full graph is small enough to enumerate; its canonical quadratic packet
has millions of variables, and its fully expanded polynomial has over a
trillion monomials. No fixed-arity unbounded-history compression follows.

The numeric data and exporter are complete. `RESIDUALS.jsonl.gz` was actually
emitted and contains every affine coefficient in the squared-residual packet.
The compact distribution omits that 46 MiB expansion and the redundant 24 MiB
verbose branch file; both can be regenerated. It does not claim to distribute
or to have emitted the trillion-term monomial expansion.

## 1. Closure definition and proof of completeness

For each ordered 18-label mode a, let c_i=v(a_i)-v(a_(i+1)), i=0,...,16.
An edge i is eligible exactly when c_i>0 and the literal collision table has
the incoming pair {a_i,a_(i+1)}. For every nonempty subset J of eligible
edges with no consecutive indices, replace all those pairs atomically by
their prescribed outputs in strictly increasing speed order. No other label
moves. Every such J is included, with pivot j=min J.

The breadth-first algorithm begins with the fixed literal initial order,
adds every newly found successor, and processes every queued mode. It stops
only when the queue is exhausted. Every added mode has an explicit path
from the initial mode; every successor of every final mode is included.
Thus induction gives both inclusions with the least mode-only closure.
Termination is formally bounded by 114^18 modes; the implementation also
has a 500,000-mode resource cap that raises an error rather than claiming
completion. The successful run finishes far below the cap. An independent
recursive matching enumerator verifies the same complete modes and edges.

Every genuine defined next event of a two-input/two-output machine consists
of disjoint adjacent collision pairs. Their incoming speeds descend, each
pair has a literal rule, and every earliest pair must occur in J. Consequently
the genuine successor is among those enumerated. Induction preserves every
encoded run. An adjacent pair of selected edges would instead be a triple
collision, which has no rule in this literal table and is correctly excluded.
There is no unspecified identity completion.

## 2. Every enumerated edge is feasible for some strictly positive geometry

For any enumerated (mode,J), choose an integer initial gap vector

    h_i = c_i                  if i belongs to J
    h_i = max(c_i,0)+1         otherwise.

All h_i are positive. At time tau=1, precisely the selected gaps vanish:
for i in J, h_i-c_i=0; otherwise h_i-c_i is positive. Every gap remains
positive before tau. Thus all selected collisions are earliest and exactly
tied, all other particles remain separate, and the prescribed disjoint
2-to-2 rules are legal. Sorting outgoing pairs creates valid outgoing germs.
This construction is checked for all 80,501 branches using exact integers.

The quantifiers matter: every candidate J works for *some* positive gaps.
It is false that every positive gap choice realizes every J; changing one
closing gap generally changes its collision time. No numerical LP
feasibility claim is used.

## 3. Complete guards, including zero-gap outgoing germs

The arithmetic state is X=(h_0,...,h_16,u) in N^18 and S=sum h_i. The mode
code is q=1+sum(label_index(a_i)*114^(17-i)), using the literal sorted labels.
For a branch with q_old,q_new,J,j,c_j, the guards are:

- Equality u-q_old*S=0
- Equalities c_j*h_i-c_i*h_j=0 for i in J except j
- Strict h_i>0 for every c_i>=0
- Strict S>0 and h_j>0
- Strict c_j*h_i-c_i*h_j>0 for every i outside J

The omitted pivot equality is the zero polynomial. The explicit span and
positive-delay guards are retained even though some other guards imply them.
All weak gap inequalities are supplied by the ambient natural-number domain,
so W=0. For c_i<0, h_i=0 is allowed: these are correctly ordered expanding
outgoing germs. If c_i>=0, the strict gap guard forbids zero-time recollision
and equal-speed coincidence. Hence the germ condition is exact.

The affine endpoint forms state that precisely J vanishes at tau=h_j/c_j.
At every earlier positive time all adjacent gaps are positive. Strict guards
on *all* nonselected edges exclude omitted ties and any omitted third arrival,
including encounters without a rule. They do not merely compare the eligible
pairs. Nonpositive c_i are retained in these full endpoint comparisons.

For a fixed admissible state the complete earliest set J is unique, and
S>0 makes the mode codes distinguishable. Thus branch domains are disjoint.
The matrix is N_j=c_j I-c e_j^T on the 17 gaps, with row j zero, rank 16,
N_j^2=c_j N_j, at most 32 nonzero entries, and coefficient magnitude <=24.
The last row is q_new times the column sums of N_j; the input u column is
zero. Every active source mode in the enumerated closure has stationary
endpoints, which is explicitly checked; its last row therefore contains
c_j*q_new in every gap column. This endpoint fact is not presumed for the
36 collision-free escaped modes, which have no outgoing event branches.

## 4. Literal numerical ledger

The fixed d=18 frontend yields:

- B=80,501 branches
- E=95,445 equality guards
- T=2,667,479 strict guards; W=0
- B(d+1)+T=4,196,998 auxiliary natural variables
- 4,197,034 total variables including X,Y
- 1+2d+E+T=2,762,961 affine squared residuals
- 80,501 nonnegative complementarity products
- 15,323,489 affine variable-coefficient entries and one affine constant
- 1,479,509 total gap-matrix entries; 2,848,026 full matrix entries
- Maximum mode code 475451290367006497995199791576174838 (119 bits)
- Maximum affine coefficient magnitude
  11372800035259304801214410999907194640 (124 bits)

A branch with g=# {i:c_i>=0} has |J| equalities and g+19-|J| strict guards.
Here g is 16 on 25,890 branches and 15 on 54,611 branches. The speed/pivot
and guard histograms are in `LEDGER.json`.

Variable indexing is explicit in `POLYNOMIAL_CIRCUIT.json`: X indices 0..17,
Y indices 18..35; selectors next; then 18 input-copy coordinates per branch;
then strict slacks in literal guard order. All intervals in that file are
half-open. Numeric coefficient strings avoid JSON floating-point rounding.

## 5. Polynomial and canonical witnesses

For branch r, introduce b_r in N, a natural copy X_r in N^18, and one slack
s_(r,k) for each strict guard. Square these affine residuals:

    sum b_r - 1
    X_i - sum_r X_(r,i)                         (18 rows)
    Y_i - sum_r (M_r X_r)_i                     (18 rows)
    L(X_r)                                     (each equality)
    L(X_r) - b_r - s_(r,k)                      (each strict guard).

Add the polynomial products

    sum_r [ (sum_(a != r) b_a) * sum_i X_(r,i) ].

The circuit shares the literal expression selector_sum=sum b_r and writes
selector_sum-b_r inside each product. This is an algebraic abbreviation for
a sum of other natural selectors, **not a new unconstrained variable**.
Every square and every product is nonnegative on all natural assignments.
A zero forces exactly one selector to equal 1, all other copies and their
slacks to vanish, the active copy to equal X, its strict guards to be >=1,
and Y to equal its matrix image. Conversely every valid step produces the
unique witness: its unique active branch and slacks L(X)-1. This is an exact,
canonical, globally nonnegative, degree-two one-step polynomial.

## 6. Expanded coefficient counts, height, and exporter

Let H=17B, L=4,132,044 be the summed number of nonzero coefficients in the
strict forms, and M=2,848,026 the full matrix-entry count. Distinct quadratic
monomials separate into disjoint categories:

    all local gap pairs                  H(H+1)/2
    all local control-copy pairs         B(B+1)/2
    within-branch gap/control pairs       17B
    external X,Y squares                 36
    external X/local-copy pairs          18B
    external Y/local-gap pairs           M
    all selector pairs                   B(B+1)/2
    selector/inactive-copy pairs         18B(B-1)
    selector/own-gap pairs               17B
    selector/slack pairs                 T
    local-gap/slack pairs                L
    slack squares                       T.

All gap-pair coefficients are nonzero: their common output-mode contribution
is positive and dominates every possible small signed gap-matrix term.
Within a branch, the mode equality adds another positive q_old^2 term.
The selector/own-gap coefficients cannot cancel: summing the strict forms
gives positive coefficients on all 17 gaps, using sum c_i=0. The local
control-copy diagonal coefficient is 2, one from the global input residual
and one from its mode equality; off-diagonal control-copy coefficients are
also 2. This fact is explicitly tested.

The resulting expanded polynomial has 1,059,563,015,521 quadratic nonzero
monomials, 80,501 linear nonzero monomials, and one constant:
**1,059,563,096,023 nonzero monomials in total**. The maximum absolute
coefficient is

    259133269143011392111352351966853298220157195726258486219937575989578112842

and has 248 bits. Here coefficient bit height means the bit length of the
absolute integer magnitude; a separate sign bit is not included.

For each branch, write w=c_j*q_new. The largest within-branch gap cross-term
is exactly 2*(w^2+q_old^2+1+2*c_j*max(0,-min c_i)). Taking its maximum gives
the displayed number, at branch 79,695. Every cross-branch coefficient is
bounded by 2*w_max^2+19,586, strictly less than that number; all remaining
coefficient families are smaller as well. This proves the exact height
without materializing a trillion coefficients.

The compiler emits all sparse affine coefficients and can query any fully
expanded coefficient by variable indices. It also implements a complete
streaming expanded-monomial exporter with bounded working memory and no
repeated monomials; it is disabled by default behind an explicit flag because
its output is intrinsically enormous. Three small packets (B=1,3,5, including
a simultaneous branch and the maximal-height branch) were fully expanded by
an independent sum-of-squares routine; every coefficient and every zero query
agrees with the streaming exporter. The full trillion-term export was not run.

## 7. Target, dead ends, exact replay and reproduction

There are 1,728 modes with no eligible pair, of which 1,692 have a forbidden
future collision and 36 are collision-free. The collision-free modes include
six accepting-label and thirty null-label modes caused by the broader
mode-only geometry. The encoded-run acceptance test remains the single
original `q_accept_final`, not their union. Its BFS mode ID is 6198; the
original null-final mode ID is 7508. Initial mode ID is 0. The literal decimal
codes in the machine JSON are unchanged.

All five original complete signal runs were replayed through this compiler:
13,798 event batches, 13,798 equality guards, 463,909 strict guards, 13,793
zero input gaps and 2,713 distinct branches used. These five trajectories
contain no simultaneous batches; simultaneous handling is instead verified
by the constructive all-branch witnesses and independent closure audit.
The original tape/controller comparisons and exact lift checks also pass.

Compact public data:

- `MORITA_18_SIGNAL_MACHINE.json`: unchanged literal machine and loader modes
- `MODES.jsonl.gz`: every mode ID, ordered label indices, q,c, and BFS depth
- `EVENTS.jsonl.gz`: [branch ID, source ID, target ID, pivot, J bitmask]
- `LEDGER.json`, `POLYNOMIAL_CIRCUIT.json`: numerical packet and indexing
- `compile_packet.py`: complete regeneration, coefficient queries/export
- `test_exporter.py`, `EXPORTER_TEST_RECEIPT.json`: small-packet exact audit
- `check_original_replays.py`, `ORIGINAL_REPLAY_AUDIT.json`: original event audit

Optional binary encodings are `MODES.bin` (18 one-byte labels per mode) and
`EVENTS.bin` (little-endian source,target,Jmask, three unsigned 32-bit values
per branch). They are redundant and need not be distributed.

Commands:

    python compile_packet.py verify
    python compile_packet.py build
    python test_exporter.py
    python check_original_replays.py /path/to/original-source-or-release-root
    python compile_packet.py residuals --output RESIDUALS.jsonl.gz
    python compile_packet.py coefficient 36 36

`verify` reads every compact archived record, compares it with a freshly
exhausted closure, and checks every constructive branch witness. It is read-only.
`build` regenerates the complete closure and verbose branch export. It does
not expand residuals unless `--residuals` is added. The `residuals` command
emits the full sparse affine row coefficients. For the trillion-term full
polynomial export, the explicit command is `expanded --allow-trillion-terms
--output EXPANDED.jsonl.gz`; do not run it without budgeting the huge output.
