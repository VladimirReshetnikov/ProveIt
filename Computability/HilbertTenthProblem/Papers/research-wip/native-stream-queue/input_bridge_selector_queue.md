# Native selector/FIFO composition: a 63-operation specialization

The reviewed [54-operation selector module](native_controller_three_selector_53.md)
can supply both the common native stream bounds and the time power for
the [six-operation queue transport](../../1980/EXPLORATION_NATIVE_STREAM_RAW_QUEUE.md).
One further multiplication supplies the queue-length power. Four fixed
trit-column projections cost at most eight additions/subtractions, giving
an exact finite three-label FIFO relation in **at most 69=33M+36A**.

A concrete specialization shares its two append streams and their
transport product, and costs **63=32M+31A**, with 29 strictly positive
existential coordinates and 21 equations. Its represented positive inputs
are exactly the ternary repunits `(3^ell-1)/2`, `ell>=1`. This is a
complete arithmetic statement about that small table, not a universal
computation certificate. The existing universal delayed loader does not
fit the fixed three-label projection interface, for two elementary reasons
proved below. The established universal bound remains 76.

The [source checker](input_bridge_selector_queue.py) and
[receipt](input_bridge_selector_queue.json) contain both a literal 63 source
and a literal worst-case 69 source, all independent source residuals and
their inherited triangular corrections. Author and independent complete
proof/source reviews pass, with a matching fresh default receipt replay.
A separate root proof/source review and default replay also pass.

## 1. Fixed native projections, with their full cost

Use the 54 module with positive supplied coordinates `q,F0,F1,F2,H`.
It proves

    q=3^t, t>=1, H=(q-1)/2,
    Fi=H+Ti,
    each Ti is a Boolean native ternary word of length t,
    T0+T1+T2=H coefficientwise,
    label at time 0 is 0.                                 (1)

Its eighteen additional positive coordinates include H and its seventeen
Pell auxiliaries, and it has thirteen equations. In particular `2H` is
already a paid register. In the formulas below, `H` is named `Hrep` in
the executable source, to avoid any kernel-name collision.

For any fixed column `v=(v0,v1,v2)` with entries in `{0,1,2}`, define

    word(v)=v0*T0+v1*T1+v2*T2.                             (2)

Equation (2) describes its semantics; the source uses the following
short formulas rather than paying three products and two sums. Because
the selectors are genuinely one-hot, its trit at time j is exactly
`v_(label_j)`. Consequently

    0<=word(v)<q,            word(v)=v0 modulo 3.          (3)

Every one of the 27 columns needs at most two additions/subtractions:

| Column form | Paid expression | Operations |
|---|---|---:|
| Constant 0, 1 or 2 | `0`, `H` or `2H` | 0 |
| One 1, at label i; others 0 | `Fi-H` | 1 |
| One 0, at label i; others 1 | `2H-Fi` | 1 |
| One 2, at label i; others 1 | `Fi` | 0 |
| One 1, at label i; others 2 | `(H+2H)-Fi` | 2 |
| Entries 0 and 2 | Double the corresponding Boolean expression | 2 |
| A permutation of 0, 1, 2 | `(H+F_at_2)-F_at_0` | 2 |

Doubling is one addition, not a free numeral multiplication. A zero
column can be used as a computed literal, but comparing it with a positive
stream coordinate makes that source infeasible, as it should. No claim
that every table has positive stream witnesses is made.

The short formulas and (2) sometimes differ as unconstrained polynomials.
Their difference is an explicitly checked integer multiple of the already
imposed checksum `F0+F1+F2-4H`. The executable source records that acyclic
residual correction. It is not an added equation or a hidden operation.

## 2. The exact generic FIFO relation

Fix three rows indexed by labels 0,1,2. Each row specifies a paired removed
symbol `(d0,d1)` and paired appended symbol `(a0,a1)`, all entries being
trits. Project their four columns by Section 1, supplying positive stream
coordinates `D0,D1,A0,A1` and comparing each with its computed projection.
Supply positive `L,W,alpha,V` and the ordinary positive input x. Impose

    W=3L,
    x+alpha=L,
    D0=x+W*A0,
    D1=L+W*A1,
    q=L*V.                                                (4)

The first four equations are the six-operation queue source. The fifth
adds one multiplication. The schedule appended after the projections is

    Wcalc=3*L;
    input_bound=x+alpha;
    shift0=W*A0; read0=x+shift0;
    shift1=W*A1; read1=L+shift1;
    time_divisor=L*V.

Compare `W=Wcalc`, `input_bound=L`, `D0=read0`, `D1=read1`, and
`q=time_divisor`. Thus the total is `54+P+7`, where the explicitly paid
projection subtotal `P<=8`. At the upper end it is 69=33M+36A. The
generic source has 30 positive existential coordinates, including the
22 coordinates of the 54 module, and 22 equations. The checker supplies
one literal four-column schedule attaining that 69 ledger; no assertion
that its particular table is universal or has a zero-reaching run is
needed for this source-count example.

Here all power and stream-bound hypotheses of the FIFO lemma are proved.
Since `L*V=q=3^t`, positivity and unique prime factorization give
`L=3^ell` for an integer `0<=ell<=t`. Hence `W=3^(ell+1)` is the
physical queue-length power. The input bound gives `0<x<L<W`, and
`I1=L<W`. Projection (3) gives `0<D0,D1,A0,A1<q` directly. The paid
joint bound `D0+D1+beta=q` from the eight-operation queue version is
therefore unnecessary; no claim that every such projected pair satisfies
that stronger joint inequality is made. Moreover `D1>=L` and `D1<q`
give `t>=ell+1` before invoking any loader. Positivity of A1 even gives
`D1>=L+W>W`, but the weaker derived history bound suffices.

The [scalar FIFO theorem](../../1980/EXPLORATION_NATIVE_STREAM_RAW_QUEUE.md)
now applies to both coordinates at the same t positions. It proves that
the projected removed symbols are exactly the successive heads of the
queue initialized by the ell ordinary ternary digits of x followed by
`#=(0,1)`, and that the final queue is all zero. Each supplied label
selects the stated read/append row. Conversely, any such finite zero-ending
queue history whose first label is 0, whose four aggregate streams are
positive, and whose initial x satisfies `0<x<L`, supplies every coordinate
of (4): `alpha=L-x` and `V=q/L` are positive integers. Necessarily
`t>=ell+1`, since the delimiter must be removed. Its labels supply (1),
and the retained selector theorem supplies all positive Pell auxiliaries.

This is a two-sided, complete finite FIFO relation for the fixed three-row
table. It does not require a guessed conversion of wide-radix histories.
It does not yet restrict the label word to a path in any given finite
controller. A controller would have to prove its initial state, each
state transition on these exact paired symbols, and the common time
positions. For the established delayed-loader machine, its semantic
zero-endpoint theorem would then supply genuine acceptance; for a
different table or machine that acceptance implication must be proved.

## 3. A positive 63-operation specialization and its exact language

Take this fixed table:

| Label | Removed pair | Appended pair |
|---:|---|---|
| 0 | `(1,0)` | `(1,1)` |
| 1 | `(0,1)` | `(0,0)` |
| 2 | `(1,1)` | `(0,0)` |

Both append columns are identical. Supply just one positive coordinate A
for their shared word. All three projections take one subtraction:

    A=F0-H=T0,
    D0=2H-F1=T0+T2,
    D1=2H-F0=T1+T2.                                      (5)

Append precisely these nine instructions to the 54 schedule:

    projectedD0=twice_H-F1;
    projectedD1=twice_H-F0;
    projectedA=F0-H;
    Wcalc=3*L; input_bound=x+alpha;
    shiftedA=W*A;
    read0=x+shiftedA; read1=L+shiftedA;
    time_divisor=L*V.

Compare (5) with their coordinates and the five expressions in (4), using
A for both append streams. This is 3M+6A beyond 54, hence **63=32M+31A**.
The shared product is actually computed once. There are 29 positive
existential coordinates (`q,F0,F1,F2,H`, seventeen Pell auxiliaries,
`L,W,alpha,V,D0,D1,A`) and 21 equations, with the same ordinary positive
parameter x.

**Exact language theorem for this source.** The 63-operation source has
strictly positive witnesses exactly when

    x=(3^ell-1)/2 for some integer ell>=1.                 (6)

To prove necessity, Section 2 reconstructs the actual queue. Every initial
ordinary raw symbol is read before any appended symbol. The only ordinary
raw symbol among the three permitted reads is `(1,0)`, so all ell input
trits are 1. The input is positive and `x<L=3^ell`, so `ell>=1`; this
proves (6). These ell first transitions have label 0 and replace each
raw 1 by `(1,1)`. The delimiter next uses label 1 and appends zero.
Exactly ell label-2 transitions erase the marked `(1,1)` symbols. The
result is all zero, and no further transition is possible because `(0,0)`
is not a permitted read. The unique zero-reaching label word is therefore

    0^ell 1 2^ell,             t=2ell+1.                 (7)

For the positive converse, given ell>=1 put

    L=3^ell, x=(L-1)/2, W=3L,
    q=3L^2, V=3L, alpha=(L+1)/2,
    T0=x, T1=L, T2=W*x,
    H=(q-1)/2, Fi=H+Ti,
    A=x, D0=x+W*x, D1=L+W*x.

These are exactly the streams of (7), all required coordinates are positive,
and every equation (4)--(5) holds. The selectors are one-hot with first
label 0, so the complete selector converse gives the remaining seventeen
positive Pell coordinates. This is a parametric witness construction;
the enormous Pell coordinates are not materialized by the finite checker.

For example `x=1,L=3,W=9,q=27,V=9,alpha=2`, labels `012`, fields
`(F0,F1,F2)=(14,16,22)`, and `(D0,D1,A)=(10,12,1)` give a positive
outer tuple. The next example is `x=4,L=9,q=243`, with labels `00122`.
Classification (6) concerns only this particular table. The separate
[stateless FIFO theorem](native_stateless_fifo_regular.md) proves that
every fixed finite stateless table of this form accepts a regular input
language, including the fixed origin and stream positivity requirements.

## 4. Two barriers to importing the existing delayed loader

First, the 54 module fixes the first selector label to 0. For any fixed
read projection, (3) forces

    D0=d0(0) modulo 3.

But `W=3L` and (4) force `D0=x modulo 3`. Thus the literal direct
projection interface admits only inputs

    x=d0(0) modulo 3.                                    (8)

This is a necessary condition on every arithmetic solution, independently
of any controller implementation. A fixed first label cannot represent
all ordinary-input residue classes by simply changing its interpretation
as x varies: the read columns are fixed program numerals. A redesigned
initialization or a paid change of time origin would require its own
equations and machine proof. No free prefix, input recoding, or permutation
depending on x is being assumed here.

Second, even if that first-position issue were repaired, the actual
delayed loader requires at least four distinct paired read symbols on
some genuine accepted inputs. At `x=5`, whose ordinary ternary digits
are `(2,1)`, any successful padding has at least one further raw zero.
The initial loading pass therefore reads

    (2,0), (1,0), (0,0), and the delimiter (0,1).

These four pairs are distinct. A fixed three-label projection has at most
three distinct paired read values, regardless of the controller's state
or the number of operations used to certify its state path. Thus adding
only controller equations to the literal projection interface cannot
recover every history of the established delayed loader. For example a
work machine accepting every input must admit this input and padding.

These are scoped obstructions to direct identification of the four
existing queue streams with fixed three-label projections. The separate
stateless FIFO theorem gives a stronger limit for this exact transport.
A serial encoding, shifted pairing scheme or partitioned cellular model
could have different dynamics and would need a new transport, initialization
and universal simulation proof; neither its possibility nor its impossibility
follows from (8) or the four-read count.

## 5. Evidence and reproduction

Run in the repository's pinned environment:

    python input_bridge_selector_queue.py

The checker verifies every instruction and source residual of the full
63 source and an explicit 69 source, including the inherited Pell
auxiliary-norm correction and all projection-checksum corrections. It
checks all 27 column formulas symbolically and 3,267 finite projected
native words. The projection costs are six zero-operation columns, six
one-operation columns and fifteen two-operation columns.

An independent queue simulation compares the two transport equations
against actual paired reads and a zero endpoint on 96,936 positive-stream
candidates through time length 6. Exactly the two instances of (7) with
ell=1,2 are admitted. This finite search corroborates the parametric
language proof; it does not establish it. The receipt hashes the selector
source dependency. No historical full regression suite or gigantic Pell
tuple is needed for these focused checks.

The arithmetic sharing and derived bounds are proved. A universal
controller or a complete universal certificate below 76 is not provided.
