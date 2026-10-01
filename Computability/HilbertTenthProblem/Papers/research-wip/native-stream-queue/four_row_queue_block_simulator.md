# Four ternary rows simulate arbitrary finite-state queues on block-coded input

The four physical read/append rows

    0 -> 0 or 1,       1 -> 2,       2 -> 0                 (1)

support a fixed finite controller simulating **any** fixed finite-state
constant-length queue machine. The input is an explicit fixed block code
with two nonzero sentinels. No unbounded counter, externally announced sweep
boundary, or variable-length rewrite occurs. Every physical zero-reaching
run from a valid encoded input implies genuine source acceptance, and every
accepting source run has a physical zero-reaching simulation.

This escapes the [read-functional obstruction](native_read_functional_controller_regular.md):
the choice between `0->0` and `0->1` writes a target code after its old symbol
has been read. The finite controller uses this branch nonlinearly. A scalar
affine carry is not being substituted for that controller.

The theorem is a **coded-input simulation**, not a complete universal
Diophantine representation. Arithmetic certification of the finite controller
and a bridge from the ordinary varying integer `x` to the initial block word
remain separate obligations. The existing complete bound remains75.

## 1. Fixed source and fixed codes

Let the source have finite alphabet `Sigma={0,...,s-1}`, finite state set S,
initial state s0, and accepting states T. A source step reads one symbol,
appends one symbol, and changes the state according to an arbitrary fixed
finite relation. A missing transition rejects. Make every accepting state
absorbing with the identity rewrite on every symbol; this only completes
runs after their first acceptance. The source queue length N is positive.

Introduce two new symbols `$` and `#`, numbered s and s+1. They never occur
in source data. Choose an **even fixed** k large enough that every number
`2a`, for `0<=a<=s+1`, has at most k binary digits. Let beta(a) be those k
digits in low-first order. Thus

    beta(0)=0^k,
    every beta(a) begins with0,
    beta($),beta(#) are distinct and nonzero.               (2)

Code choice and k depend only on the fixed source alphabet. They do not
depend on the input, padding, space used or computation length.

Write `B(a)=beta(a)` as a trit block over0/1, and `C(a)=2beta(a)` as a
trit block over0/2. For a source word w=a0...a_(N-1), the initial physical
queue, in read order, is

    Enc(w)=C(a0)0^k ... C(a_(N-1))0^k C($)0^k C(#)0^k.     (3)

Its fixed physical length is `m=2k(N+2)`. The controller begins in its
COMPUTE phase with source state s0. The sentinels are part of the supplied
encoded input in (3); their presence is not an uncharged loader theorem.

## 2. One complete simulation cycle

A COMPUTE sweep scans blocks in (3). For each active block it reads its k
trits, appends0 at every step, and stores the decoded symbol in finite
control. This uses only `0->0` and `2->0`. Invalid blocks have no outgoing
completed decoding transition.

On a data symbol a, choose exactly one source transition `(state,a)->(state',b)`.
Then scan the following k zero work cells, appending B(b) one bit at a
time, using `0->0` or `0->1`. The finite controller stores the chosen target
b and its fixed position within the k-bit code. On either sentinel, keep
the source state and choose the same sentinel as target. Detecting `#`
ends the COMPUTE sweep after its k work cells have been written.

Suppose N source steps produce targets b0,...,b_(N-1) and state s'. After
these exactly m physical steps the physical queue is

    0^k B(b0) ... 0^k B(b_(N-1)) 0^k B($) 0^k B(#).        (4)

Next SKIP exactly k zero trits, using `0->0`. This fixed rotation leaves

    B(b0)0^k ... B(b_(N-1))0^k B($)0^k B(#)0^k.           (5)

Now PREPARE scans the active blocks and their zero work blocks. It maps
active0 to0 and active1 to2, using `0->0` and `1->2`; it copies each zero
work trit as0. It decodes the **read** active bits and ends on `#`, after
that marker's work block. The result after exactly m preparation steps is

    Enc(b0...b_(N-1)), with source state s'.                (6)

Hence one cycle takes `2m+k` physical steps and performs exactly N source
queue steps. Processing the two extra sentinels leaves the simulated state
unchanged; removing them from the logical execution gives the actual source
queue. If the source accepts partway through the sweep, its identity loops
finish the remaining positions without losing acceptance.

Every sweep boundary is detected by the uniquely coded `#`. The controller
stores only a phase, a source state, an index smaller than the fixed k,
a k-bit prefix or target code, and one marker flag. In particular, no
controller instruction tests m, N, the number of sweeps, or the remaining
source duration. The [checker](four_row_queue_block_simulator.py) exposes
this directly: its `Compiler.step(state,read)` has no queue-length argument
and can be compiled into a finite transition table before any queue is given.

## 3. Natural zero acceptance and the role of two sentinels

After a completed cycle, if the simulated state is accepting, enter ERASE.
Scan every active0/2 block and following zero work block, appending0 at
every step. Decode before forgetting the old active block so the controller
recognizes `#`. Erase that marker and its work block last. Exactly m steps
leave the physical queue allzero. Two final `0->0` steps lead to a fixed
terminal accepting controller state.

At least one full simulation cycle precedes ERASE, even when s0 was already
accepting. Therefore the history contains a complete marker write and
preparation before cleanup.

The second sentinel is needed to make physical zero itself sound. During
COMPUTE a marker is completely cleared before its copy starts being written;
a single-marker design can transiently reach zero when all other data are
zero. In (3), while `$` is cleared and rewritten, the old `#` is still
nonzero. While `#` is cleared and rewritten, the new `$` is already nonzero.
At other times at least one sentinel is plainly present. SKIP changes only
zeros. PREPARE maps each1 to2, so it preserves both nonzero sentinels.
Consequently physical zero cannot occur before ERASE starts.

ERASE is entered only from a genuinely accepting source state. Thus even
an earlier stopping time during the accepting erasure cannot yield false
acceptance. Requiring the fixed final control state is also valid and gives
the exact duration formula below. No externally checked terminal marker
pattern or arbitrary final queue word is needed.

For valid initial words, the construction is exact in both directions.
Induction on the cycles gives (3)--(6). Every nondeterministic controller
choice during COMPUTE is a source transition, and all other transitions
are forced. A finite source accepting path extends through its final sweep
using the accepting identity loops, then takes ERASE. Conversely any
physical zero-reaching path must have entered ERASE and therefore contains
a source accepting prefix. Undefined source transitions stop while at
least one sentinel remains nonzero.

## 4. Geometry, first row, positive streams, and native parity

Let r>=1 be the number of completed cycles before ERASE. With the two final
zero steps, the exact dimensions are

    m=2k(N+2),       t=r(2m+k)+m+2.                       (7)

Both m and t are even because k is even. The first physical row is `0->0`
by the leading zero in every code. Every accepting trace uses every row
in(1): nonzero markers are read via `2->0`, written via `0->1`, prepared
via `1->2`, and their zero work blocks use `0->0`. This remains true for
an initially accepting source and an allzero source data word.

Let I be the ternary integer of (3), let W=3^m and q=3^t, and let D,A be
the low-first read and append trit words of the complete trace. Then

    0<I<W, I even, D>0, A>0,
    D=I+WA, t>m, D,A<q.                                 (8)

The integer I is even because its digits are0/2. The standard FIFO
identity proves the transport. These powers describe the trace geometry;
they are not free exponentiation instructions in an arithmetic source.
The two final zero steps leave D,A unchanged and multiply the previous
time power by9. Therefore they also supply the strict joint bound

    D+A<2q/9<q.                                         (9)

For direct integration with four native selectors, define Fi as the Boolean
ternary indicator word of the corresponding row:

    F0=[00], F1=[01], F2=[12], F3=[20],
    H=F0+F1+F2+F3=(q-1)/2, G=F1+F2,
    D=F2+2F3, A=F1+2F2=G+F2.                            (10)

All five fields F0,...,F3,G are positive Boolean words. From(8), W odd
and I even give `D-A=0 modulo2`; from(10), `D-A=2F3-G`, so G is even.
Since t is even, H is even too. Thus their total `H+G` is even, which
is the parity required by the proved five-field raw Boolean packing in
[the exact four-selector58 / FIFO66 component](native_four_row_fifo66.md).
Also `H+G<=q-1`. These assertions are exact field identities, not an
assertion that a controller has already been arithmetized.

Every auxiliary of the elementary outer queue interface can be made
strictly positive: width slack `W-I`, duration quotient `q/W`, and optional
joint slack `q-D-A`. For an interface whose scalar initial value is `2x`,
this trace uses `x=I/2>0`. That x is the **coded** initial integer. It is
not the original unencoded source input, and renaming it does not pay
for conversion. The exact [FIFO66 theorem](native_four_row_fifo66.md) supplies all26
strictly positive arithmetic witnesses for these traces at its ordinary
parameter x=I/2, by its constructive converse. This is a positive extension
into that finite FIFO component, not an arithmetization of the simulator
controller or a bridge from unencoded source input.

## 5. What this proves about universality, and what it leaves open

The established [constant-length queue machine](../../1980/EXPLORATION_CONSTANT_LENGTH_RAW_QUEUE.md)
and its [delayed loader](../../1980/EXPLORATION_DELAYED_BLANK_RAW_QUEUE.md)
provide finite-state source machines for arbitrary recursively enumerable
sets, using adequate existential tape padding. Apply the construction above
to the complete initial word of such a source, including its own original
delimiter. The fresh `$` and `#` are distinct extra wrapper symbols. With
an adequate source padding, the physical simulation accepts exactly when
the source accepts. Smaller source padding still cannot create acceptance.

Thus (1) supports Turing-complete **finite-control, block-coded** computation.
One may fix a universal source machine and hence fix this entire controller.
The block encoding is fixed and effective. These facts refute any proposed
nonuniversality argument based merely on the four physical rows or on
lack of an external sweep counter.

Two arithmetic obligations remain substantive:

1. A Diophantine controller relation must certify the actual states and
   phases just constructed. Selecting the four physical rows alone does
   not certify this controller, and an arbitrary affine carry does not
   automatically realize its finite graph.
2. Ordinary numerical input must be loaded into(3), or another input format
   must be proved equivalent and its costs paid. In particular the numeric
   block map is a digit dilation. It is not generally a fixed polynomial
   in the ordinary input.

For clarity, if `B0=3^(2k)` and `c(a)` is the ternary integer C(a), then

    I=sum_(i<N) c(ai) B0^i + [c($)+B0*c(#)] B0^N,
    W=B0^(N+2).                                         (11)

The bracket in(11) is a fixed program numeral. If the encoded data sum
and L=B0^N were already supplied, marker attachment would cost one fixed
numeral multiplication and one addition, and `W=B0^2 L` one fixed numeral
multiplication. This conditional three-operation subtotal supplies neither
the encoded data sum, the powers, nor their relation to the original x.
No part of(11) is silently included in a universal-certificate ledger.

## 6. A binary three-row corollary

The same construction works on physical alphabet{0,1} with only

    0 -> 0 or 1,       1 -> 0.                           (12)

Use B(a) itself as the active block. COMPUTE clears it and writes the target
into the following zero work block exactly as before. After SKIP, the new
word is already in the original format, so PREPARE is omitted. A cycle
therefore takes `m+k` steps. The same two-sentinel proof makes zero acceptance
sound, and the final duration is

    t=r(m+k)+m+2, r>=1.                                 (13)

All three physical rows occur, the first is00, and m,t are even. The scalar
transport and strict joint bound still hold. If these binary physical symbols
are packed in **radix3**, initial I need not be even. For native **radix2**
packing, the fixed leading code bit0 makes I even automatically. In that
case put W2=2^m, q2=2^t, x=I/2 and use the binary row indicators:

    D2=F10, A2=F01, D2=2x+W2*A2,
    F00+F01+F10=q2-1, F00 odd, all three fields positive.

The [exact binary FIFO58 component](native_binary_three_row_fifo58.md) applies
at this coded x, including its fixed first00 selector and full positive
converse. Both radix2 and radix3 numerical trace identities are checked;
changing packing radix does not change a physical controller transition.

Thus three rows suffice for coded-input finite-control universality already
on two symbols. For a two-symbol row system covering both possible read
symbols, two rows would make rewriting read-functional and fall under the
regularity theorem. This is a precise row-count boundary for that coverage
condition, not a general minimum-operations theorem. The binary corollary
cannot directly read ordinary ternary inputs containing2; its loading gap
is explicit.

## 7. Evidence

The checker compiles literal finite controller graphs and compares complete
physical queue reachability against independent direct source reachability,
without a duration cutoff: 928 four-row comparisons across48 deterministic
and nondeterministic source systems, plus480 binary three-row comparisons.
It checks every reachable zero event against the source accepting state.
Thirteen explicit accepting traces include initially accepting input and
one, four and nine complete simulation cycles. Their exact transports,
row positivity, first row, duration formula, parity and joint bounds are
verified as integers. The three binary trace fixtures are additionally
checked in radix2 against the native FIFO58 interface, including even input,
positive fields, first-selector parity, geometry and the transport.

These finite checks supplement the constructive proof. They are not an
arithmetic controller certificate, an ordinary-input loader, a formalization,
or a universal operation-count improvement. The saved receipt is replayed
by running the checker without `--write`.

Independent full constructive-proof and literal-controller review passed
with no findings. Fresh default receipt replay also passed. The review
checked the sweep rotations, finite-state boundary detection, double-sentinel
zero invariant, positive row occurrence, and the separate arithmetic/input
obligations; it does not change those boundaries.
