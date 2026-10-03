# An actual rejecting compiler slice for the weakened86 polynomial

The [all-input collapse theorem](complete75_weakened86_all_input_collapse.md)
proves that the unchanged86 polynomial accepts every positive ordinary
input whenever the fixed compiler parameters have odd d,b, with3 not
dividing d and MC even. This packet supplies an **actual rejecting
helical program and its exact fixed compiler recipe** satisfying those
conditions. Its language is empty, yet the weakened polynomial has
complete positive19-coordinate zeros at x=1, and at every positive x.
Thus the weakening is unsound on an actual program/input slice.

This is an existence counterexample with a fully specified finite
program/compiler recipe. The billions of permitted windows, enormous
fixed numerals, Dirichlet prime and full Pell witness integers are not
materialized. The parametric arithmetic theorem supplies the full zeros;
no local machine trace is represented as a numerical full-zero evaluation.
The sound75 certificate and87 polynomial remain unchanged.

The [checker](complete75_weakened86_rejecting_compiler.py) and
[receipt](complete75_weakened86_rejecting_compiler.json) distinguish the
literal transition table, exhaustive local-cross enumeration, exact lazy
window ordering, and compressed compiler metadata from that full existence
conclusion.

## 1. A fixed normalized rejecting machine

Take states start,loop,halt; tape alphabet0,1,2; blank0; initial state
start; accepting state halt. The total transition table is:

| State | Read | Next state | Write | Move |
|---|---:|---|---:|---|
| start | 0 | loop | 0 | stay |
| start | 1 | loop | 2 | stay |
| start | 2 | loop | 2 | stay |
| loop | 0 | loop | 0 | stay |
| loop | 1 | loop | 1 | stay |
| loop | 2 | loop | 2 | stay |
| halt | 0 | halt | 0 | stay |
| halt | 1 | halt | 1 | stay |
| halt | 2 | halt | 2 | stay |

Every initial transition enters loop. In loop, tape, head and state
remain unchanged forever. The accepting state is unreachable. This
proves rejection for every input, independently of a simulation cutoff.
The64 finite traces in the checker only corroborate this invariant.

The start-on1 transition writes2, stays in place, and enters a state
distinct from start and halt. It therefore satisfies exactly the
stationary first-step normalization used by the
[helical marker construction](../../1980/FIXED_RAW_UNIVERSAL_81_PROOF.md).
No additional normalization is required. Its fixed Start window has
boundary top row, middle row(I,I,Q), and bottom row consisting of two
headless1 cells followed by the2 cell with state loop. Its End window
has the same boundary row, middle row(L,I,I), and headless bottom
symbols(0,1,1). Both are accepted by the existing helical local predicate.

The complete75 compiler uses doubled ordinary input: at x its initialized
I-run has length2x+1 and the adjacent Q head, so Start-to-End distance
is2x. At x=1 this is the four-one initial tape with an I-run of length3.
The machine still enters loop after one step. Equivalently the doubled
language of the empty set is the empty set; no input recoding can turn
this program into an accepting one.

## 2. The exact finite tile and window alphabet

Use the canonical tile alphabet consisting of:

- the vertical boundary tile(1,0) and horizontal boundary tile(0,1);
- the12 ordinary interior tiles with a symbol in{0,1,2}, a head in
  {none,start,loop,halt}, and no initialization phase;
- the four initialization tiles L,I,Q,R with precisely the payloads
  required by the existing phase predicate.

There are18 distinct tiles. This omits no cell of a valid helical
configuration. The local predicate forces a vertical tile to have no
horizontal flag or payload, and a horizontal tile to have no payload.
At an ordinary interior cell, either the phase is absent and its payload
is one of the12 stated choices, or the predecessor boundary forces one
of the four exact phase/payload combinations.

The existing radius-one predicate reads only a center and its left,
right, down and up neighbors. It does not read the four corners of a
three-by-three window. The checker exhausts all

    18^5=1889568

five-cell crosses using that exact predicate;121165 are permitted.
Every such cross has18^4=104976 independent corner choices. Thus the
full allowed-window alphabet has exactly

    k=121165*104976=12719417040                       (1)

members. This count is of permitted local windows, not accepting
computations.

The source supplies a bijective random-access enumeration. Crosses are
lexicographically ordered by their five tile indices; corner choices
are ordered by their four base18 digits. The two actual marker windows
are moved to positions0 and1, and all other windows retain their raw
order. Explicit rank/unrank functions account for the two omissions.
They specify the entire list without constructing it. The checker
verifies1,030 selected rank/unrank round trips, the actual predicate on
those windows, and256 independent corner variations. The exact loop
count and its saved hash cover all five-cell crosses.

Every permitted window is included, with Start selector0 and End
selector1. Therefore the ordinary helical tableau theorem applies to
this exact finite alphabet: a correctly marked cyclic computation would
project to a halting run of the machine in Section1. No such run exists.

## 3. The actual modified compiler recipe

Apply the frozen [modified complete75 compiler](complete75_half_binomial_compiler.md)
to the list specified by Section2 and alphabet size18, and export with
its `new_constants` function. In exact mathematical pseudocode:

    windows = [window(i) for i in range(k)]
    constants = new_constants(compile_windows(windows,18)).

This is a finite, effective recipe for fixed integers. The checker does
not execute the billions-element list or the resulting numeral export.
It instead derives the following exact layout metadata from the frozen
compiler's formulas.

Let a_tiles=18 and let A_clause=2^ell, where
ell=max(2,bit_length(k+1))=34. Before zero-clause padding,

    m_initial=2ell+30a_tiles+8=616.

The required dummy inequality is m+1>=k+9a_tiles+5. Each zero clause
adds2 to m, hence there are6359708295 padding clauses and

    m=12719417206, native positions=m+1=12719417207.

Exactly one ignored dummy position remains. Its exponent is

    e_dummy=k+12a_tiles=12719417256.

Writing U=m+6a_tiles-3, the four anchors are U,3U,9U,27U. The frozen
compiler's band and support formulas give:

| Quantity | Exact value |
|---|---:|
| U | 12719417311 |
| largest native exponent Emax=27U | 343424267397 |
| spatial copy exponent H_layout | 648690282916 |
| first clause band T1 | 1335538817729 |
| second clause band T2 | 2022387352524 |
| optional high correction exponent | 2365811619922 |
| cell radix length L | 3814697265625=5^18 |
| inner bit width b | 762939453125=5^17 |
| cell bit width d=bL | 2910383045673370361328125=5^35 |

Here H_layout is a compiler exponent, unrelated to the Pell modulus H
in the arithmetic theorem. L is the least power of5 at least
213U+4a_tiles+5, exactly the implemented support bound.

To check b without constructing an enormous clause mask, put
h0=9a_tiles+4=166 and h=h0+padding=6359708461. The mask is exactly

    mu_clause=A_clause-2+sum_(j=1..h) A_clause^j.

All nonzero source coefficients are supported only through clause
exponent h0; dummy padding contributes no source coefficient. Their
sum is strictly less than

    (14k+9a_tiles+5)*A_clause^h0 < 2^5682.

Consequently the modified raw-margin radix target is less than2^5720.
The other target2mu_clause+4 dominates it, and

    bit_length(2mu_clause+3)=ell*h+2=216230087676.

The next power of5 is exactly b=5^17, matching the frozen compiler's
choice. The checker also matches every displayed closed layout formula
against the literal parent on three modest thousand-window alphabets;
these are supplementary finite formula checks, not the rejecting
program's full export.

The new masks, with Rradix=2^b and B=2^d, are precisely

    MC=B-1-sum_(e in native positions,e!=1) Rradix^e
           -2*Rradix^e_dummy,
    MF=sum_e MFpoly[e]*Rradix^e+4.                      (2)

The fixed DC,DR have the unchanged effective source recipes, including
the possible high monomial used for five-adic control. They are positive.
The original cached mask properties must not be exported in place of
(2); `new_constants` performs the required modification. The compiler
proof supplies the range, population, carry and synchronization
conditions. In particular MC=2 modulo4, MF=4 modulo8 and their
populations sum to d. Their computed populations are

    pc(MC)=2910383045673357641910918,
    pc(MF)=12719417207.

The small d=4,b=1 masks of the earlier scalar family are not this
compiler instance. They are unnecessary for the corollary.

## 4. Applying the arithmetic collapse

For this single fixed compiled program, b=5^17 and d=5^35 are odd,
3 does not divide d, and MC is even. All other source constants are
positive. These are exactly the hypotheses of the all-input-collapse
theorem. For each positive x it chooses a sufficiently large power-of-five
N, so q=B^N>2dx+2, while the source's input offset u=2dx+b remains odd.
The theorem pays every ratio, input and index congruence, and all five
positive strong/auxiliary coordinates. Thus the **actual unchanged86
polynomial for these fixed compiler constants has a complete positive
zero for every x>0**.

On the other hand the genuine compiler's language is empty by
Sections1-2 and the sound helical compiler theorem. In particular x=1
is a false positive. This is an actual program/input counterexample,
not an inference that negative R alone must encode a false input.
The earlier scalar family did not establish that semantic connection;
this construction does.

More generally every actual modified complete75 compiler has d,b
powers of5 and even MC. The collapse theorem therefore makes the
weakening accept all positive inputs on every such fixed program slice.
Any slice representing a proper subset loses soundness. This refutes
this particular86 proposal, not a general possibility of an86-operation
universal polynomial. The established75/87 results are unaffected.

## 5. Reproduction and limits

```sh
python3 complete75_weakened86_rejecting_compiler.py
```

The checker imports the arithmetic theorem's lightweight contract and
records its unchanged source ledger/hash. It checks the actual nine-row
machine, all local crosses, the marker ordering, random-access window
bijection, exact compressed layout, and three literal small compiler
matches. It does not rerun the arithmetic theorem's potentially separate
number-theoretic audit or build giant constants/witnesses. The full-zero
existence conclusion relies explicitly on its proof, including Dirichlet's
theorem and irrational rotation.

Author receipt generation and a separate fresh default replay passed.
The root reviewer read the full proof/source and inherited local predicate
and compiler formulas, and independently replayed the default. A separate
root oracle, importing neither the author nor inherited predicate, counted
5,508 vertical-boundary, 10,368 horizontal-boundary, 104,907 ordinary, and
382 initialization crosses: exactly121,165 crosses and12,719,417,040 windows.

A second independent reviewer read the full proof/source, marker and input
conventions, modified compiler construction and exact compressed layout,
then ran a fresh default replay. Additional independent checks covered256
lazy window recipes and omission boundaries,88 exact clause-mask bit lengths,
and every actual layout field. Both reviews passed without findings.
These finite checks retain the existence-versus-materialization distinction
above. No parent source, shared navigation or Git state is modified by this
packet.
