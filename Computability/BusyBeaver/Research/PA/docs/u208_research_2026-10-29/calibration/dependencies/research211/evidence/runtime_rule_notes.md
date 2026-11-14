# Audit notes for the U211 symbolic primitive certificate

These notes concern the final native table with SHA-256
`7edae566b4c2e5c34d88030e0ae7caa49edda32c174b06b1a68bf9eb78567c8d`
and source-site file with SHA-256
`a1c81a3abff846a329a109927ce92d0be1553b7af2671855cdfe5bc4d6d953d1`.
The executed driver is `check_guarded_runtime.py`; the results are
`guarded_runtime.json` and `guarded_runtime_cases.json`. This is an executable
mathematical certificate using audited induction rules, not a Lean, Rocq,
Metamath Zero, or PA kernel certificate.

## Quantified configurations

The engine represents the whole two-sided tape, including the infinite zero
exteriors. A configuration consists of the literal control label, head
orientation, and two lists of tape-word atoms on the two sides of the head.
An atom is a constant-symbol run with affine length, an arbitrary finite list
of unary register blocks, an opaque exterior used by local block lemmas, or
the infinite zero exterior used by whole primitive contracts.

There are thirteen affine slots: constant term; extra header gap; nine primary
register values; first spare-register value; and the width of the remaining
finite spare-register list. The primary values and gap range over all natural
numbers. A decrement is split into the exhaustive cases zero and `v+1`.
The first spare is represented separately, so the spare list is nonempty.
The remaining list may be empty and its contents are arbitrary. Its width
variable denotes its actual total block width, rather than an unrelated
additional input to the machine.

The physical register permutation is `(6,2,0,4,3,7,8,5,1)`. The dispatcher is
native 84 (legacy checker label 96), native 254 is halt, and HEADER_BASE is 56.
All changes of state names are explicit bijective relabelings on the literal
working states and halt. The final source has 3909 sites, maximum address
length 42, and maximum consecutive-zero address run 6. The exact 56-cell
minimum header distance is the one supplied by blank startup.

## Why the symbolic steps are sound

1. **Literal transition.** The engine reads and applies an actual row from the
   supplied final table. It permits a literal read of a run only if the run's
   constant length term is at least 1 and every coefficient is nonnegative.
   Thus the run is nonempty for every represented valuation. One symbol is
   removed, the written symbol is inserted on the proper side, and the actual
   direction and control are updated. No unknown or opaque tape cell may be
   read by this rule.

2. **Unary scan induction.** When the literal row loops in the same state and
   moves in the current traversal direction, the engine consumes the whole
   homogeneous run. For length `n`, this is precisely `n` repetitions of that
   row. The proof is induction on arbitrary natural `n`; it includes `n=0`.
   The step count and displacement are the affine run length and its signed
   version. This does not bound any register value.

3. **Finite-list induction.** Write `B(v)=0 1^(v+1)` and
   `C(v)=1 0 1^v`. The checker first rederives four one-block traversal laws
   directly from the final table, for arbitrary natural `v` and arbitrary
   left and right contexts. Their entry labels in the inherited checker are
   73,95,48,112 (the wrapper maps the actual native table to these labels).
   Each block law costs `v+2` literal steps, traverses exactly that width,
   and returns to its entry state. The laws are B-to-B rightward,
   B-to-C rightward, reversed B-to-B leftward, and reversed C-to-B leftward.
   The base case for an empty list and induction by concatenating another
   checked block give traversal of every finite spare tail. The clock and
   displacement use the actual summed block width.

4. **Word normalization.** Adjacent equal-symbol runs are concatenated and
   identically zero runs are removed. The infinite zero exterior absorbs
   finite neighboring zero runs. The additional normalization identity is
   `C(A) 1 = 1 B(A)`, together with its reversal. Its empty-list case is
   immediate; the one-block identity follows by expanding the definitions;
   concatenation proves the finite-list identity. These rewrites preserve
   the represented whole tape, not just a finite viewed window.

All lengths accepted by these rules have nonnegative affine coefficients.
The literal-step nonemptiness condition is stronger than mere sampled
positivity. Unknown possibly empty runs cause rejection instead of an
unjustified branch choice.

## What each primitive contract checks

For every source occurrence, the engine starts with its exact binary address,
zero padding, the fixed header separator, arbitrary primary registers, an
arbitrary nonempty spare list, and the full blank exterior. It computes the
expected register change and successor address by the source instruction:
CI increments; CD either decrements a positive value or takes its zero
branch; CB and CC cut the appropriate source-address ancestor; CH halts.
The address increment overflow and the consequent head shift are accounted
for explicitly. A positive decrement enlarges the header gap; an increment
appends the prescribed spare block.

For every nonhalting instruction, the symbolic final state, both tape sides,
and head displacement must equal the expected contract exactly. For CH the
literal halt label must be reached. The computed duration must be an affine
nonnegative expression with strictly positive constant term. Hence every
simulated source step takes finite positive time for every actual finite
register valuation. An infinite source execution cannot be compressed into a
finite binary run by zero-duration blocks.

The 4000 symbolic-inference limit per primitive is a limit on certificate
construction only. A successful proof with an affine run length or a list
atom represents unbounded natural registers and arbitrary finite tails; it
is not a bounded execution test.

## Completed evidence and its limits

The final run checked all 5084 cases: one case for each of 3909 sites, plus a
second case for each of 1175 decrement sites. It used 1,280,108 symbolic
inferences, covered all 422 literal transition rows, and obtained minimum
positive duration constant 5. The four block laws were rederived from the
same final table. Row coverage is an additional completeness diagnostic;
the case-by-case symbolic contracts are the mathematical content.

The independent source audit establishes complete ordinal control-flow
identity and freshly checks all 3908 internal source-prefix bindings after
each of the nine rotations. The independent startup audit checks the whole
48140-step blank trace and exact final finite support, reaching native 84,
head-2, source ordinal 136, header distance 56, primary registers
`(1,0,13,0,0,1,0,0,1)`, and 43 spare registers equal 1. No changed retained row
is visited during this prefix. The initial source address is identical to
the baseline's address at the same ordinal.

The symbolic primitive theorem, source CFG identity, and exact startup
therefore transport the baseline's source-level behavior to this literal
U211 table. The numerical calculus, safe-suffix bootstrap, cofinal proof
search, and U/PA consistency calibration are separate inherited mathematical
obligations. These executable checks do not by themselves prove those
logical theorems or assert PA's consistency.

The inherited symbolic module intentionally refuses optimized Python because
it uses assertions. The portable wrapper must preserve that refusal. The
independent construction/source/local-fold checkers can use explicit checks
and can be tested under `python -O`; an optimized run must never be described
as rechecking this assertion-based symbolic engine unless the driver actually
provides equivalent explicit checks.
