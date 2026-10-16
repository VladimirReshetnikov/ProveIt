# Independent review of the EPSC2 certificate checker

Reviewed by the engineering strand, 16 October 2026.
Reviewed file: `checker/epsc2_tableau.py`.
SHA-256: `efca519f170224a3a3efcb514616c793834e3bbcbc83640d287b1260a7db1c7f`.

No correctness issue was found in the requested audit scope. No checker or
test source was changed during the review.

## Parser and finite-candidate totality

The public matrix parser accepts precisely Bottom, nonnegative-index binary
atoms, implication, and universal binders with the specified arities.
Boolean values are explicitly excluded as natural labels. Scope checking
at depth 4 enforces exactly four possible free slots while admitting arbitrary
internal binder depth. Injecting a template `hole` through a matrix fails.

For nonnegative numerical input, each recursive matrix decoder child is
strictly smaller than its positive parent. Each recursive proof decoder
child is at most floor(n/6), and recursion is used only for n>=2. Each
nonempty list decoder step uses a tail at most n-1. Consequently numerical
candidate decoding is mathematically total. The proof checker processes
the resulting finite proof tree and has no hidden unbounded search.

The actual Python implementation uses recursion in parsing, scope checking
and numerical decoding. Thus a sufficiently deep finite input may exceed
Python resources. RecursionError and MemoryError propagate; they are not
accepted refutations. The design note explicitly distinguishes the ideal
unbounded-storage algorithm from this resource-limited Python reference.
That distinction must also hold in any later machine compiler.

## Refutation boundary

`check_refutation` accepts exactly two keys, `matrices` and `proof`. It builds
every root internally as a positive instance of the fixed EPSC2 template.
There is no input field for a target theorem, an initial signed formula,
an alleged axiom, or an initially contradictory branch. A proof of A from
assumed A and not-A cannot enter this boundary as an EPSC2 refutation.

`check_tree` is deliberately a separate generic testing interface: it accepts
arbitrary signed roots and is used for logical identity/specialization tests.
Only `check_refutation` and its numerical wrapper `accepts_number` should be
used as the theory-refutation entry point. The supplied search follows that
boundary correctly.

Positive implication requires both children; negative implication adds both
required signed entries. Positive Bottom is the only Bottom closure, and
atomic closure requires opposite signs of exactly the same interpreted
ordered parameter pair. The empty-matrix case cannot close an empty branch.

## Fresh parameter counter

Initially the counter exceeds every root environment label. For closed
axiom roots it is 1, with 0 reserved for a nonempty parameter universe.
Every subsequent environment label remains below the counter. Positive
universal instantiation reuses an older label or introduces exactly the
counter value and increments it. Negative universal instantiation always
uses the counter value and increments it. It cannot reuse an old eigenname.

The two implication children inherit the same prefix counter but may extend
it independently. This is sound because branch assignments and their witness
extensions are independent. Fresh names are syntactically distinct; the
rules do not assume that they denote distinct domain elements. The stated
first-occurrence renaming argument preserves tableau completeness.

## Four-slot environments

I independently traced the binder stack from the outer parameter binders
through all three matrix occurrences:

| Occurrence | Actual wrapper stack | Projection | Result |
|---|---|---|---|
| Subset-bound premise | [y,b,x,q,p] | (2,0,4,3) | [x,y,p,q] |
| Closure condition | [y,x,C,q,p] | (1,0,4,3) | [x,y,p,q] |
| Support condition | [x,y,C,q,p] | (0,1,4,3) | [x,y,p,q] |

The subset predicate's additional dummy binder selects z,y,b correctly.
The emptiness guard selects z,x; the closure membership atom selects y,C;
and support selects y,C. Matrix-internal binders prepend their own names to
the projected environment, preserving the ordinary de Bruijn interpretation.
Exposure drops template metadata only after entering a parsed matrix, which
cannot itself contain template holes. No capture or free-slot permutation
error was found.

## Executed checks

I independently reran the complete existing audit through its `run()`
function, without rewriting agent-owned outputs. It passed 145 matrix cases,
2,610 direct schema semantics comparisons, 69,600 independent projection
comparisons, 145 identical virtual/expanded proof checks, 11 adversarial
rejections, 10,000 matrix and 10,000 proof-code roundtrips, and a 2,000-candidate
non-refutation control.

Ten additional public-boundary malformed/adversarial certificates were all
rejected. A reserved-parameter 0 specialization check passed. A generic root
test with an existing label 100 confirmed that a negative universal does not
reuse that label as its fresh witness.

These checks support the ordinary mathematical checker argument. They
neither prove the separate strength theorem for EPSC2 nor certify a binary
Turing-machine implementation or state count.
