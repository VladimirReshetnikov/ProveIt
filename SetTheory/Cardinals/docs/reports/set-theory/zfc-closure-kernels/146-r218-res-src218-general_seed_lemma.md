# General logical seeds for the 218 startup search

## Result

The logical seed need not be `[3,0,0,0,3,0,0,0,0]`.
At a clean source-root boundary, **every** seed

```text
[n, 0, 0, 0, d, 0, 0, 0, p]
```

with arbitrary natural `n`, `d`, and `p` has the same halting/refutation
equivalence.  In particular `n=0,1,2` and `d=0` are allowed.  There is no
logical need for `np >= 3` or `param1 = 3`.

The full register mapping is:

| Logical register | Meaning | General sound seed condition |
| --- | --- | --- |
| 0 | nextproof (`np`) | Any natural |
| 1 | topwff (`tw`) | A theorem code; zero suffices |
| 2 | wffstack (`ws`) | Every decoded stack entry a theorem; zero suffices |
| 3 | axiomcode | Zero at the root command boundary |
| 4 | param1 (`d`) | Any natural |
| 5 | param2 / cached formula (`h`) | A theorem code; zero suffices |
| 6 | scratch1 | Zero at the root command boundary |
| 7 | scratch2 | Zero at the root command boundary |
| 8 | prooflist (`pl`) | Any natural |

The theoremhood conditions are sufficient, not claimed necessary for every
individual dirty seed.  Arbitrary formula values cannot simply be admitted
to the soundness invariant: a cached contradiction could make NIP halt
without a derivation.

## Explicit proof

Soundness is the existing invariant that current formula, cache, and all
stack entries are theorems.  It does not mention `np`, `pl`, or `d`.
Every command preserves that invariant, and a halting NIP has cache1.

For completeness, a derivation of falsity compiles into a block `L` whose
contract holds for **every** current formula and underlying stack when
entered with `d=h=0`: it either halts or returns falsity with the same
underlying stack and `d=h=0`.  For every natural `U`, the prefix
`START_U = AX(0,1,1,U)` sets `d=h=0`, so

```text
START_U ++ L ++ [DROP,NIP,NIP]
```

halts from every retained input tuple.  Its candidate number is exactly

```text
N_U = P(3, P(1, P(1, P(U,R))))
```

where `R` is the fixed encoded tail `L ++ [DROP,NIP,NIP]`.  Pairing is at
least either argument, hence `N_U >= U`.  Choosing `U >= np` supplies a
successful candidate above any finite initial cutoff.  This is an explicit
cofinal family; it does not assume a fixed command word has multiple codes.

An initial positive `pl` strictly decreases on each nonhalting command until
zero, without changing `np`.  From a zero proof-list boundary, the next
candidate is loaded and `np` increases by one.  Every finite loaded list
drains unless it halts.  Thus every candidate above the initial cutoff is
eventually executed unless the enumerator has already halted.

The same proof applies to the current K219 calculus: only the literal
axiom/bundle formulas changed along the calibrated source lineage.  The
AX command interface, ten pushed entries, block compiler contracts,
enumeration, and contradiction test are retained.  K219's equality rewrite
is valid for all natural registers in every source context.

## Physical scope

The provisional 218 table is
`root218/candidate218/candidate.tm`, SHA256
`cd2e25ad8bd58112b74d671ff78334eacc0eb237201b32c871a73424e134073f`.
Its unchanged published219 source has SHA256
`0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789`.
The completed runtime driver checks every leaf and both CD guards with
all nine primary registers independently arbitrary, a natural extra gap,
and a nonempty finite spare list of arbitrary natural values.  Therefore
that core already supports the general seed family above.

**This does not repair blank startup.**  A startup candidate must still
reach the complete represented frame with the correct source-root entry
and zero exterior.  Any subsequent table mutation needs a new runtime
check.  In particular, neutrality searches using projected reachable
windows from the original `[3,0,0,0,3,0,0,0,0]` seed do not automatically
cover all new seeds; the original abstract domain at the root constrains
register0 to positive values.

## Source references and proof status

The inherited K224 note `portable/theory/enumerator_adaptation.md`, section3,
already proves the cofinal `START_U` family and arbitrary additive counter
case.  The general proof-list case follows from the inherited `drain` lemma.
Within the vendored K230 formal sources:

- `coq/logic/Enum230.v`: command state and `enum_step` definitions.
- `coq/logic/L1_Comp230.v`: `step_pl`, `drain`, `run_first`, `compile`, and
  `program_halts` contracts.
- `coq/logic/L1_Sound230.v`: `Inv`, `Inv_step`, `Inv_run`, and `halt_step`.
- `coq/logic/Seed230.v`: `reach_from` and `halts_from_reached`.
- `coq/settheory/KCode230.v`: `P_ge_l` and `P_ge_r`.

`general_seed_lemma.tex` gives an include-ready proof.  This is an ordinary
mathematical extension of the inherited contracts and their current-source
adaptation, not a new compiled Rocq endpoint.  No minimality claim is made.
