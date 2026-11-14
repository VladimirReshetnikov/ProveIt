# Independent follow-up audits

These checks extend the archive census at ProveIt commit
`906367250a7f96c923147b10df392294bced7be5`. None produced a verified machine
with fewer than 196 states. Their scope is narrower than a lower bound.

## Exact source-emitter audits

`audit_sevenhead_emitter.py` independently interprets the macro word as a free
algebra of implication, successor, and symbolic register values. It imports no
compiler or optimizer code. The four-gate input audit checks all 114 elementary
head variants, every gate, the unchanged prefix with its parameter reads, the
older stack, and the unchanged cleanup suffix. The four gate matrices differ
only by exchanging the antecedents of an implication and the conjuncts of a
conjunction. All 32 Boolean cases agree. A deliberately wrong head-order
declaration is rejected.

The seven heads consist of the six existing heads and the separately emitted
gamma formula `A -> U(A,A)`. Allowed changes are schema-parameter permutations,
the documented antecedent exchanges, a global equality-argument reversal,
gamma's parameter choice, and the order of the seven heads. Their exact emitted
expression trees are checked before interpreting a proposed search witness.
This is an independent arithmetic-emission check, not a new proof of the
arithmetic interpretation or the complete TM simulation.

`audit_negation_emitter.py` adds two conditional arithmetic normalizations:

| Physical-source spelling | Restored original spelling | Necessary hypothesis |
|---|---|---|
| `node37; incT; node64` | `push; incT; cons` | Incoming register 7 is zero for block equivalence; the formula macro also uses register 6 zero |
| `node64; node61; node61` | `push; incT; cons` | Incoming registers 6 and 7 are both zero |

`node61` is four increments. The second identity follows from
`4*p(t,1) = 4*p(0,t)+8 = 2*t^2+6*t+8` for the source Cantor pairing.
The upstream `M6/Source/AXMacro.lean` definition `registers` fixes both scratch
registers to zero; `AXMacroSound.lean` preserves this clean macro store.
`AXPair.pair` and `AXTimes4` give the arithmetic core contracts. A new source tree
must still bind those contracts at each occurrence. This checker does not prove
that binding or any physical tape contract. In particular, an individual-step
zero/positive approximation that loses register-6 information is not itself a
counterexample to the stronger macro invariant.

Fresh checks passed for the following grammar files:

| Source | Normalized family | Replacements | Receipt |
|---|---|---:|---|
| `pa_work/negation190/best73.grammar.json` | Separate 190-token word | 8 drain/inc/pair | `negation190_emitter_audit.json` |
| `pa_work/negation190/best78.grammar.json` | Diagonal 191-token word | 8 drain/inc/pair | `negation191_emitter_audit.json` |
| `pa_work/negation190/double_quad_seed.grammar.json` | Separate 190-token word | 8 pair/plus-eight | `double_quad_emitter_audit.json` |

The all-third-spelling seed is an emitter control, **not** an accepted physical
table: its inherited association contains a seven-zero address run. The checker
also accepts a C++ integer-grammar witness with its exact `negmask`, head order,
role selectors, equality orientation, and gate selector. The explicit synthetic
mixed-role/mixed-negation control `ternary_joint_control.json` passes; its label
marks it as not a physical candidate.

Replay, with `AXINPUT` naming the joint search's `inputs_four.json`:

```sh
python3 audit_sevenhead_emitter.py --inputs "$AXINPUT" --out fourgate_emitter_audit.json
python3 audit_negation_emitter.py --inputs "$AXINPUT" --grammar path/to/double_quad_seed.grammar.json --out double_quad_emitter_audit.json
python3 audit_negation_emitter.py --inputs "$AXINPUT" --witness ternary_joint_control.json --mask-encoding ternary --out ternary_joint_control_audit.json
```

The plain `--grammar` mode checks the declared baseline `--family separate` or
`--family diagonal`. Joint roles and orders use `--witness`. Binary masks select
old/new spellings with one bit per occurrence; ternary masks use two bits per
occurrence for the three spellings.

## Full-prefix two-row reader-fold search

The independent, standard-library-only `prefix_search/search_prefix.py` uses
every known internal source prefix, including its left `1` sentinel, rather
than only a fixed short window. For each pair of pure reader states it attempts
to retain one state, project the other to it, and synthesize both retained rows.
Each row may be an inherited right-moving reader action or an arbitrary
bit-writing left move to an existing helper. The local execution must preserve
the entire known prefix and arrive one cell right at the appropriate projected
child state. Attempts that inspect unknown cells or exceed 100 transitions are
rejected. Both rows are subsequently checked together.

| Input | Pure readers | Pairs | Branch-action trials | Joint trials | Survivors |
|---|---:|---:|---:|---:|---:|
| Separate196 | 115 | 6,555 | 5,139,048 | 86,459 | 0 |
| Scanner-best196 | 114 | 6,441 | 5,049,668 | 91,661 | 0 |

Both use 3,672 known internal prefixes. Their maximum known prefix lengths are
34 and 37 respectively. The zero-survivor result excludes this bounded family
only: it does not cover additional changed rows, external unknown cells, longer
blocks, different source semantics, or arbitrary smaller machines.

A positive control reconstructs the raw 202-state Separate source before the
six inherited folds. Restricting the search to states 2018 and 2024 recovers the
known fold: remove 2024, retain 2018, set row 0 to `0 L 2009` and row 1 to
`1 R 2019`. This took 807 branch trials and nine joint trials, producing exactly
one survivor. The 201-state output is a local fold control, not a new small TM.
See `prefix_search/positive_control/receipt.json`.

Replay, with `AX` naming the latest archive's extracted `axioms` directory:

```sh
python3 prefix_search/search_prefix.py --machine "$AX/separate196/machine.native.tm" --sites "$AX/separate196/sites.json" --out prefix_search/separate196
python3 prefix_search/search_prefix.py --machine "$AX/search/scanner_best196.native.tm" --sites "$AX/search/scanner_best196.sites.json" --out prefix_search/scanner_best196
python3 prefix_search/search_prefix.py --machine prefix_search/positive_control.native.tm --sites "$AX/separate196/sites.json" --pair 2018 2024 --out prefix_search/positive_control
```

## Short-scanner obstruction and exterior rotations

Deleting native state 34 and replacing `23/0 -> 0 L 34` by `23/0 -> 0 L 75`
requires more than eliminating the six reported interior AX addresses. The
existing `search/export_scanner.py` score tests for `1000000` and for **seven**
leading zeros. It misses the first source site's path `000000`, with exactly
six leading zeros. That first site independently defeats the shortened scanner.

On Scanner-best196, true six-zero leaf addresses occur at source ordinals
`0, 197, 584, 786, 867, 1759, 2068`. Increment instructions introduce an
additional transient trailing zero; sites `1246` and `1988` have that hazard.
The seed site's path is `100000`. Thus an AX-only maximum-zero score cannot
certify the global shortened-scanner condition.

`scanner_exterior/search.py` reconstructs the exact source tree and independently
resolves its jumps by subtree intervals. It enumerates 15 single-occurrence
pure-reader rotations outside the AX subtree, excludes protected engine controls,
requires the identical ordinal control-flow graph, checks the physical prefix
decoder, and then executes every symbolic instruction contract for survivors.
Two rotations retain all 4,780 original runtime contracts, at prefixes
`1010101` and `10101011`; both still fail the shortened scanner at site 0's
zero branch. Other rotations change the CFG or fail prefix/runtime checks.

This is a negative result for these cost-free local exterior rotations, not a
proof that every source restructuring must preserve the first six-zero path.
No new startup theorem or accepted 196-state layout is claimed from this audit.

Replay:

```sh
python3 scanner_exterior/search.py --axioms "$AX" --out scanner_exterior/receipt.json
```

The exterior audit uses the supplied symbolic runtime and its inherited engine
contracts. The prefix fold search and emitter checks are independent portable
Python programs. Exact input hashes, measured counts, and scope statements are
stored in their JSON receipts.

## Subsequent positive result: 18-instruction negation

The later `INC7; INC7; node64` construction is independently verified in the
self-contained `negation18/` directory. Its `proof.tex` gives a universal
terminating-loop proof of the arbitrary-scratch-Y core contract. Its `verify.py`
checks that proof's polynomial identities, two independent CFG resolutions,
exact native-entry bindings, all eight blocks in the new 3441-site source,
and the 245112-pair inductive zero/positive invariant that establishes clean
scratch at every block entry. A clean copied-bundle replay reproduces the receipt.

The associated whole-machine construction currently has 197 states, so the
strict state target remains open. The source-emitter checker now supports all
five spellings using `--mask-encoding five`; this uses three bits per occurrence.
The five choices are the original 47-site block, the prior 20-site block, the
24-site pair/plus-eight block, the new 18-site preload-two block, and a 21-site
preload-one/plus-four block. An explicit mixed-variant control is included as
`five_joint_control.json`, with its separate audit receipt.
