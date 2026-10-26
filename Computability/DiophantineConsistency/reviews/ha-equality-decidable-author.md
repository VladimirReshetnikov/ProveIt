# Equality decidability in conventional HA: author receipt

The new `HAEqualityDecidable` packet constructs actual intuitionistic HA
proofs of `∀x ∀y (x=y ∨ (x=y → ⊥))` and its arbitrary-term instances.
The only direct main import is the frozen `HANaturalCases`, hence the frozen
basic arithmetic and finite-deduction interfaces. No excluded-middle schema,
double-negation elimination, semantic truth oracle, classical BProv conversion,
C222 calibration, or consistency assumption occurs in the proof. In particular,
this arithmetic equality result is not a general formula-decidability theorem.

Frozen files under `Lean/DiophantineConsistency/`:

| Source | Lines | SHA-256 |
|---|---:|---|
| `HAEqualityDecidable.lean` | 181 | `3decb32e7c5bd2bdf2d45b9ce73f1ff85752d5d0927cbb45c1a0940c672985cd` |
| `HAEqualityDecidableChecks.lean` | 63 | `aef2d186ec74e1f8c81d74c95ec6fa76a14a3523fe0aa9b0511dcdcbe76fbc1b` |

The public helpers `Relative.or_elim`, `Relative.ex_elim` and
`Relative.eq_elim` assemble the existing `HA.Derives` constructors.
Disjunction elimination combines the finite axiom lists used by its two
branches and premise, weakening only by membership. Existential elimination
concatenates both actual finite axiom lists `L ++ K`. Its explicit
`Formula.Sentences B` premise proves that this entire axiom list is unchanged
by variable shift. The open context is still mapped by `Formula.rename
Nat.succ`, and the conclusion is likewise shifted. No open assumption is
discharged or silently treated as a sentence. Equality transport shifts its
arbitrary left term through the Leibniz hole before substituting the right
term, preventing capture.

`EqualityDecidable.zero_cases` eliminates the actual HA zero/successor
split. The successor option contradicts `succ_ne_zero` after equality
symmetry. `succ_cases` propagates a predecessor equality using successor
congruence and a predecessor inequality using `succ_inj`. The main theorem
applies the actual first-order formula-induction rule to
`body = ∀y cases(x,y)`. The base is the preceding zero theorem. In the
successor step the proved decomposition of y supplies either zero or an
existential predecessor. Existential elimination shifts x, y, the retained
existential assumption and the universally quantified induction hypothesis;
opening the shifted hypothesis at the new predecessor gives the required
successor case. This uses one arithmetic formula induction rather than a
redundant second induction. Finally, two actual universal-elimination rules
yield `eq_decidable s t` for arbitrary terms.

I read the complete new source/check pair before execution, each correction
before its replay, and the entire final pair again before freeze. Checks cover
the literal closed sentence, shared variable 0 in both arbitrary terms,
distinct nested parameters through variable 7, arbitrary reclosure, and an
existential elimination that retains the genuinely open assumption
`var 0 = var 4` by shifting it to `var 1 = var 5` inside the witness branch.
All 14 final axiom reports use only `propext` and `Quot.sound`, or no axioms.
There is no `Classical.choice`, `sorryAx`, native decision oracle or new axiom.

Fresh compilation used only the private overlay
`/tmp/ha-equality-decidable-author-oaqht0mm/lib`, the pinned Lean 4.32 compiler,
and `-M6000 -j1 -DElab.async=false`. Nine custom prerequisite objects were
reused after exact current-source and prior-object checks: the eight modules
in the preceding NaturalCases receipt plus its newly frozen main object.
Every prerequisite source/object pin was checked before and after each
invocation and again at freeze. Lean's toolchain is an explicit cached
boundary. This is a fresh two-leaf compilation, not a fresh whole closure.
No existing source, shared object, umbrella, package source or Git state was
modified.

The final main exited zero in 0.70 seconds with an empty log. Checks passed on
their first invocation in 0.55 seconds, with the 14 expected reports. The two
earlier main runs exposed only elaboration issues: a simplified `True` leaf
needed `True.intro`, a final `Proves` wrapper needed unfolding, and one local
context placeholder needed inference from the preceding theorem. All failed
snapshots and logs are retained. No statement, premise or mathematical proof
strategy was weakened.

Final private object hashes:

- Main: `5605bfe640d18427f6e3d45208de33cd3fce5f17d4ab79a22f2354d391f05946`.
- Checks: `14e0ee189ed2dea5f8360694edf0a6c00b4549bcd480b7606f2adc115da08424`.

`ha-equality-decidable-author-replay/` durably records the full preparation
and build scripts, inputs, source snapshots, exact commands, exit codes and
logs. Aggregate `ha-equality-decidable-replay.json` has SHA-256
`e08f75509369f5859a208174b409bb722b7ed2c809442f3d1c6e8be1661b472b`.
This receipt is author validation; root's independent review remains separate.
