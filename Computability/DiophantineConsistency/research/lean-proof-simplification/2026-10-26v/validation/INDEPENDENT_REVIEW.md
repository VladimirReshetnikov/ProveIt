# Independent source-level candidate review

Pin: `22e020937caa81d0cb72a4f63071d6c0bcc1eba9`.

**Disposition:** six concrete additional mechanisms pass static semantic/contract review, subject to Lean elaboration and integration. All new Lean is **uncompiled**; no performance claim. The pulse is optional structural factoring, not a line-count saving. Ledger W1 is report R2 (pulse), and ledger W2 is report R1 (interval).

## Assumed-applied baseline

Reviewed `baseline_audit/ASSUMED_APPLIED_BASELINE.md`, `ASSUMPTION_LEDGER.json`, `NOVELTY_DECISIONS.md` and `INTEGRATION_CONFLICTS.md`. The audit models the shared outcomes/APIs of six placed packets, five incoming packets and nine prior-round recommendations. Alternative implementations are not applied simultaneously. Advertised adapters, even formerly incomplete ones, are assumed complete. The 75 legacy, 31 additional/strengthened and nine round-two ledger rows overlap; they are not 115 independent simplifications.

The present ideas remove residual obligations not supplied by those outcomes:

| Candidate | Residual mechanism | Closest excluded mechanism distinguished |
|---|---|---|
| M1 | Reflect one optional-state equality through an existing injection | Finite invariant predecessor reflection requires finite dynamics and a predicate; neither occurs here |
| M2 | Split at the unique tape-write location and leave destination conditional symbolic | Earlier syntax/tag constructor views do not give this spatial write-support normalization |
| M3 | Convert the sharp exterior guard with existing `le_abs'` | General library-reuse advice does not cover every newly introduced trace client |
| E1 | Identify the exact terminal-slot encoder with `Fin.val ∘ finSuccEquivLast.symm` | Product-pair inverse graphs concern missing coordinates, not this optional-state encoding |
| W1 | Derive west/east as shifted views of one spatial bond | Prior field-direction descriptors and NorthView do not establish spatial edge matching |
| W2 | Guarded `Int.induction_on` at translated displacement | Prior Nat scanner/cycle propagation does not cover this two-sided open interval |

## Semantics and guards

**M1.** The theorem header is byte-identical. `a.2.2 < 216` is retained, and is necessary: raw target216 also maps to `none` but is not215. The rewrite is equality reflection, not a new halt/transition axiom. `act_stateNumber` supplies the exact code equality. This works with either the original or E1's replacement injection; the two savings are distinct.

**M2.** The full three-way conclusion is unchanged. Old and moved heads are unequal because movement is exactly ±1. At the old head the new tape bit is the write; away from it the tape-read frame rule applies while the new-head conditional remains symbolic. An action entering `none` still writes and moves and produces final head colors432/433. Already halted configurations are stationary under `Machine.step`, a separate existing rule, not a fictitious action application. No tape normalization, uniqueness of stored list entries or live-next-state premise is added.

**M3.** `le_abs'` has the required orientation `a ≤ |b| ↔ b ≤ -a ∨ a ≤ b`. Its source-generated API is verified at the locked Mathlib revision. The inclusive threshold remains, including `t=0,x=0`; no positivity assumption is added. Existing trace induction and write-before-move support remain unchanged.

**E1.** Pinned Mathlib source lines186–204 explicitly send `none` through the inverse to `Fin.last n`, and `some q` to `Fin.castSucc q`. Therefore composing with `Fin.val` preserves `none=215` and every live state value. `finSuccEquiv` would instead use the wrong zero slot and is not used. The executable `stateNumber` definition and theorem statement are identical. One narrow import is added and separately charged; its cost is unmeasured.

**W1.** Let `h` be old head, `h'` new head. For right movement, `h'=h+1`, and the bond's left endpoint is `h`; for left movement, `h'=h-1`, and its left endpoint is `h'`. Thus west at `x` is `E(x−1)` and east at `x` is `E(x)`. The paired lemma derives this from original transition/receive/pass constructors, not an assumed compatibility premise. `nextHead_ne` excludes the impossible double-head branch. Target215 remains included; q supplies a live transition index, while north/south step interpretation still requires `cfg.state=some q`. The construction does not assert a stationary halted row.

`stepTile`, `receiveTile`, `sourceIndex`, `nextHead` and all north/south/whole-row statements are unchanged. **The west/east theorem statement forms change** despite preserved names. A search of the608 active Lean files finds their only other occurrences in the old horizontal proof and Checks audit commands, but this does not prove external clients absent. Compatibility wrappers, if required, must be counted separately.

**W2.** All binders and strict interval premises are byte-identical. The motive is `l < x₀+z → x₀+z < r → P (x₀+z)`. The positive branch gets its previous lower bound from `hl₀` and `n≥0`, the negative branch its previous upper bound from `hr₀` and `n≥0`; opposite bounds follow from the guarded target. No induction branch asks a local propagation rule to cross an endpoint. Both directions remain necessary. Finite counterexamples confirm why deleting either strict seed bound would invalidate the general statement.

## Independently reproduced source measurements

Nonblank code/declaration lines exclude comments, blank lines and separate audit commands consistently. Every helper introduced within a replacement is included.

| Target | Before | After | Delta |
|---|---:|---:|---:|
| M1 declaration | 10 | 3 | −7 |
| M2 declaration | 15 | 11 | −4 |
| M3 declaration | 8 | 3 | −5 |
| E1 declaration | 18 | 7 | −11 |
| W2 declaration | 31 | 23 | −8 |
| Five API-preserving declarations | **82** | **47** | **−35** |
| E1 additional import | 0 | 1 | +1 |
| W1 whole replacement block | 28 | 29 | +1 |

Thus the five API-preserving changes save34 net nonblank source lines after the import. Taking optional W1 as well yields33 net lines across these selected edits, but W1 is not itself a line saving. These are textual counts, not kernel proof-term size, elapsed time or whole-project totals.

## Evidence and acceptance

`source_validation.json` records all source/library hashes, nine probe audit names and six successful disposable-copy patch applications. `helper_test_output.txt` records48 passing tests. `validation_status.json` separates executed source checks from not-run Lean stages. Original files are unchanged. Fully qualified audits were moved outside namespace/theorem spans; all public probe theorems are covered.

Before adoption: compile probes and patched modules in the pinned full environment; run affected Encoding/Action/Step/TraceBounds/ResetRows/StepConstruction Checks and downstream strip/run consumers; inspect final endpoint axioms; integrate with the actual prior-proposal adoption branch; check/migrate west/east clients; only then consider resource-option or performance claims. No such acceptance gate has run here.
