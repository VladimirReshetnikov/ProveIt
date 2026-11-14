# PA194AX11H and PA194QAX11H

This research packet supplies two concrete new 194-state binary blank-start Turing machines, a comparison of all 72 research deliveries at the pinned ProveIt snapshot, a complete written mathematical proof, reproducible builders and certificates, and fresh unsuccessful searches below 194 states.

**Result:** for each delivered table, the report proves the written mathematical theorem

```text
iPRA ⊢ Con(PA) ↔ ¬Halt_blank(M).
```

This fulfills the requested alternative of materially different 194-state designs. No valid machine below 194 states was obtained. The proof supplies explicit primitive recursive constructions and uniform weak-arithmetic arguments; the accompanying executable checks certify the finite machine bindings. This release does not supply a new end-to-end Lean or Rocq kernel build. The exact current `Con(PA)` predicate is the repository's `nativePAConsistency`, namely the negation of `nativePARefutation`, at the pinned Foundation dependency.

Start with **`report/main.pdf`**, whose complete editable source is **`report/main.tex`**. The report includes all 388 transition rows for each machine, the complete delivery ledger, every recognized 194-state spanning class, precise command proofs, and proof-status distinctions.

## Machine conventions

Both machines have 194 working states numbered `0..193`, with initial state `0` and a separate halt label `194`. There is one head and one two-way infinite tape. The alphabet is `{0,1}`, every cell initially contains zero, the head initially sits at coordinate zero, and each transition moves one cell left or right. No external initialization is needed or allowed. State counts exclude the halt label.

The literal format is one row per state/symbol pair:

```text
current_state read_bit write_bit L_or_R next_state
```

| Machine | Dense table SHA-256 |
|---|---|
| PA194AX11H | `c5dfe1026d077d3e062eca11edb789597bfbbced4f6040f8828ae5d467b1167a` |
| PA194QAX11H | `19e215df20429fa6a35f0a99ba0dcfcb40893a6e4b9a4ae6e450b0225f110e50` |

## What changes

Both machines combine the existing AX11 four-parameter, eleven-entry protocol with the H cache-only Shift halt test and visible, no-push MP. QAX11H also exchanges the two curried premises of the sixth universal-distribution head. The ingredients are credited to the supplied packets; the exact composition, physical tables, certificates, and adjusted command compiler are the new result.

The change is operational: Shift halts exactly when the cache `h` is one. A contradiction in visible top `t` with cache zero no longer halts under a plain Shift. The proof compiler therefore uses

```text
A0 = AX(0,0,0,0)
Pop = A0; Shift^12
refutation word = A0; W_e; Pop
```

Pop halts when the saved top is one; otherwise it preserves the top and removes one stack entry. The fourth AX operand is real: the AX tail falls into the full MP operand reader. It cannot be omitted from the word encoding.

## Checks completed

For each machine:

- deterministic reconstruction: `134 fixed + 67 raw reader - 7 folds = 194` working controls;
- 3,671 primitive source sites and all 4,778 source outcome contracts;
- independent binding of every primitive source instruction and outgoing edge to explicit arithmetic templates, including all 190 AX tokens and both guard comparisons;
- 28 local fold contexts and complete dense/native conjugacy;
- symbolic command algebra including four-field decoding, all eleven emitted entries, selectors, zero aliases, generalization, and MP/Pop early halts;
- independent literal-tape verification of all 4,778 outcomes, with arbitrary natural register values and arbitrary nonempty spare files, using four generic list identities rederived from actual rows;
- exact complete-tape blank startup after 57,922 transitions, reaching native state 84 with head -2;
- exact structural novelty comparisons with all 82 recognized spanning 194-state classes; the two additional nonspanning 194-state tables are excluded by an invariant;
- the two candidates are distinct from each other under the same broad cosmetic transformations.

The independent literal runs used 1,101,836 symbolic operations for AX11H and 1,130,254 for QAX11H. Their maximum per-contract count was 403, and every physical duration expression has positive constant at least three. These are checker statistics, not universal runtime bounds for the machines.

## The complete written proof

`proof/ax11h_preservation.tex` gives written iPRA soundness and completeness for the **explicit abstract command schedulers**, relative to the stated numerical calculus. Its proof compiler is justified by quantifier-free induction over a bounded Boolean invariant, with explicit primitive recursive store bounds. `proof/ipra_simulation_theorem.tex` proves an exact positive-segment transport theorem with explicit witness maps and all hypotheses stated.

`proof/physical_ipra_audit.tex` proves a second substantive iPRA theorem: each literal blank-start machine halts exactly when its own supplied primitive-register program halts from source site 25 and logical store `(2,0,...,0)`. The proof interprets every symbolic rule, supplies all four generic list traversals, proves complete frame closure, and composes exact primitive recursive durations. Its additional finite audit checks all 4,777 nonhalting padded endpoints and all 4,778 duration vectors per machine. Source halting at step `k` gives physical time `57922 + tau(k)`; physical halting at time `t` gives the source witness `t+1`.

`proof/source_command_completion.tex` supplies the formerly separate source/command instance. It proves each arithmetic template with quantifier-free counter induction, matches all 3,671 literal source instructions, and composes an exact primitive recursive clock through fetch, dispatch, and execution. Its checker includes all intermediate scratch preconditions and the complete guarded AX expression. Both new receipts were independently replayed. The exact fresh-counter update is immediate at candidate selection, and the halted source file is retained explicitly.

`proof/consistency_implies_nonhalting.tex` then proves **`iPRA ⊢ Con(PA) → ¬Halt(M)` for both literal tables**, using the complete execution chain, the pinned model-uniform numerical seed soundness, the completed guarded gate, and the existing one-way IΣ₁-to-iPRA transfer. The Q head is handled by a fixed PA premise-exchange template. `proof/q_exchange_ipra.tex` separately justifies uniform translations between the two numerical calculi over iPRA.

`proof/foundation_paeq_completion.tex` constructs the current Foundation PA-to-ordinary-PAeq adapter. It checks the actual current coding and ten proof rules, translates arbitrary induction axioms, supplies explicit proof opening/closing constructors, and handles the one changed finite axiom (`addEqOfLt`). It also proves the necessary inclusion of historical prenex Σ₁ induction in the current hierarchy. Foundation falsity has code 13; numerical-calculus falsity has code 1. Those different codes are connected by transformations, not identified.

`proof/term_leaf_completion.tex` and `proof/forward_calibration_completion.tex` supply the forward numerical compiler in IΣ₁. The construction replaces full-PA inductions over all environments by finite trees of exactly the requests used. It covers term syntax, substitution, guards, value totality and coherence, vector and formula realization, arbitrary canonical induction matrices, and every outer proof rule. The recipes define total primitive recursive functions, and the bounded table invariants prove their correctness for arbitrary internal codes. They are mathematical specifications; this packet does not implement the entire enormous PA proof compiler as executable Python or Lean code.

`proof/consistency_equivalence.tex` composes the two model-uniform IΣ₁ directions with the repository's two one-way transfer theorems for the atomic halting formula `chi_M(t)=1`. The resulting theorem is the full **iPRA nonhalting/Con(PA) equivalence for both literal tables**, with no PA-consistency assumption and no use of Markov's principle.

| Interface | Written proof strength |
|---|---|
| Literal blank TM ↔ primitive source | iPRA |
| Primitive source ↔ abstract command scheduler | iPRA |
| Abstract scheduler ↔ C4 or C4Q refutation | iPRA |
| C4 ↔ C4Q proof-list translation | iPRA |
| Numerical refutation → current PA refutation | Model-uniform IΣ₁ |
| Current PA refutation → ordinary PAeq → numerical refutation | Model-uniform IΣ₁ |
| Con(PA) ↔ literal blank TM nonhalting | iPRA, by the cited transfer endpoints |

`claims.json` states the final claims. A `kernel_checked: false` field or `arithmetic_derivation_checked_by_this_script: false` field in a finite receipt refers to that checker's scope. It does not negate the separately supplied written theorem. Intermediate reviews are clearly marked historical under `references/historical_reviews/`.

## Fresh reduction searches

The joint grammar search tested 2,912,159 proposals across AX11 and AX11H, with 854,658 accepted moves, retaining a best score of 60 effective reader controls: 194 total. The seed family includes both original/Q shapes, equality orientations, three diagonal choices, curried premise exchanges, and per-head parameter permutations. No qualifying smaller implementation appeared.

Physical screens tested all 18,721 ordinary control pairs and 32,038 head-displaced pairs for each of primary PA194, AX11H, and QAX11H. A staged QAX11H screen completed 358 neutral rewrites followed by merger synthesis, comprising 6,702,118 pair instances, 8,726,731,232 individual action trials, and 52,929,250 paired choices. No hit was found. These are bounded screens using recorded windows and arithmetic samples, not global lower bounds.

Applying the runtime splice `301→88` to either new machine produces a 193-state table that reaches an outward nonhalting ray after exactly 92 blank-start transitions. The complete prefix and finite tape support are certified. Such a table does not implement the intended proof search.

## Reproduce

Python 3.10+ with the standard library suffices for the main checks. Keep assertions enabled.

```sh
python3 -B verify_all.py --quick
python3 -B verify_all.py
```

Quick mode reconstructs and byte-compares both machines, replays command checks, every primitive-template binding, physical-frame closure, the finite Foundation proof constructors, the 119 current/historical coding comparisons, the fixed premise-exchange certificate, and corpus novelty, and checks saved reference-source identities and independent certificate bindings. It explicitly skips the expensive construction and literal symbolic contract replays. Full mode performs those replays too. The independent certificates already included here were produced by full runs. Replay outputs go to a new temporary directory, preserving the delivered receipts.

The optional search scripts require a C++17 compiler. See `research/physical/` and `research/joint_grammar/` for exact input files, limits, counters, and replay commands. Recreating the entire repository census additionally requires the pinned checkout; all representative tables needed to replay novelty are already included.

To rebuild the PDF:

```sh
python3 -B generate_report_tables.py
cd report
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

## Provenance

Repository: https://github.com/VladimirReshetnikov/ProveIt

Commit: `1c9524d8bf2e0a27b9a16ff622359927f536e663`

Current Foundation dependency: `32e1a0956a8622fad067328ca1959729a7634428`

`NOTICE.md`, `PROVENANCE.json`, and the retained license texts identify inherited code and mathematical ingredients. `SHA256SUMS` binds the release files. Corpus recognition is exhaustive within the scanner's documented formats; historical proof claims are attributed and are not all independently replayed.
