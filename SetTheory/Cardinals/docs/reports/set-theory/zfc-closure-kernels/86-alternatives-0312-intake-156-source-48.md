# Intake 156, source 48: independent review

Reviewed manuscript: **Toward a Smaller ZFC-Consistency Machine: Sparse proof certificates, ranked continuations, and an involutive search controller**, dated 17 October 2026. Arrival `2447a98214`. Review scope: complete manuscript, mathematical ancillary notes, source and reference checkers, all advertised executable branches, primary references at the cited theorem locations, and current-tree comparison. This is an ordinary mathematical/source review, not a new proof-assistant check.

## Disposition and provenance

Accept as an addition to the existing closure-kernels research report. No retraction of a currently asserted repository theorem is required. The package gives new ordinary proofs and executable research, correctly describes the existing 252-state machine, and makes no new state-record claim. Its strongest concrete new result is an all-input sparse-certificate bound for the exact current C254 proof encoding. The new involutive controller is a mathematically specified alternative search architecture, with no binary compiler or completed ZFC query.

The untouched delivery is `/tmp/zfc-intake156/zfc_consistency_research_20261017/zfc_consistency_research_20261017`. It contains 70 files totalling 36,412,082 bytes. Every execution and generated output was in the separate review tree `/tmp/zfc-source48-review-a4mw2c8q`, principally `bundle`, `internal-replay/work`, and `pdf-build`. No delivered file was edited. Bulk checksum manifests and line endings were not checked. Functional identity guards for the literal table, formula-source export, circuits, and search inputs were retained. No Lean or Coq build was run or advertised for this package: its four Lean files are explicitly incomplete source excerpts, not a standalone dependency closure.

Pins accurately stated by the package:

- ProveIt: `fab89c5d26b81cd2ccab2ee5d213ff23725c7726`.
- Upstream busy-beaver main: `ec9ed4f713d8c017f15743ad0692cdf31a59952a`.
- Historical upstream identity underlying the local formal comparison: `297ab8df7e5de329605c3875b4934643b371a5e3`.
- Public 253 PR20 head: `0d544f2a2e3c18f12278441a74b7879f31cbe856`.
- Existing complete 252 endpoint: `9facd7770cdac94e72bb89c04cf09be1994e1ff8`.
- Historical requested commits `6d8bc7f1ba02c83e54757366f019f61b966ed0b7`, `63c83cf79986f8a92bb75460848a1d4f863b7b15`, and `0301aa64e0676bed17402a63de46996631252a51` are distinguished from the later unbounded endpoint.

The canonical table is the repository's existing table, byte for byte. Its functional pin is `8dae0c2359aa8bf87d32543b9e53e1f87fe4716c016a4e2fd174bfe09e520797`; the old-label pin is `939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713`. These identities identify actual inputs to executed checks; they are not a bulk manifest audit. Attribution to Mira-Cult, Jeff, Wade, mira-emmy, the prior ProveIt permutation work, and intake 154/source 38 is retained. The package expressly avoids blanket relicensing of imported files.

## Mathematical findings

### Exact sparse proof checker

The recurrence preserves all twelve `Code254Proof` tags and exact dual Cantor pairing. Zero is invalid; truth proof code 1 stores value 1, representing formula 0. An accepted conclusion is stored as its formula code plus one, so invalidity cannot alias truth. MP checks the actual major formula against implication of the actual minor conclusion to the proposed conclusion, GEN uses the exact universal constructor, rho8 retains all four literal arguments, and the bundle checks both literal inequalities. Literal schema parameters are not recursively mistaken for proof children. All demanded proof children are smaller than their parent, including malformed nodes.

Strong induction therefore establishes agreement with the pinned `decodeFuel (c+1) c`/validity/conclusion API on **every natural code**, not just quotations of valid proofs. Sparse histories include code zero, sort the dependency closure, and compute each row from prior child rows. The verifier may accept additional correctly evaluated interior rows. The size theorem correctly applies to the canonical dependency closure or the existence of a small certificate, not every accepted redundant certificate. Missing children, forged row values, and rows after the requested target are rejected.

For input bit length b and positive unfolded occurrence count N, the proof gives `N(N+2) <= 3b`, hence at most `floor(sqrt(3b+1))` canonical rows including zero. It handles input zero separately. The key parent inequality accounts for the outer Cantor squaring at MP: parent bits are at least twice the sum of positive child bits plus one. The one-child and two-child induction cases reduce to nonnegative squares. Height is at most `floor(log2(b+1))`; the sums of positive node bit lengths and squared bit lengths are below `2b` and `4b^2/3`. These apply also to distinct cache keys by selecting occurrences.

The balanced valid truth-proof family shows the square-root order for **unfolded occurrences**, not a matching lower bound for distinct cache rows: its height-h cache has only h+2 rows. The manuscript and independent note explicitly preserve that distinction.

The fixed formula circuits give the conservative uniform bound `E(c) <= c^(2^23)` and `bits(E(c)) <= 2^23 bits(c)` for positive c. Schema leaves, valid nonzero bundle payloads, GEN and MP are treated separately. The exponent is large but fixed; the depth-23 bundle is included. Temporary MP-comparison values at rejected nodes also receive a bound, rather than being assumed bounded by the invalid stored value zero. These arguments support an ordinary bit-model existence bound of quadratic time and linear workspace, with large constants. They are not an exact complexity theorem about Python containers, an array-access oracle, a shorter search over all proof codes, or a transition-table bound.

The API's mathematical domain is naturals. The ancillary review acknowledges ordinary Python interface hardening limitations outside that domain: float `0.0` can compare equal to integer 0, and malformed row objects can raise a `TypeError`. This does not refute the stated natural-code theorem; summaries should not advertise a total hostile-object parser.

### Arithmetic graphs and rejection

The explicitly printed pairing polynomial, tag equations, fixed constructor circuits, shifted row values, preceding-row lookup, and sortedness give an actual arithmetic graph, not an appeal to an opaque computation predicate. Every bound variable is renamed before expansion. BETA's quotient is bounded by its witness integer; lookup is restricted to preceding rows. The final presentation introduces a separate bound W for fields and local circuit witnesses, including the prospective implication at an unsuccessful MP comparison. CRT witness integers themselves are not circularly required to lie below W.

Acceptance and rejection are separate Sigma-1 formulas for the unique total evaluator. Rejection uses final value different from the requested conclusion plus one; it does not retain an acceptance conjunct. Ordinary totality/uniqueness gives the claimed Delta-1 presentation. A direct sparse list's linear bit size is carefully distinguished from the larger but polynomial CRT/BETA integer bound. The final manuscript supplies ordinary formalizability arguments, not an actual PA formula-representation or PA proof file.

I independently expanded all 11 printed arithmetic DAGs into symbolic primitive constructor trees and compared them to the fully expanded source-export trees, without using the submitted `Circuit` class. All match, including the 60-pair-gate bundle; the total is 103 pair gates. This also replaces reliance on the delivered auditor's unbundled small symbolic-DAG driver.

### Ranked continuation and bounded deletion searches

The proposed continuation theorem distinguishes visible register actions from pure jumps. After normalizing pure-jump chains, a successful positive action macro must perform the exact whole-register effect and land in the appropriate action-successor equivalence class. A jump macro preserves registers and strictly decreases a supplied rank. Thus an infinite simulation cannot silently stutter forever; the positivity/rank conditions are sufficient for the stated halting equivalence. The proof does not identify all symbolic checker failures with semantic impossibility.

The program has 6,459 internal decision nodes, 6,460 leaves, and 8,391 guarded cases. Of these, 1,927 are pure jumps and 4,533 are actions or halt. The action control quotient has 4,530 classes and maximum jump rank 4. Its only three nontrivial action pairs are leaf indices `(6306,6431)`, `(6336,6363)`, `(6337,6364)`. The independent certificate auditor reconstructs all successors, checks class/rank obligations, accepts 8,390 nonhalt continuation targets, and rejects 1,927 artificial stutters and the insufficient gap-39 control.

The full affine checker preserves complete left blank margin, marker, header, arbitrary sufficiently large gap, register-box interpretation and all exterior cells under the four attributed register-box contracts. The uniform family has 55,471 candidates. The incoming-action family has 132,048 candidates, varying a selected incoming transition's write, direction and surviving target while protecting all 55 box rows and the start/dispatch conventions. Both complete ledgers have zero certified survivors. Stop categories `fuel`, `unsupported_box`, `unknown_right_run`, and `missing_transition` are conservative certificate failures, not global inequivalence witnesses or minimality evidence. No failed candidate is promoted to a new table or blank endpoint.

The exact-prefix/modular-tail invariants for `(M,m)=(2,1),(8,4),(32,8),(128,32)` are checked as postfixed invariants; divisibility makes the modular increment/decrement transfer sound. They exclude the same six guarded cases as the earlier phase analysis and do not claim further exclusion.

### Involutive rewrite controller

The E7 basis, term codec, prior contextual rewrite reduction and Boolean-algebra calibration are attributed to earlier work. A ground contextual equation becomes a total endpoint transposition. Such transpositions generate exactly the ground equational congruence. Merely applying a fair list of generators is correctly shown insufficient by a finite cycle counterexample.

The new inside-out context code is total, including ignored unary sibling fields. The binary heap address encodes arbitrary generator words: a zero appends generator zero, a following one increments the final generator, and leading ones represent the empty word. A right edge applies generator j followed by j+1; its return reverses that order. This order is essential and is correct in the reference code. Complete bounded-depth tours return to the exact initial term and cover every finite word at some depth. The threshold doubles at stage boundaries; the unbounded vertex integer stores the path, so this is not constant-space search.

The exact stage call count is `6(2^D-1)-4D`. Initial equality checks cover the empty word. Zero-call right edges leave an already checked value unchanged. The optional phase flip and lifted edge transposition preserve exact projected orbits, including equal endpoints; their separate weight bound includes flips. The ordinary mathematical unbounded lifted architecture follows from the same event schedule. The public `lifted_search` convenience function itself has a finite depth argument; the direct `search` function supports an unbounded run. This is an implementation interface distinction, not a completeness defect.

No actual ZFC-calibrated ground query, its complete literal writer, binary startup, compiler correctness or state count is supplied. The eight-element finite algebra and finite E7 identity checks validate implementation controls only. They do not calibrate an absent ZFC query or prove that E7's empty-premise theory is inconsistent.

### Internal ZFC criterion

The report correctly distinguishes an external Lean consistency comparison, a theorem internal to ZFC, and PA internalization. It specifies primitive-recursive proof/axiom certificates rather than assuming an r.e. axiom range is decidable. Coded countable models have a nonempty domain subset of omega, a set relation and a satisfaction set for internal formula codes. The countable Henkin-completeness argument is an ordinary theorem formalizable in ZFC, not an illicit satisfaction predicate for the entire universe.

The least-representative interpretation imposes domain guards and equality invariance; the interpreted membership uses the bisimulation relation and its membership definition, not raw membership. It does not confuse internal Foundation with external well-foundedness. The sufficient ZFC theorem explicitly assumes four project-specific **uniform, all-code** bridges: literal execution/native proof, native-to-ZF, ZF-to-native, and ZF-to-ZFC via constructibility. Their combination gives both directions with the correct polarity. They are not discharged merely by naming existing external semantic Lean proofs. Guarded least-witness search is general recursive and ZFC-provably total once those internal implications are proved; it is not asserted primitive recursive or extracted from arbitrary Lean semantics.

The final independence warning is correct: consistency alone does not automatically give both polarities' unprovability in every theory.

## Primary-source verification

I opened the cited primary PDFs at the actual theorem pages rather than relying on the submission's bibliographic paraphrase:

- [Andreka–Nemeti, CAIII paper](https://old.renyi.hu/pub/algebraic-logic/CAIII-ANpaper.pdf): Theorem 1.6(i), physical PDF page 7, is the structural computable unrestricted-first-order to `Ldf3(P,3)` translation with its premise-preservation theorem. Remark 1.3(ii), physical page 5, supplies the one-generator free-Df3 connection. The report's narrow use is supported; it does not emit the project-specific fixed query.
- [McCune et al., Short single axioms for Boolean algebra](https://www.cs.unm.edu/~mccune/papers/basax/v12.pdf): Sh1 at physical page 3 and Theorem 2 at physical page 6 support the stated NAND Boolean basis.
- [Paulson, Constructible Sets and the Relative Consistency of the Axiom of Choice](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-551.pdf): physical pages 7–8 support the distinction between set-model satisfaction and class relativization used here. This reference does not automatically supply the missing project-specific internal ZF/ZFC bridge.

No primary paper was imported into the repository or quoted at length.

## Current-tree reconciliation

The main historical comparison remains accurate. Current `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/BinaryPerm252.lean:110` states `nonhalting_iff_zf_consistency`, whose right side is absence of a `BProv ZFax_s [] Form.fBot` proof. `ZFCBoundPerm252.lean:47` proves `blank_nonhalting_of_zfc_consistent`, and its header at line 13 still explicitly leaves removal of Choice from finite ZFC refutations open. Thus the report's distinction between complete external ZF calibration and the remaining full standard-ZFC/internal comparison is preserved. No unconditional nonhalting conclusion follows.

One concrete report proposal is already further along in current Lean than its pin: `Code254History.lean:197` states `accepts_iff_check (code conclusion : Nat)` for all natural inputs; line 205 gives `c254_iff_history`. This is the **dense** numeric history evaluator. It does not establish the report's demand closure, square-root row bound, bit mass or sparse arithmetic formula. These remain useful new formalization targets rather than a missing all-code dense correspondence.

The exploratory untracked `GroundRewriting.lean` contains proposed `prov_iff_walk` (line138), reset completeness (216) and `prov_iff_program` (223). It has not been kernel-checked and is outside the integration. An initial review sentence called these proved; the source author confirmed that status was unsupported. These are draft contextual-rewrite arguments, and neither they nor their presence verify the new involutive tour, phase lift or numeric implementation. All of these formal controller interfaces remain open.

Current `InternalWO.lean:27` defines internal set-relative class well-orders, and `OrderRec.lean:170` onward builds stages using explicit definability and set-bounding resources. Those generic tools do not yet provide `CodeOrder.lean` or `ConstructibleOrder.lean`, a complete constructible well-order, Choice or an internal finite-refutation translation. Their corrected headers now say the constructible-order application is future work. The report's internalization gaps should not be silently marked solved by them.

Existing full-control alternatives should retain their actual counts: the separate GEN-free experiment currently reports 285 states (`Research/ZFC/gen_free.md:6`), and prior 268 complete-logic controls concern a different baseline word/backend. Neither is a new calibrated record below 252. The report does not conflate these with the included canonical table.

## Executed verification

Main command, in a scratch-only wrapper:

```sh
uv run --no-project python -B /tmp/zfc-source48-review-a4mw2c8q/run_reproduce.py
```

The wrapper runs the submitted `reproduce.py --skip-manifest --full-searches --output .../runs/reproduction.json` using `runpy`. It only retains the submitted internal temporary copy for later review; algorithms and assertions are unchanged. A portable helper can invoke the submitted command directly on a recovered copy: no further manifest adapter is needed. Imported repository-oriented helper `main` functions must not be invoked in the shallow packet; this is already stated by its README.

Python 3.13.14; total 233.925 seconds; every advertised functional branch PASS:

| Branch | Actual result | Seconds |
|---|---|---:|
| Canonical table/renumbering/literal blank prefix | 252 working states, 504 rows, 82,552 moves, state 94/head 2, all 77 one-cells equal | included |
| Exact formula-source export | Saved `formula_circuits.json` bytes reproduced | 0.048 |
| Explicit arithmetic graph generation | Saved graph text bytes reproduced | 0.044 |
| Sparse checker | 1,024 pair, 10,000 unpair, 20,000 node-bound, 72 all-code/72 forgery, 14 tagged examples, 4 BETA controls | 35.159 |
| Involutive controller | Entire saved evidence JSON reproduced | 0.448 |
| Independent involutive review | Recursive-tour, address, phase and boundary controls PASS | 0.062 |
| Ranked continuation/ledger audit | All 8,391 successors and finite ledger/rank checks PASS | 2.118 |
| Full uniform search | 55,471 recipes, 127,868 affine checks, zero survivors | 55.143 |
| Full incoming-action search | 132,048 recipes, 203,162 affine checks, zero survivors | 124.555 |
| Four residue analyses | All saved masks/excluded lists reproduced | 13.838 |
| Regenerated ledger audit | Fresh complete ledgers accepted | 1.974 |

The sparse suite computes a valid bundle conclusion of 22,009,311 bits. Balanced truth controls at heights 0–6 have input bit lengths `1,8,35,142,571,2288,9156` and 2–8 canonical rows. These are controls of a mathematical theorem, not finite evidence extrapolated to all inputs.

Involutive finite controls include 5,000 pairing/context/edge roundtrips each; 1,024 coordinate roundtrips; 10 free stages/2,036 vertices; 341 word addresses; 457 finite two-involution actions/145,232 swaps; 3,584 basis valuations; 6,000 edge-involution and 8,000 semantic controls; 12,000 phase controls; seven direct and seven lifted positive basis searches; a restored depth-8 negative query; 128 lifted direction controls; and two unfair-schedule counterexamples. The separate auditor compares seven exact recursive stages, 255 last-letter vertices, 341 addresses, 144 phase controls, and six boundary cases.

I separately compared regenerated ledgers against the delivery: every field and every recipe is equal except elapsed time. Failure counts are respectively `(fuel 26,059; unsupported box 26,370; unknown right run 2,869; missing transition 173)` and `(69,429;55,328;6,313;978)`. All four residues retain the same six exclusions. The canonical table also equals the current repository artifact bytewise. Independently comparing the two packaged helper files to `git show` at the ProveIt pin confirms every function/class AST unchanged (9 and 15 definitions respectively); only the documented shallow `ROOT` packaging assignment is adapted.

Independent graph command:

```sh
uv run --no-project python -B /tmp/zfc-source48-review-a4mw2c8q/independent_graph_check.py
```

Optional advertised figure regeneration also PASS:

```sh
uv run --no-project --with matplotlib==3.10.7 python -B code/make_figure.py
```

No PDF-byte identity is inferred from a figure regenerated by a different rendering environment. The mathematical plotted data are the same exact saved integers.

## PDF quality and artifact completeness

A separate `pdf-build` copy was compiled with three successful sequential `pdflatex -interaction=nonstopmode -halt-on-error report.tex` passes (0.993, 1.007, 0.991 seconds). Result: 37 pages, 23 embedded fonts, zero warnings/errors/underfull/overfull boxes. Pages 1, 9, 11, 15, 24, 28 and 37 were visually inspected and are clean; ten pages were rendered in total. Evidence includes all three logs, `pdfinfo`, `pdffonts`, extracted text, rendered images and `pdf-build.json`. An incidental attempt to make a contact sheet could not use Pillow in bare Python; individual page rendering/viewing succeeded. This is not a submitted check failure.

Artifact roles: 14 TeX sources and two PDFs (main report and vector figure), 13 Python files, 20 JSON data/provenance/ledger files, six Markdown notes, five text files, four Lean excerpts, one imported Coq data file, two machine tables, a Makefile, the frozen build log and ignored checksum manifest. `source-excerpts/Code254.lean`, `Code254Proof.lean`, `BinaryPerm252.lean`, and `ZFCBoundPerm252.lean` are historical references, not new theorem sources. `Prog254.v` is program data, not a requested Coq build.

The delivered mathematical review records additional small historical independent controls without bundling every private review driver. The advertised package reproduction itself is complete and succeeded. In particular my independent gate expansion supplies a fresh check of the symbolic circuit identities; it does not pretend to reproduce an absent private driver. The source-excerpt sparse proof is a companion argument, not an additional executable check.

## Useful next work and limits

The most concrete next Lean target is an exact demand-closure evaluator proven equal to current `Code254History.value` on all codes, followed by the bit-growth and square-root lemmas. This preserves the exact existing calculus and can reuse its already checked numeric rows. Whether replacing dense histories or the current enumerator improves a complete binary machine is still a compiler question: the manuscript supplies no priced full sparse controller.

The involutive schedule removes permanent proof-history storage and repeated reset as a sound ordinary transformation, but still pays for unbounded addresses, term generation, comparisons, context decoding, a real calibrated query writer and blank startup. These are promising implementation experiments, not measured savings. The zero-survivor continuation families and unchanged residue exclusions are useful negative evidence only for their precisely enumerated sufficient-certificate families. There is no new sub-252 machine, global minimality, unconditional nonhalting, full internal ZFC equivalence or PA theorem in this delivery.

Evidence root: `/tmp/zfc-source48-review-a4mw2c8q`. Machine-readable companion: `/tmp/zfc-intake156/source48-review.json`.

