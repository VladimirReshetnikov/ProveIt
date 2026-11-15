# Comparison of the current PA consistency-machine corpus

**Snapshot:** [`3c3bf00e3132d31d328a7bcfe79761ef238eced3`](https://github.com/VladimirReshetnikov/ProveIt/tree/3c3bf00e3132d31d328a7bcfe79761ef238eced3).

The current corpus contains **100 research deliveries, 91 distinct named positive-claim constructions, and 528 spanning 194-state transition-graph classes**. These figures answer different questions: the 528 classes also include 419 research auxiliaries, 14 rejected constructions, and four research seeds. The audit found no accepted blank-start consistency machine below 194 states. It did establish that the two new constructions in this release, **PA194H5XS** and **PA194JH5XS**, are graph-distinct from every one of the 528 recognized prior classes and from each other, even under the enlarged cosmetic equivalence described below.

This comparison concerns exact tables, documented mathematical mechanisms, and attributed proof claims. Graph comparison cannot establish arithmetic correctness. The complete current ledgers and executable evidence accompany this document.

## 1. What was inspected

The pinned tree contains 93 filed delivery directories under [`PA/docs`](https://github.com/VladimirReshetnikov/ProveIt/tree/3c3bf00e3132d31d328a7bcfe79761ef238eced3/Computability/BusyBeaver/Research/PA/docs), together with seven archives under [`docs/incoming`](https://github.com/VladimirReshetnikov/ProveIt/tree/3c3bf00e3132d31d328a7bcfe79761ef238eced3/docs/incoming). The audit enumerated all `.tm`, `.json`, and `.zip` blobs in the requested PA and incoming subtrees directly from the pinned Git tree. It checked every selected blob against its Git object identity and recursively inspected every distinct ZIP payload.

| Quantity | Observed count |
|---|---:|
| Filed deliveries / current incoming deliveries | 93 / 7 |
| Selected Git blobs / missing selected blobs | 12,031 / 0 |
| Distinct recursive ZIP payloads / archive references | 23 / 40 |
| Recognized complete binary-table occurrences | 5,686 |
| Normalized labeled transition tables | 1,338 |
| Spanning graph classes, all state counts | 1,125 |
| Spanning classes with 194 working states | 528 |
| Spanning classes with 193 working states | 55 |
| Nonspanning normalized tables, all sizes | 7 |

The recognizer accepts complete numeric five-column tables and four explicit JSON forms: multiline table strings, arrays of five-field rows, lists of row strings, and dictionaries keyed by state/read pairs with three-field transition values. It does not execute arbitrary generators or reconstruct every table printed only in prose, TeX, or Lean. Consequently the census is exhaustive for its documented explicit representations; the separate family and delivery ledgers cover the named architectures and report claims.

There are 22 literal-table inputs outside the strict single-external-halt recognizer. A separate audit established that these are small or partial search fixtures with zero or several external terminal labels; none has more than 139 working controls. They cannot conceal a 194-state graph isomorphic to either new candidate. The nonspanning tables are also structurally excluded from such a match: both new candidates have all 194 working controls graph-reachable from their declared dense start.

### Why the historical count was 139 and the current count is 528

The difference is fully reconciled:

\[
139+17+372=528.
\]

The 139 classes are the spanning 194-state classes already represented in the filed catalog. The seven current incoming archives add 17 named constructions and 372 unproposed research variants. Of the latter, 370 are retained in the physical-search corpus of `pa194_comparison_and_new_designs_2026-11-15.zip`, and two occur in the loop-return research packet. Thus the increase mainly reflects the inclusion of explicit experimental tables. It is not evidence of hundreds of separately established consistency theorems.

The role reconciliation is equally exact:

| Attributed role | Classes |
|---|---:|
| Reported principal constructions | 84 |
| Reported supplementary constructions | 7 |
| Research auxiliaries | 419 |
| Rejected constructions | 14 |
| Research seeds | 4 |
| **Total** | **528** |

All 528 roles and mechanism annotations are matched to the freshly recomputed graph classes by exact table identities. Their role labels remain attributions to the supplied research, rather than new independent certifications of the associated arithmetic proofs.

## 2. The common construction and the meaningful differences

The named 194-state candidates share a register-program implementation lineage. They vary along several mathematically independent axes: numerical formula constructors; axiom heads; command and store behavior; decoder association; history-sensitive folds; physical register placement; and guarded execution shortcuts. This common structure makes reliable composition possible, but it also explains why a shorter source or a new axiom presentation often remains at 194 physical controls.

The primary PA194 construction uses

\[
134\text{ fixed controls}+67\text{ readers}-7\text{ contextual folds}=194.
\]

Other original allocations use 68 readers and eight folds. The latest witness and independent-diagonal families use 69 readers and nine folds, while their symmetric companions use 135 fixed controls and ten folds. The final control count depends on shared decoder subtrees and the compatibility of all simultaneous folds. Neither the number of AX macro tokens nor the number of resolved primitive instructions is a reliable substitute for the final transition-table count.

### Store protocol and contradiction detection

The C family returns an MP conclusion in the cache and clears visible top. The N family returns the conclusion as visible top, avoids a dummy-zero push, and keeps the original Shift test `t+h=1`. H combines visible no-push MP with the cache-only test `h=1`. S changes the destructive comparator implementation to remove a restoration loop; it appears both with the cache-only guard and with the original sum guard.

These choices require different proof-command compilers. For a cache-only guard, a contradiction in visible top with zero cache does not halt under an arbitrary single Shift. The compiler must use the correct Pop or another proved detection word. Similarly, removing a dummy push changes stack preservation obligations. A theorem for one store protocol cannot simply be asserted for another.

The historical name **PA194NS is ambiguous**. One path uses NS for the cache-only machine also called HS; another uses NS for a symmetric implementation of the original sum guard. The current ledger distinguishes the machines by table identity and source path, as well as by their names.

### Formula coding and axiom presentations

Q exchanges the two curried premises of universal distribution. Its proof obligation is an explicit uniform derivation connecting the numerical calculi. Constructor coefficients four, five, and six require hereditary formula and label recoding, including the special zero alias. D changes the diagonal selector; G makes the explicit first AX operand control the saved generalization binder. GD combines an independent binder `U(c,h)` with the offset diagonal `Gamma(d+x)`.

The AX11 interface pushes the guard and enters the full MP operand reader. This makes its fourth operand a genuine consumed field and produces eleven protected entries. A three-operand encoding would describe a different computation. The fourth field, all eleven selectors, and the appropriate Pop contract must be included in the command proof.

The current witness packet changes the fifth head from

\[
U(D,E(H,D)\to1)\to1
\]

to

\[
U(D,E(H,D)\to1)\to A,
\]

where `A` is independent. The old calculus derives the new instances using explosion, and specialization `A=1` recovers the old family. JH5X additionally replaces a first head `(X→1)→H` by `(X→H)→H`; a separate explosion bootstrap is required to avoid a circular argument. H5X has 189 AX tokens and 3,677 primitive sites; JH5X has 188 tokens and 3,683 sites. Both still use 194 controls. These numbers illustrate why shorter axiom words need not yield smaller physical machines.

### Source invariants and physical transformations

Known-zero variants replace selected jumps or returns by decrements of registers proved zero at those sites. Their source invariants do not supply blank initialization automatically; that must be checked independently. Physical register-placement variants preserve logical stores through a tape-frame correspondence while changing active routing transitions. They are operationally different machines, even when the logical source is unchanged.

Dedicated history selectors, loop-continuation reassociation, and exact guarded shortcuts change recurring physical execution. LC preserves the resolved source program but changes constructor-loop addresses. F replaces certified three-step segments by one transition. LCG adds another shortcut justified by the unique incoming edge of a return control. Marker-separation and SF variants combine selectors with these arrangements. Direct positive finite-run simulations with primitive-recursive clocks give particularly clean relative iPRA proofs for these changes.

## 3. The seven current incoming deliveries

| Incoming packet | Named constructions | Material contribution |
|---|---|---|
| `pa194_gd_research_2026-11-14` | GD, GDH, GDHS | Independent generalization binder and offset diagonal, with three detectors |
| `pa194_lcfast_tagged_research_2026-11-14` | LCAX11GHF, LCAX11GHSF | Loop reassociation with two guarded physical shortcuts; separate tagged arithmetic research |
| `pa194_loop_return_2026-11-14` | LCG, LCGS | A third guarded return shortcut after loop reassociation |
| `pa194_comparison_and_new_designs_2026-11-15` | AX11H_SF, LC_AX11H_SF | Compatible history-selector and acceleration composition |
| `pa194_marker_separation_2026-11-14` | LCGMS, LCGSMS | Marker separation composed with the shortened loop returns |
| `pa194_ax11gdh_research_2026-11-15` | AX11GDH, AX11GDHS, AX11GDHF, AX11GDHR | AX11 plus independent binder/diagonal; symmetric, fast, and helper realizations |
| `pa194_witness_research_2026-11-15` | H5X, JH5X | Independent witness consequent and a coupled first-head replacement |

All 17 machines have 194 working states. Each recent packet explicitly identifies the revised AX11H written arithmetic calibration on which its absolute consistency conclusion depends. None of these readme-level claims is promoted here to a new end-to-end Lean theorem.

## 4. What the 193-state experiments do and do not establish

The 55 recognized spanning 193-state classes contain runtime cores, rejected mutations, and diagnostic inputs. No accepted blank-start consistency construction is identified among them. A particularly instructive Runtime193 has complete symbolic source-step contracts from a prescribed initialized tape, yet its unchanged blank startup fails. That is a useful runtime reduction, but it does not satisfy the requested blank-input specification.

The new 55th class is `research/runtime/header_feasibility/runtime193.native.tm` in the witness archive. Its local JH5X source contracts allow a 36-cell header, but its fixed blank-start splice remains rejected. The AX11GDH packet separately proves local contracts at header distance 38 for an inherited runtime. A smaller sufficient header does not itself construct the missing initializer.

The prior marker-separation packet examined all 10,422 starts of the historical 54 classes. It reports 110 halts, 10,308 certified outward rays, and four 100,000-step cutoffs. Those cutoffs were not called divergence proofs; the originating proposals had separate logical or source-control failures. The current comparison retains these distinctions and does not infer nonhalting from a long finite run.

The untagged coefficient-three calculus is a different failure: the supplied research gives a numerical contradiction certificate. The tagged-three proposal repairs the representation with disjoint tags and a two-way proof recoding, but its implemented source costs 207 states. Its optimistic 203 score overcounted four simultaneous folds. Neither that numerical score nor the existence of a sound smaller-coefficient calculus establishes a smaller TM.

### A complete finite quotient screen

The audit computed the greatest immediate-action state congruence for **all 528 current spanning 194-state classes**. Every result has exactly 194 blocks. The refinement distinguishes controls by their two `(write, move, successor-block)` triples, with halt separate. Therefore none of these tables has an unrestricted one-step state quotient that reduces its number of controls while preserving both symbol actions.

This excludes a precise finite transformation family. It does not exclude reachable-context folds, multi-step simulations, new encodings, new source programs, or startup redesigns, and it is not a global lower bound of 194.

## 5. The new symmetric witness constructions

The present release constructs PA194H5XS and PA194JH5XS by composing the witness-calculus sources with the symmetric cache-only comparator. Their final accounting is

\[
135+69-10=194.
\]

The physical/source proofs and source-operation changes belong to the construction report. The independent comparison establishes a separate fact: both exact tables are absent from the entire recognized pinned corpus, including every experimental 194-state class, and they differ from each other.

The novelty equivalence permits arbitrary working-control names, every spanning choice of start, reflection of the tape, global interchange of the two symbols, and ignored terminal-edge write/move decoration. The verifier compares complete canonical tuples. Global symbol interchange is included only to make the structural novelty test stronger; it is not asserted to preserve zero-blank semantics.

## 6. Arithmetic proof dependencies and evidence levels

The repository's [main PA status report](https://github.com/VladimirReshetnikov/ProveIt/blob/3c3bf00e3132d31d328a7bcfe79761ef238eced3/Computability/BusyBeaver/Research/PA/README.md) distinguishes finite execution results, symbolic certificates, and conditional arithmetic endpoints from an end-to-end Lean proof. That formal development remains incomplete.

Separately, the [revised AX11H packet](https://github.com/VladimirReshetnikov/ProveIt/tree/3c3bf00e3132d31d328a7bcfe79761ef238eced3/Computability/BusyBeaver/Research/PA/docs/pa194_ax11h_research_2026-11-14_2) claims a complete written iPRA calibration in ten mathematical proof fragments. It is the revised `_2` directory, not the older same-name delivery. Recent GH, GD, LC, and witness manuscripts import this written calibration. It would therefore be inaccurate either to classify every recent manuscript as only a PA claim or to describe the full consistency equivalence as already kernel-checked.

The dependency chain has several distinct obligations: literal blank execution to primitive register source; primitive source to the abstract scheduler; scheduler to numerical refutations; numerical calculus to the exact current PA-refutation predicate; and the intuitionistic transfer to nonhalting. A new relative physical theorem can be proved independently of the long arithmetic calibration, but its absolute `Con(PA)` corollary still imports that calibration. Positive halting-witness maps and intuitionistic negation suffice for the relative transport; no Markov principle is needed.

This inventory did not independently rebuild every transitive proof constructor in the ten inherited fragments. Its status labels describe the supplied reports, its hashes bind exact artifacts, and its executable results establish finite graph facts. These evidence levels remain separate throughout the accompanying ledgers.

## 7. Portable replay and complete comparison ledgers

Run the following command from this directory:

```sh
python3 verify_novelty.py --output verification-replayed.json
```

It requires only Python 3 and its standard library. It checks the exact identities of 528 frozen reference tables and both new candidates, recomputes the ordinary and enlarged canonical classes, repeats the unrestricted state-quotient screen, and compares the full canonical tuples. It needs neither the original repository nor a network connection.

`frontier194_current.csv` contains every recognized prior 194-state graph, `named_designs_current.csv` contains the 91 named positive-claim classes, `packet_ledger_current.csv` accounts for all 100 deliveries, `classes193_current.json` gives all 55 smaller diagnostic/runtime origins, and `families_current.csv` gives the full mechanism comparison. The frozen reference classes are retained under `tables/`; the exact candidates are under `candidates/`.

The mechanism table below is an exhaustive reconciliation of the 35 comparison families. Names are abbreviated by omitting the common `PA194` prefix where unambiguous; exact identities and paths remain authoritative.

| Family | Designs | Recurring behavior | Main proof obligation |
|---|---|---|---|
| Original source / allocation | Primary PA194 (67/7); PA194 (68/8) | Same original command protocol and separate diagonal calculus. | Complete source simulation and PA calibration. |
| Constructor coefficient | M4R; M5; M6 | Coefficients four, five and six change numerical formula coding. | Hereditary proof recoding, including the zero alias. |
| Cached MP | PA194C; PA194CS | Successful MP stores the consequent in cache and clears visible top; Shift tests cache. | Adjusted all-store command compiler. |
| Visible no-push MP | PA194N; PA194N5; PA194N6 | Successful MP retains (b,w,b,0), omitting dummy-zero push; original sum guard. | Reserved-zero handling and arbitrary carried stores. |
| Cache-only guard | PA194H; PA194H5; PA194H6; PA194HS = filed PA194NS | Visible no-push MP with Shift test h=1; HS uses symmetric comparison. | Final contradiction detection must use Pop. |
| Symmetric sum guard | PA194NS (sum guard); PA194SUMS | Original sum condition t+h=1 with symmetric destructive comparison. | Source tail equivalence; NS and SUMS differ in MP push behavior. |
| Q distribution | PA194Q | Exchange the curried premises of the universal-distribution head. | Restricted-rho derivation of premise exchange. |
| Q with coefficient changes | PA194Q5; PA194Q6 | Q head plus coefficient five or six; original dummy-push MP. | Both premise exchange and radix recoding. |
| Q with no-push MP | PA194QN = PA194NQ; PA194QN5; PA194QN6 | Q head, visible no-push MP, original sum guard. | Composition of Q proof transport and no-push compiler. |
| Q with cache-only guard | PA194QH; PA194QH5; PA194QH6; PA194QHS | Q head, no-push MP, cache-only Shift. | Cache-only Pop compiler and Q transport. |
| Q with symmetric sum guard | PA194QNS; PA194QS | Q head with the original sum guard; QNS removes MP push, QS retains it. | Exact sum-guard block equivalence. |
| Diagonal choice | PA194D; PA194DHS; Gamma(D) + CSZA | Use Gamma(D) instead of Gamma(A); accompanying controller variants. | New diagonal selector; supplement has narrower evidence. |
| Known-zero source returns | PA194A; PA194F; PA194J; PA194ZR; PA194R; PA194CSZ = PA194X; PA194CZ; PA194HA; PA194HAZ; CSZA final-register 3; CSZA final-register 5; CSZA final-register 6 | Replace selected jumps or returns by decrements of registers proved zero. | A source invariant and separately verified blank startup are both needed. |
| Physical register placement | PA194-AD; PA194F_AD; PA194R_AD; PA194TDY; PA194P5; PA194HX | Preserve logical commands while exchanging register positions and routers. | Register-frame conjugacy and complete initialization. |
| Decoder topology | PA194B; PA1944L | Preserve the original source program. | All-tape or complete source-frame positive simulation. |
| AX11 interface | PA194AX11 | Push the guard and fall through the full MP operand reader: four operands, eleven entries. | All eleven selectors and the fourth operand must be compiled. |
| AX11 with cache-only guard | PA194AX11H; PA194AX11QH | Four-operand AX11 with H guard, with original or Q distribution. | Final Pop compiler; latest incoming supplies expanded full iPRA claim. |
| AX11 with changed coding | PA194AX11Q6; PA194AX11QH5 | AX11 and Q with coefficient six/sum guard or five/cache guard. | Four-field coding, radix transport, appropriate halt detector. |
| AX11 with symmetric sum guard | PA194AX11S | Exactly the AX11 sum-guard command semantics. | Relative source/physical equivalence. |
| Explicit generalization binder | PA194G; PA194AX11G | The first AX operand c controls U(c,h), instead of inherited offset d; ten- or eleven-entry AX. | Shorter generalization word with no offset-setting command. |
| Explicit binder with H guard | PA194GH; PA194GHS | Explicit binder and ten-entry AX with cache-only Shift. | New all-store compiler; complete physical frame checks. |
| AX11QH decoder alternatives | PA194AX11QH4L; PA194AX11QH4R | Exactly the existing four-operand AX11QH source. | Positive finite-time transfer to the parent. |
| AX11 explicit binder and cache guard | PA194AX11GH = PA194AX11QGH; PA194AX11GHS | Four-field eleven-entry AX, direct binder c, visible no-push MP and cache-only Shift; GHS symmetric comparator. | Explicit all-store proof compiler, four-field scheduler and complete physical/source proof; absolute calibration inherited from revised AX11H manuscript. |
| Exact physical acceleration | PA194AX11GHF; PA194AX11GHSF | Preserves GH/GHS commands; replaces two physical paths of length 3 by one transition. | Three finite predecessor invariants,12 local cases; primitive-recursive clock t≤σ(t)≤3 t. |
| Loop continuation reassociation | PA194LC; PA194LC_A; PA194LC_B; PA194LC_C; PA194LC_AX11H | Preserves resolved source program, changes implementation of recurring constructor loops. | Source identity, literal-frame contracts and positive polynomial clock; revised AX11H absolute calibration for LC_AX11H. |
| Simultaneous history selectors | PA194SEL; single/composite selector auxiliary classes | Merges decoder checkpoints and recycles former labels as selectors reading last written bit. | Full local-tape identities with 1/3-step expansion and primitive-recursive relative iPRA clock. |
| Optimized nine-register placement | PA194AX11HR | Preserves AX11H source and arithmetic engines. | All 4778 literal contracts and whole-tape initialization; relative internal physical simulation. |
| Independent binder and diagonal with ten-entry AX | PA194GD; PA194GDH; PA194GDHS | Explicit generalization binder c plus diagonal Gamma(D), ordinary distribution; ten-entry AX; sum/H/HS detectors. | Relative primitive-recursive simulation/command proof plus explicitly inherited revised AX11H calibration; no completed Lean endpoint. |
| Loop continuation with two accelerations | PA194LCAX11GHF; PA194LCAX11GHSF | Loop-continuation reassociation plus two guarded shortcuts; separate tagged-three calculus prototype reaches 207 states, not 194. | Relative primitive-recursive simulation/command proof plus explicitly inherited revised AX11H calibration; no completed Lean endpoint. |
| Loop continuation with third guarded return shortcut | PA194LCG; PA194LCGS | GH/GHS loop-continuation reassociation and three guarded shortcuts including native 190/1. | Relative primitive-recursive simulation/command proof plus explicitly inherited revised AX11H calibration; no completed Lean endpoint. |
| Compatible selector and acceleration composition | PA194AX11H_SF; PA194LC_AX11H_SF | One selector pair 127/124 and two guarded accelerations on AX11H/LC_AX11H. | Relative primitive-recursive simulation/command proof plus explicitly inherited revised AX11H calibration; no completed Lean endpoint. |
| Loop return plus marker separation | PA194LCGMS; PA194LCGSMS | LCG/LCGS plus a dedicated history selector, retaining shortened loop returns. | Direct positive relative simulation with 1/3/5-step clock; inherits LCG/GH and revised AX11H calibration. |
| Independent binder/diagonal with AX11 | PA194AX11GDH; PA194AX11GDHS; PA194AX11GDHF; PA194AX11GDHR | Γ(d+x), raw-cache U(c,h), ordinary distribution, four-field eleven-entry AX, visible no-push MP, cache-only Shift. | Four-field command compiler, independent binder/diagonal selectors, literal simulation, then revised AX11H calibration. |
| Independent witness consequent | PA194H5X | Witness axiom consequent changes from contradiction 1 to independent A; A=1 recovers original. | Uniform explosion derivation of new head, exact reverse specialization, source and physical simulation. |
| Coupled first-head/witness change | PA194JH5X | Uses witness head above and replaces (X→1)→H by (X→H)→H, with independent explosion bootstrap. | 16-line explosion bootstrap avoids circular use of old head; two-way 95/72-line first-head certificates. |

The taxonomy and earlier status annotations adapt the explicitly attributed comparison in the supplied AX11GDH packet, updated here with marker-separation, AX11GDH, and both witness-head families. All current graph identities, role counts, and candidate novelty claims were freshly reconciled against the pinned corpus.
