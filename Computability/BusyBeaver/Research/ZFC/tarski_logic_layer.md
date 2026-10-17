# The machines' logical engine in Lean

Every calibrated ZFC proof search in this project keeps the same logical
rows: Mira-Cult's 254-state machine (verified upstream in Coq by Jeff) and
every complete-logic control recorded in
[logical_engine_completeness.md](logical_engine_completeness.md), such as the
279-state full-logic PSC control. The reduced equality-free calculi behind
the 248–252-state experiments are refuted by the finite-sort model of
[typed_countermodel.md](typed_countermodel.md); any calibrated sub-254
machine in this family must therefore keep a complete quantifier and
equality layer. Until now its soundness and completeness existed only inside
the imported Coq development (`ZF/stdzf/coq/L1_LMeta.v`, `Std_alpha.v`,
`Std_H.v` and `ZF/m254/coq/logic/*` at upstream commit
`297ab8df7e5de329605c3875b4934643b371a5e3`). This note records an
independent Lean proof. The named-formula metatheorems were reconstructed
from the classical Tarski/Kalish–Montague route. The separately attributed
propositional certificate and numerical program ports are described below;
no Coq compiler was run.

## Statements

All modules are under `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`.

| Module | Result |
|---|---|
| `Kalmar.lean` | For any `imp : α → α → α` and `bot`, a predicate closed under MP containing K, S, Peirce and ex falso contains every instance of every classical `{→, ⊥}` tautology (`tautology_complete`). No injectivity of `imp` is assumed, so code aliases such as `imp 0 0 = 0` are harmless. |
| `TarskiCalculus.lean` | Named formulas `NF` over `∈`, `=`, `⊥`, `→`, `∀`; Tarski semantics; the calculus `Thm Ax` whose rules are exactly MP, generalization, theory axioms `Ax` and the rows below; `soundness`. |
| `TarskiDerived.lean` | Propositional toolkit; quantifier monotonicity; the B axiom from `rho6`; `vac_of_not_occurs` (vacuity for **every** formula not containing the label, although the rows only give it for atoms); equality is an equivalence relation. |
| `TarskiLeibniz.lean` | `leibniz`: `x = y → (φ ↔ φ[y/x])` without rebinding; `spec`: `∀x φ → φ[y/x]`; `spec_self` (the T axiom); `alpha_fwd`/`alpha_bwd`. No substitution row exists in the calculus. |
| `TarskiClean.lean` | Clean formulas (no rebinding), depth relabelling `cl`, the semantic substitution lemma `sat_rn`, and `cl_equiv : ⊢ φ ↔ cl K d φ`. |
| `TarskiComplete.lean` | `completeness`: validity in every model of `Ax` (all formulas of `Ax` true under all assignments) implies `Thm Ax`. Henkin construction over labels; see below. |
| `Lukasiewicz.lean` | (Codex agent) Attributed port of the 107 condensed-detachment certificates of Jeff's `CD254.v`: `rho8` alone yields K, S and Peirce; `rho6` adds ex falso; `Tarski.classical` and the unconditional `Tarski.complete`. |
| `TarskiFalsity.lean` | The machines' relative falsity `F = Rel(0,0)`: `ThmG (rel 0 0) Ax` is the literal row set; it is sound for irreflexive models and complete for `⊥`-free theories and targets with respect to irreflexive models (`alias_sound`, `alias_complete`). The comparison axiom IR is not needed as a row. |

The rows, in the machine's parameter order, are

```text
rho8  ((c → u) → a) → ((a → c) → (b → c))        Lukasiewicz
rho2  ∀a (b → c) → (∀a b → ∀a c)
rho4  ∀a ∀b c → ∀b ∀a c
rho6  ∃a ∀a b → b                                  ∃ = ¬∀¬
rho1  ∃a (a = b)
rho7  c = a → (c = b → a = b)
rho5  c = a → (c ∈ b → a ∈ b)
rho3  a = b → (c ∈ a → c ∈ b)
V∈/V= R(a,b) → ∀c R(a,b), gated by c ≠ a, b
```

matching `Codes254.v:103–110` upstream. In `ThmG F`, `¬A` is `A → F`.

## Proof outline

1. **Propositional.** `rho8` gives K, S and Peirce by condensed detachment;
   ex falso is K followed by `rho6` (`⊥ → ∃0∀0 b → b`). Kalmár's argument then
   yields every tautology instance.

   The certificate is search-determined. An independent given-clause search
   (`lukasiewicz_search.cpp`, replayed and checked step by step by
   `lukasiewicz_cd.py`) with size bound 19 and pick-given ratio 5 finds a
   107-line chain, `results/lukasiewicz-proof.txt`. Its 106 derived formulas
   coincide exactly with the 106 derived certificates of the attributed port;
   the remaining line is the axiom. Anyone can therefore regenerate the
   certificate from `CCCpqrCCrpCsp` alone:

   ```sh
   g++ -O2 -std=c++17 -o lukasiewicz_search lukasiewicz_search.cpp
   ./lukasiewicz_search 19 5 100000000 K=CpCqp P=CCCpqpp S=CCpCqrCCpqCpr > proof.txt
   py -I lukasiewicz_cd.py --from-proof proof.txt        --compare-lean ../../Lean/BusyBeaver/ZFC/Lukasiewicz.lean
   ```

   The C++ program is untrusted; the Python replay re-derives each step with
   its own unifier, and the Lean kernel checks the committed certificates.
2. **Vacuity.** For `i` absent from `φ`, `φ → ∀iφ` by induction: implication
   uses `∃i a → a` (from `rho6` and the induction hypothesis) and a classical
   case split; quantifiers use `rho4`.
3. **Equality and substitution.** `rho1`, `rho7` and atomic vacuity give
   reflexivity, symmetry and transitivity. `rho3`/`rho5` (membership) and
   `rho7` (equality atoms) give Leibniz's law for whole formulas, moving
   `x = y` under binders with `V=`. Specialization to `y` then follows from
   `∃x (x = y)` and existential elimination for the `x`-free instance.
4. **Henkin model.** A Lindenbaum chain visits every formula infinitely
   often. A rejected `∀aχ` (no rebinding of `a`) receives a fresh witness at
   every visit. Theory formulas are axioms of `Thm`, never hypotheses, so a
   witness only needs to avoid finitely many hypotheses and the theory is
   never renamed. The domain is the labels modulo provable equality; `rho1`
   and the unbounded witnesses give every class arbitrarily large
   representatives, which the universal case of the truth lemma uses.
5. **Clean forms.** `cl_equiv`, proved in the empty theory and transported by
   soundness, moves the target and the closures of the theory axioms into the
   clean fragment where the truth lemma holds.
6. **Relative falsity.** Replacing `⊥` by `F` maps derivations to derivations
   (`thm_tau`). IR becomes `∀0 (F → F)`, a generalized identity.

## Obligation map for row minimization

The proof shows exactly where each row is consumed; deleting a row must
re-establish the corresponding lemma by other means.

| Row | Consumed by |
|---|---|
| `rho8` | all propositional reasoning (via K, S, Peirce) |
| `rho6` | ex falso, the B axiom, existential elimination |
| `rho2` | quantifier monotonicity, generalization over hypotheses |
| `rho4` | vacuity of quantified formulas only |
| `rho1` | reflexivity of `=`, specialization, rich equality classes |
| `rho7` | reflexivity, symmetry, transitivity, Leibniz for `=` atoms |
| `rho5`, `rho3` | Leibniz for `∈` atoms; membership congruence of the model |
| `V∈`, `V=` | base cases of vacuity; `V=` moves `x = y` under binders |

Two consequences for compiler experiments:

* Symmetry of `=` is used essentially (for the reverse half of Leibniz),
  so `rho7` cannot be dropped merely because the theory is equality-free.
* Only atomic vacuity with `c ≠ a, b` is needed, which is exactly the
  machines' gate.

## A calibrated equality-free *language* (design analysis, unmeasured)

Soundness of a row can be established in a model of ZFC, with its singleton
sets. In such a model the formula
`U(x,y) := ∀z (x ∈ z → y ∈ z)` defines equality. Replacing every equality
atom of the rows by `U` therefore gives rows that are true in V, while the
same translation argument as `thm_tau` transports every derivation of the
primitive-equality calculus. For an equality-free theory true in V this is a
**calibrated, complete** engine whose formulas contain no equality atoms, so
the three-tag codec applies. This argument relies on the singleton resources
of the chosen set-theory model. Extensionality alone does not suffice:
on the two-element structure whose only membership edge is `0 in 1`,
Extensionality holds but `U(1,0)` is true and `1 != 0`.
The bound label of `U(i,j)` must avoid `i` and `j` (for example `i + j + 1`);
each translated row is then true in such a set-theory model: `U(c,a) → (c ∈ b
→ a ∈ b)` is even logically valid, and the others hold because `U` is
identity there (take `z = {x}`).

It is not obviously cheaper. `U` replaces six equality atoms (one in `rho1`,
three in `rho7`, one each in `rho5`/`rho3`), each costing about four
constructor calls instead of one, while saving the `V=` row (vacuity of `U`
is derivable once its bound label avoids the vacuity label) and the equality
constructor. A rough estimate is a net loss of several states under the
public backend. No compilation has been measured, and the bound-label
condition for `V=` still needs a checked choice. It is recorded as a
calibrated alternative, not a recommendation.

## Scope

These theorems concern named formulas and the abstract row calculus. They do
not yet connect numerical codes (`Base3Syntax`, `Bottom3Syntax`, the
upstream dual-Cantor base-4 codec) to `NF`, the gated theory bundle to a
set-theory schema, the enumerator, the compiler, or any literal table. They
supply the logical half of each such calibration in Lean.

## The numerical code bridge

`Code254.lean` connects the base-4 dual-Cantor code calculus (`code =
4·P(x,y) + tag`, `P(x,y) = tri(x+y) + y`, tags Imp 0 / Rel 1 / All 2 / Eq 3,
truth alias `0 = Imp(0,0)`, falsity `1 = Rel(0,0)`) shared by the calibrated
254-state machine and the 279-state full-logic PSC control to the named
calculus. `C254` has the truth code, MP, GEN, the eight coded rows and the
gated bundle; its definitions state the content of the published code
calculus in independent Lean.

* `c254_sound`: every derivable code decodes (`dec`, with `dec 0 = F → F`)
  to a formula true in every irreflexive model of all decoded bundles. The
  alias `Imp(0,0) = 0` is harmless because both readings are true.
* `c254_complete`: if the bundles that are literal encodings of named
  formulas (`EncBundle`) have no irreflexive model with a valuation
  (equivalently, a nonempty domain), then code 1 is derivable.
  Atomic vacuity, which the calculus emits only inside the gated bundle, is
  projected out with the same gate `c ≠ a, b`; conjunction elimination is a
  tautology instance through Kalmár's theorem over codes.

**Correction, 16 October 2026.** The first version of `c254_complete` omitted
both a valuation and a nonempty-domain premise from its no-model hypothesis.
That premise was impossible for every theory: the empty domain satisfies
irreflexivity and every globally quantified axiom vacuously. The corrected
theorem explicitly passes a valuation to the no-model hypothesis, and
`empty_domain_counterexample` preserves the historical counterexample in Lean.
This was a vacuous hypothesis, not an inconsistent axiom or an unsound kernel
derivation.

The two theorems use different model theories: soundness assumes all decoded
bundles, whereas completeness assumes that literal encodable bundles have no
nonempty model. No theorem here equates these theories. In particular, the
ordinary named encoder never returns code 0, although the decoder handles
its truth alias. One can either prove the necessary normalization and
model-class comparison, or calibrate the two stated model obligations
separately; this distinction must survive the set-theory bridge.

The remaining calibration obligations include: (i) Con(ZFC) gives an
irreflexive model of all decoded bundles
(upstream: `SoundBW254.v`, via L); (ii) a refutation of ZF gives a refutation
of `EncBundle` (the bisimulation-quotient interpretation, upstream
`S_quot.v`/`S_ax.v`, partly mirrored by the equality-free CP/GIC modules
here), with explicit encodability and binder-freshness checks for the chosen
instances; (iii) the enumerator, program and literal table.

## L2: the shared register program computes the enumerator

The attributed public 253-state machine and Mira-Cult's 254-state machine
run the same 219-node register program (`Dag254.lean`, generated from the
pinned upstream `Dag254.v` by `generate_dag254_lean.py`, an attributed data
port). Under Wade's structured semantics (`RMDag.lean`, deterministic):

* `L2Lib254`: the nine-register record; all 19 loop nodes (transfer, copy,
  clear); `pair` adds `P(s1, tw)` (induction on `s1 + tw` with the triangular
  step); the unpair walk computes `Cantor.ofNat`.
* `L2Macros254`: `pushwff`, `v_1`, `par1/2/3`, `cons = Imp`, `wel/wal/weq`,
  `wn/wa/wex`, `read`, `pop`, as record transformations on clean states.
* `L2Control254`: the destructive equality test, fetch, MP and NIP.
* `L2Axioms254`/`L2AxiomsEval254` (generated by `generate_l2_axioms.py` and
  `generate_l2_axioms_eval.py`): one lemma and one closed form per node of
  `axioms()`; the closed forms collapse `unP (P x y)` at every step (a one-shot
  evaluation duplicated terms exponentially and did not finish in ten minutes).
* `L2Root254`: `ax_eval` (axioms() pushes exactly `Enum254.axStack` and leaves
  exactly `Enum254.gate`, which also validates the transcription of the rows
  and the bundle against the compiled program), the dispatch cascade,
  `root_step` (one root run is one `enumStep`, halting included), `iter_iff`,
  and the boot form: the first two candidates (MP on truth, DROP) reach
  `nextproof = 2` with all else zero, the register file the TM boot produces.

The composed theorem is

```text
program_halts_iff : IterHalts dag254 (nextproof = 2) ↔ C254 1
```

Together with `Code254` and `TarskiFalsity`, the chain from the register
program to first-order semantics is kernel-checked. What remains for a Lean
end-to-end statement about the 253- or 254-state table is the TM layer
(literal table ↔ path semantics ↔ structured semantics, where the attributed
253 table's boot and register boxes already have Lean proofs) and the set
theory of the bundle (an irreflexive model of all decoded bundles from
Con(ZFC), and the bisimulation-quotient interpretation in the other
direction).

## L3: path semantics ↔ structured semantics

The Turing machine implements Wade's *path* semantics (`RegisterPath.lean`,
ported by the Codex lane); L2 is stated in the *structured* semantics of
`RMDag.lean`. `RMEquiv.lean` proves, for every DAG `p` read as a path program
`ofDag p nn`,

```text
halts_iff_iterHalts (W : WF p nn) (R) : Halts (ofDag p nn) ⟨[], R⟩ ↔ IterHalts p R
```

following the method of upstream `RMEquiv.v` in an independent Lean
development: a forward simulation by induction on the big-step derivation
(the path reaches the exit position of every structured exit, up to trailing
zero bits), and a backward simulation by strong induction on the number of
path steps with an inner induction on edge height (a `continue 1` restart
re-enters the same node with strictly fewer remaining steps). Paths are
compared up to trailing zeros because finishing a cdr leaves a zero bit
behind; the decoder's zero-padded `consume` is shown to read exactly the bits
of the leaf path. `WF` asks for a height table within the decoder fuel
`nn + 1` and break/continue bound tables showing that nothing escapes the
root; `wfCheck_sound` reduces it to a Boolean check.

`RMEquiv254.lean` (generated by `generate_rmequiv254.py`; the tables are
untrusted and re-checked by the kernel with `decide +kernel` in about thirty
seconds) instantiates this for the 219-node program: root height 96 of the
available 220, break bounds at most 1, continue bounds at most 2. Composed
with L2 and L1:

```text
path_halts_iff :
  RegisterPath.Halts pathDag254 ⟨[], nextproof = 2⟩ ↔ C254 F
```

Only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`) occur.

## L4: the literal decoder tree against the DAG

The literal machine table decodes the 6459-row tree `Prog254` (Codex lane,
attributed port of the public `Prog254.v`), not the 219-node DAG. The DAG
unfolds to exactly 6459 nodes, and `Prog254` is a pure tree that differs
from that unfolding only by local re-associations (with adjusted continue
levels) and reordered increments, so the two are related by a *segment
bisimulation*: between register tests a path program only increments,
breaks and continues, none of which reads a register.

`RMBisim.lean` (generic, the counterpart of upstream `Bisim.v`, developed
independently) proves that a segment bisimulation transfers halting from the
empty pointer for every register file. Its relation is symmetric by
definition, so one checked certificate gives both directions, where upstream
checks a mirrored certificate a second time. The Boolean checker reads a
balanced tree of entries, and the relation is *defined* as the set of pairs
its lookup returns, so soundness needs no invariant of the tree. For kernel
evaluation the programs are first unfolded into explicit decoder trees and
walked by structural recursion on the bit list (`walk_tree`); a first attempt
that indexed lists through `getElem?` was more than a hundred times slower.

`Bisim254.lean` (generated by `generate_bisim254.py` from the exploration in
`bisim254.py`; untrusted) holds 3010 related test-site pairs. Independent source
comparison found all pairs and both successor indices exactly equal to upstream
`Cert254.v`, including source order. The explorer regenerates them independently.
The kernel re-checks them in sixteen chunks with `decide +kernel`.

The checked current source shares the literal program's explicit tree through
`ActualTree254` and writes out the DAG's tree. Kernel definitional equalities
identify both with the actual decoders. The local full check passed with the
explicit pinned Lean 4.32.0 compiler in 9 minutes 15.41 seconds, excluding the
separately checked 53.53-second `ActualTree254` identity. Peak memory was 6.58 GiB.
The generator's default reproduces this checked source exactly; `--plain`
reproduces the earlier numerical-lookup module, whose original author reported
a 39-minute check. See `results/bisim254-optimized-verification.json` for exact
source hashes, commands, nine axiom reports and callers, including rejection of
mutations to each decrement successor and the all-zero logical-root endpoint.

A first version of the explorer modelled
pointer overflow as the empty pointer, while `incPath` returns the all-zero
pointer of the same length; the kernel rejected those entries, and the
corrected exploration gives the 3010. Composed with L3, L2 and L1:

```text
literal_halts_iff :
  RegisterPath.Halts Prog254.program Prog254.initial ↔ C254 F
```

With the Codex lane's `NativeTheory254.c254_refutation_iff`, the literal
register program from its public initial configuration halts iff the explicit
first-order theory `NativeAx` is refutable. What remains for the binary
machine is the TM layer (literal 253/254 table ↔ path semantics of
`Prog254`), and for ZFC the consistency transports between `NativeAx` and
ZFC.

## ZF proves the native axioms

*Correction kept for the record.* An earlier version of this section claimed
the Regularity transport and the file name `WellFoundedPart.lean`, which
already belonged to the Codex lane; that claim was withdrawn.

Every model of `SetTheory.ZFax_s` (ZF with Foundation and Power) is a model
of `NativeTheory254.NativeAx`, so by `theory_transfer`

```text
ZFNative.zf_refutation_of_native :
  BProv NativeAx [] fBot → BProv ZFax_s [] fBot
Endpoint254.literal_nonhalting_of_zfc_consistent :
  ¬ BProv ZFCax_s [] fBot → ¬ RegisterPath.Halts Prog254.program Prog254.initial
```

(the second through L4 and `NativeTheory254.c254_refutation_iff`). This is the
counterpart of upstream `S_sound.v`, which works in the constructible
universe; here the argument is semantic and needs no L:

* `NamedZF`: named formulas over `Form` (each binder moves its name to slot
  0), with an `atom` constructor embedding a De Bruijn matrix, and named
  Separation/Replacement. Every internal construction below is a readable
  formula with a one-line meaning lemma.
* `InternalOrd`: inside any model of the `ZFAxioms` bundle with set
  Regularity, ordinals (transitive sets of transitive sets), ordinal
  induction without transitive closures (an ordinal is its own container),
  trichotomy by a double induction, least elements of definable classes.
* `InternalRank`: `V_a = {z | z ⊆ V_c, c ∈ a}` by transfinite recursion with
  set approximations of Kuratowski pairs (unique by ordinal induction,
  extended by one stage, glued by Replacement; the gluing relation carries
  `Ord b` so that it is functional on *all* inputs).
* `ZFRank`: transitive containers by recursion along ω
  (`BoundedZFCConsistency.OmegaRecursion`, which needs neither Power nor
  Foundation), ∈-induction, the rank theorem, **Collection for every matrix**
  (outputs of least rank lie in one `V_β`) and power containers (`V_λ`, `λ` a
  limit above the rank, by iterating the successor along ω).
* `ZFNative`: irreflexivity is Foundation on a singleton; with the above,
  every `ZFax_s` model satisfies containers, full native GIC and IR.

The model is arbitrary: nothing assumes its membership is well-founded from
outside; every induction cuts its counterexamples out by Separation. Axioms:
`propext`, `Classical.choice`, `Quot.sound`. Each module compiles serially in
seconds. `Endpoint254` was checked here against the plain-lookup `Bisim254`
(commit 58d773ac24, 39 minutes); the current literal-tree `Bisim254`, whose
`literal_halts_iff` has the same statement, was checked by the Codex lane
(`results/bisim254-optimized-verification.json`, 6.9 GB peak, too large to
repeat on this 13 GB machine alongside other builds).

A subsequent independent local replay freshly checked all nine newly imported
units, including `Basic`, `OmegaRecursion`, `Choice` and the six ZFC research
modules, against the current source-matched optimized `Bisim254` object.
All nine passed in about nine seconds; five axiom audits and two direct callers
also passed. Their exact sources, commands and outputs are in
[the fresh verification record](results/zfnative-fresh-verification.json).
This replay reuses the other 117 previously checked source-matched imports;
it does not rebuild the entire expanded library. A separate full-source
mathematical review of the named-formula and rank construction is recorded in
[the independent review](results/zfrank-independent-source-review.json).

**Status of the goal.** The checked `WFTheory.c254_refutation_iff_zf` now
identifies the exact numerical calculus with ordinary ZF refutation, including
Foundation and Power. It combines this lane's `ZFNative` direction with the
[direct well-founded model](wf_model.md) of the native CP/GIC quotient.
For the literal register program, non-halting is therefore equivalent to
`Con(ZF)` and follows from `Con(ZFC)`. Choice removal is the remaining semantic
transport to full ZFC. The actual252-state binary table now has the
[closed `BinaryPerm252` endpoint](binary_perm252.md): complete blank bootstrap,
all8,391 decoder guards and unbounded simulation give blank nonhalting iff
`Con(ZF)`, with no coverage premise. PA internalization is an additional
proof-code obligation.

## The constructible class is a model of ZF

The Choice transport (`foundation_choice_route.md`: a ZFC refutation yields a
ZF refutation) is semantic in this lane: the constructible class of a model
of `ZFax_s` should be a model of `ZFCax_s`. The ZF half is proved.

* `TransRec`: transfinite recursion `stage a = ⋃ {G (stage c) | c ∈ a}` for
  any operation `G` whose graph is a named formula (`DefOp`); `InternalRank`'s
  cumulative hierarchy is the case `G = P`.
* `ConstructibleDef`: `DefinableIn X S` through
  `BoundedZFCConsistency.InternalSatTotality.SatIn` (certificate satisfaction
  of coded formulas over set-sized structures, total and single-valued even
  on nonstandard codes), embedded into named formulas as atoms; the stage
  operation `Gdef X = {S ⊆ X | S = ∅ or S definable over X}`.
* `Constructible`: the truth bridge (for a standard formula, `SatIn` of its
  code is satisfaction with quantifiers bounded by the carrier), `L_a` and its
  basic laws, `L_a ∩ Ord = a`, stage bounds, pairing, union and power in L.
* `ConstructibleReflect`: the **reflection theorem** for the L-hierarchy. A
  limit `β` containing the least witness stage, over every internal
  environment on an earlier stage, of each quantifier body (and its negation)
  of `φ` reflects `φ` between `L` and `L_β` (a Tarski-Vaught induction); such
  `β` exist above every ordinal by iterating the definable closing step along
  ω. No closed-unbounded classes are needed.
* `ConstructibleZF`: Separation in L (reflect, then the separated set is
  definable over `L_β`), Replacement in L (collect images in the model, bound
  them in a stage, separate), and `L_models_ZF`.

**What remains: AC in L.** The selector principle (`ChoiceSem`) needs a
well-order of each `L_α` that is itself constructible. Three ingredients are
missing: (i) a well-order of the internal formula codes, which are hereditarily
finite sets, so new elements of `L_{α+1}` can be compared by their least
definitions; (ii) definitions with *finite* parameter tuples (internal finite
sequences with their lexicographic order), since environments over `ω` cannot
be well-ordered lexicographically, or else an internal proof that a coded
formula depends on finitely many variables; (iii) absoluteness: the hierarchy
computed inside the constructible model agrees with `L` (agreement of every
internal operation and of certificates between the two), so that the
canonical well-order lies in `L`. A Gödel-operations presentation would trade
(i)-(ii) for Gödel's normal form theorem. Upstream's `zfc/` spends about 7.6k
Coq lines here. Mathematically the goal does not wait on it: non-halting is
equivalent to `Con(ZF)` (`WFTheory.c254_refutation_iff_zf` with L4), and
`Con(ZF) ↔ Con(ZFC)` is Gödel's 1938 theorem, whose `L ⊨ ZF` half is now
formalized here.

The constructibility modules received an
[independent source review](constructible_choice_review.md). The review found
no defect in their internal recursion and reflection arguments. For the
remaining definable well-order, it identifies an explicit prerequisite:
uniform internal finite support for `SatIn` on every internal formula code,
so definitions use finite parameter tuples rather than arbitrary full
omega-environments. Fixed-standard-Form support lemmas alone do not supply it.
The review does not claim Choice or a new compiler check.

**Claimed by this lane (Choice transport, in progress).** New modules, in
dependency order: `SatSupport.lean` (uniform finite support of `SatIn` on
every internal code, by code induction), `InternalWO.lean` (internal
well-orders: append, lexicographic product, least-key pullback, chain union),
`CodeOrder.lean` (a well-order of the pair closure of `ω`, hence of the
formula codes), `ConstructibleOrder.lean` (the canonical well-order of each
`L_α` and `ChoiceSem` in any ZF model satisfying `V = L`),
`ConstructibleAbs.lean` (absoluteness of certificates, codes and `Def`
between `M` and its constructible class, hence `V = L` in `L`), and
`ConstructibleChoice.lean` (`L ⊨ ZFC`, the Choice transport
`BProv ZFCax_s [] ⊥ → BProv ZFax_s [] ⊥`, and the literal Con(ZFC)
endpoint).
