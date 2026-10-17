# Proof boundary and transfer lemmas for a smaller consistency machine

Audit basis: ProveIt revision `beb2c633ae57a0883d28fb6d0c75342d08cfdeda`, inspected on 2026-10-17. This is an intermediate research note, not a newly kernel-checked theorem or a claim that a machine below 252 states has been constructed.

## 1. Exactly what the baseline proves

The canonical `candidate-permutation252/zfc_permutation252.tm` is a binary, one-tape machine with 252 working states, start state 0, blank tape and head 0. Its SHA-256 is `8dae0c2359aa8bf87d32543b9e53e1f87fe4716c016a4e2fd174bfe09e520797`. The old-label table has working labels `{0,...,253} \ {5,8}`, start 64, halt label 254 and SHA-256 `939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713`. It executes 82,552 actual blank-tape moves before reaching its certified complete root frame.

The checked external theorem is

```
(not exists t, (machinePerm252.run t).state = none)
  iff not BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot.
```

`BinaryPerm252.blank_halts_iff_register` composes the actual bootstrap, complete source-tree coverage, whole-tape representation, positive-segment simulation and the exact original literal register program. The next interfaces are `blank_halts_iff_c254`, `blank_halts_iff_checked_refutation`, `blank_halts_iff_native_refutation` and `blank_halts_iff_zf_refutation`. `BinaryZFC252` and, independently, `ChoiceCalibration254` supply the ZFC comparison through a constructible submodel.

This is stronger evidence than a finite simulation or an abstract uninstantiated compiler correctness lemma: no bootstrap, coverage, model-existence or Choice premise remains in the endpoint. Its reported Lean axiom dependencies are the standard `propext`, `Classical.choice` and `Quot.sound`. Nevertheless, the result is an external Lean metatheorem, not a serialized derivation of a sentence in the repository's internal ZFC proof calculus. The maintained note explicitly says that no internally serialized ZFC machine statement is asserted. The repository's stronger original PA-internal target also remains open. Its newer internal arithmetic runtime and scheduler developments do not silently close their still-missing comparison.

An arbitrary Lean theorem using only those three axioms must not be presented as automatically a ZFC theorem: a blanket interpretation of Lean's universe hierarchy is a separate foundational question. A particular ordinary set-theoretic mathematical proof can instead be expressed directly in ZFC as described next.

## 2. A precise theorem that ZFC can prove

Fix conventional finite Gödel codings of formulas, proofs, machine descriptions and finite machine traces. For a recursively axiomatized first-order theory T, let `Prf_T(p,bot)` be the arithmetical predicate checking a finite refutation and define

```
Ref(T) := exists p in omega, Prf_T(p,bot),
Con(T) := not Ref(T).
```

For a fixed literal binary machine M, let `Trace_M(t,c)` be the recursively defined run graph from the canonical blank configuration, including the last write and move of a halting transition, and define `Halt(M) := exists t,c (Trace_M(t,c) and c.state=halt)`. Configurations can use an integer head and a finite-support Boolean tape, or two natural-number tape halves. Finite-support functions, finite sequences, their encodings and the primitive recursive trace checker are sets definable in ZFC.

For a nonempty set A and relation E contained in A times A, write `Mod_T(A,E)` for the *set-coded* assertion that the first-order structure `(A,E)` satisfies every coded axiom of T. Satisfaction here is the usual recursion on finite syntax with assignments into the set A. It is not a truth predicate for the entire ambient universe. This distinction prevents a Tarski or reflection shortcut.

**Set-model transfer lemma, internal to ZFC.** Let S and T be fixed recursively axiomatized theories in countable first-order languages. Suppose ZFC proves

1. `forall A,E, Mod_S(A,E) -> exists B,F, Mod_T(B,F)`;
2. `forall B,F, Mod_T(B,F) -> exists A,E, Mod_S(A,E)`.

Then ZFC proves `Con(S) iff Con(T)`, and consequently `Ref(S) iff Ref(T)`.

**Proof.** ZFC proves first-order soundness and completeness for set-coded countable syntax. Thus for either fixed theory U,

```
Con(U) iff exists A,E, Mod_U(A,E).
```

For the forward implication of this equivalence use the Henkin construction conditional on `Con(U)`; the domain can be chosen countable. For the reverse implication apply satisfaction soundness to an alleged finite refutation in the nonempty set model. Apply transformations 1 and 2 between these two model-existence assertions, then classical contraposition. No unconditional model of ZFC is introduced, and no soundness assumption about the ambient ZFC theory is used. All steps are statements and proofs *within* ZFC. QED.

**Machine transfer corollary, internal to ZFC.** If in addition ZFC proves `Halt(M) iff Ref(S)`, then it proves

```
not Halt(M) iff Con(T).
```

This corollary makes the deliverable obligation precise. It is not enough to establish two ordinary external truth values or equiconsistency in an unspecified stronger metatheory; the stated simulation and model transformations must be formulated and justified in ZFC.

### Application to the existing semantic argument

Use the literal native theory `NativeTheory254.NativeAx`: universal closures of the container principle CP, every native first-order formula instance of GIC, and raw irreflexivity. This is a first-order effective schema, not comprehension over arbitrary external relations. The proof path to express in set-coded mathematics is:

* finite C254 proof trees/refutations correspond to native first-order refutations;
* every ordinary ZF model gives a native model (`ZFNative` plus the native syntax adapters);
* every native numerical model gives the actual CP/GIC quotient and its **internally** well-founded part, a ZF model (`WFModel` and `WFTheory`);
* the constructible substructure defined **inside that ZF model** gives a ZFC model (`ConstructibleZF`, `ConstructibleAbs`, `ConstructibleOrder`, `ConstructibleChoice`);
* every ZFC model is a ZF model by forgetting Choice.

These set-model constructions are conventional ZFC mathematics. Their external domains need not be well-founded or standard. Do not substitute an external well-founded part or `L intersect A` for the repository's internal constructions: those are different objects and need not preserve the relevant theory. A subtype of a set-coded model is a subset of a set, and an equivalence quotient is a set of equivalence classes; neither calls for an inaccessible cardinal or a universe as a set.

The remaining **written-proof** task is to state the codings and uniform satisfaction lemmas, and explain that the already checked structural arguments use only these set-sized operations and induction/recursion available in ZFC. The remaining **machine-checked internal-proof** task is stronger: construct internal formula/proof objects and check their derivations in the chosen ZFC proof calculus. The first can be a rigorous mathematical proof without the second, but a report must not describe the second as completed when it is not.

This route is materially easier than PA internalization: the above proof deliberately uses set-model existence and completeness, which are available in ZFC. It does not produce a primitive recursive translator from arbitrary internally coded ZFC refutations to numerical refutations, or a PA proof of such a translator's totality. Those additional properties are unnecessary for the user's present ZFC target and remain separate if the stronger repository target is retained.

## 3. Exact inheritance by a new machine

If a new literal machine N is proved in ZFC to halt exactly when the old M does, the consistency equivalence transfers immediately. This prevents having to redo CP/GIC, Foundation and Choice proofs for every machine reduction. The new obligations concern finite tables, full tapes and unbounded runtime only.

### 3.1 The cheapest case: a guarded state quotient

Suppose N deletes state d and identifies it with state r. Let pi map old states to new states and map halt to halt, with no working state mapping to halt. Keep tape and head unchanged. It suffices to prove an invariant I of every old blank-run configuration such that for each configuration in I, if the old transition on its scanned symbol is `(write,move,q')`, the new transition on `(pi(q),symbol)` is `(write,move,pi(q'))`. The projected blank configurations must agree.

Induction on time then proves literal equality of projected configurations at every time; this gives both halting directions. Only reachable guarded uses of `(state,symbol)` matter. One does not need the two complete rows of d and r to be syntactically identical on unreachable inputs. This is a viable certificate shape when a deletion becomes possible after a source phase invariant removes an impossible state/symbol case.

The invariant cannot be justified by observing a long finite run. Use the full source-site symbolic proofs, register-box contracts and bootstrap, or an independently proved inductive phase relation. Boot may exercise pairs that are unreachable during the eventual runtime, so it must be included separately.

### 3.2 A more flexible positive-segment relation

Let A be an abstract source configuration space, `next : A -> option A`, and `Terminal` its designated halt predicate. Let R relate source configurations to configurations of N. The following four obligations are sufficient:

1. **Active endpoints:** R(a,c) implies c has a working state.
2. **Positive simulation:** if R(a,c) and next(a)=some b, there is k>0 with R(b,run_N(c,k)).
3. **No accidental stop:** if R(a,c) and next(a)=none, then Terminal(a).
4. **Actual halt:** if R(a,c) and Terminal(a), then N eventually performs its actual halting transition from c.

Together with a related actual blank-prefix endpoint these imply `Halt(N) iff AbstractHalt(a0)`. Forward simulation proves the abstract-to-binary implication. For reflection, if N halts at time t, an active endpoint of a simulated source prefix must occur before t because halted configurations are absorbing. Positive segment lengths force at least n binary moves for n abstract operations. Induction below the finite halting time therefore reaches a designated terminal source configuration. There is no missing fairness assumption or need for a uniform bound on segment lengths.

The repository already contains this exact general proof as `RuntimePerm252.PositiveSimulation` and `RuntimePerm252.halts_iff`; despite its name it is generic in the machine state count. Reusing it is the easiest sound route for a 251-state candidate whose instruction implementations or continuation phases change. Its source is `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RuntimePerm252.lean`.

An appropriate R may identify different physical spare suffixes, account for a different head offset, use a different encoded PC, or compare two continuation phases after scratch disposal. Every such freedom must be part of R and preserved by the proof. Exact-PC mismatch alone need not refute semantic correctness. Conversely, a changed formula register cannot simply be renamed disposable scratch. A simulation where some operations take zero moves needs a separate well-founded bound on consecutive zero-move steps; keeping positive segments avoids that issue.

### 3.3 A concrete development order

1. Freeze N's literal table, state convention and SHA-256; count actual working states.
2. Replay its complete blank bootstrap into a whole frame, with a trace certificate.
3. Reuse untouched register-box contracts by table identity on every required transition pair. Prove any changed box separately for unbounded register values and arbitrary valid spare suffixes.
4. Supply either full accepted-site coverage with the new relation, or a source-control invariant and guarded coverage sufficient for every reachable abstract step. The old unconditional `Covered` theorem cannot be weakened merely by omitting cases from a test.
5. Instantiate the generic positive simulation and compose its halting theorem with the old numerical/native/ZFC endpoint.
6. Present independently which portions are mathematically proved, executable audits, and new Lean-kernel checks.

The prior source analysis removes six guards through an overapproximation using register classes `{0,1,>=2}`. It proves no general minimality result. The existing 503 focused fold checks all fail the old bounded exact-contract checker. Further progress would require a stronger invariant, jointly compensating edits, a changed representation or a semantic continuation relation; a re-run of the same rejected family is not a novel construction.

## 4. Full-frame and dirty-start obligations

`Permutation252Frame.DispatchFrame` specifies the entire infinite tape, represented by a finite zipper and zero exterior. At dispatch the marker is immediately left of the head. To the right are the PC word, a zero gap, one header 1, then unary register blocks encoding `value+1` ones each with a preceding separator 0. There are nine primary blocks in physical order `[2,8,1,4,3,7,0,5,6]` of logical registers, followed by an arbitrary finite list of spare block values. The length of PC plus gap is at least 40. `Related` also requires `RegisterPathClean.Clean`: surplus PC bits after the consumed leaf are zero.

The physical map for logical `[N,T,W,A,D,H,X,Y,L]` is `[6,2,0,4,3,7,8,5,1]`. Logical registers at indices 9 and above must be zero. Arbitrary *physical* spare values are permitted; they are not additional nonzero logical registers. Positive decrement may append a zero spare. There is no extra all-spares-zero or capacity premise. Arbitrary isolated tape marks outside the valid suffix are not permitted. A small gap at an interior PC cannot be misread as an empty root with adequate padding.

The older general dirty-root result `DirtyProgram254.iter_halts_iff` permits arbitrary values of N,A,D,X,Y,L but still requires `C254(T)`, `C254(H)` and a `Good(W)` formula stack. Zero T,H,W suffice. The fact that a scalar W is a theorem code does not imply W is a safe encoded stack: the stack is recursively unpaired.

### A stronger already-proved six-seed relaxation

`DirtyReset254.six_dirty_starts_iff` states precisely

```
forall n t stack d h,
  n in [0,1,2,4,5,6] ->
  EnumSafeStart254.HaltsFrom <0,n,t,stack,d,h> iff C254 F.
```

Thus pointer PL=0 and candidate NP in `{0,1,2,4,5,6}` allow arbitrary top, whole stack, additive parameter and cache. Candidate 6 produces a sufficient safe prefix above the dirty old stack; the prior small candidates reach it without an unsafe halt. Candidate 3 is deliberately absent: `three_cache_one_halts` proves an immediate halt from NP=3/cache=1 with arbitrary other fields.

For a clean literal-program root, use logical vector

```
[N,T,W,A,D,H,X,Y,L] = [n,t,stack,0,d,h,0,0,0],
  n in {0,1,2,4,5,6}.
```

The all-zero scratch and command-control fields make this exactly an `L2.toAS` encoding of the enumerator state in the six-seed theorem. Compose `L2.iter_iff`, the path/iteration equivalence in `RMEquiv254`, and `Bisim254.prog254_halts_iff` to transfer it to the original literal `Prog254.program`. The all-sites runtime then transfers it to a valid binary frame. This extends bootstrap targets beyond the baseline all-zero frame, while requiring no new theory calibration. It is not justified by `DirtyProgram254.six_nonformula_iff` alone: that theorem fixes the formula fields instead of using the reset argument.

Relevant exact source paths under `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`:

* `DirtyReset254.lean`: six dirty starts and NP=3 counterexample.
* `EnumStackCount254.lean`: actual candidate ordering and safe stack credit.
* `L2Root254.lean`: `SetTheory.BusyBeaver.ZFC.L2.iter_iff`, with `L2.toAS s = ⟨s.np,s.tw,s.ws,0,s.d,s.h,0,0,s.pl⟩`; its import is `BusyBeaver.ZFC.L2AxiomsEval254`.
* `RMEquiv254.lean`: `path_halts_iff_iter`.
* `Bisim254.lean`: `prog254_halts_iff`.
* `Permutation252Frame.lean`: complete tape and physical register map.
* `RuntimeInstancePerm252.lean`: whole-frame binary equivalence.

## 5. Limits of independence claims

For a theory T satisfying the usual second-incompleteness hypotheses, an internal theorem `not Halt(M) iff Con(T)` implies that consistency of T prevents T from proving nonhalting. It does not, merely from consistency, prevent T from proving the false Sigma1 sentence `Halt(M)` or equivalently `not Con(T)`. An appropriate Sigma1-soundness assumption supplies that other unprovability direction. The requested equivalence is the clean target; do not silently strengthen it to two-sided independence under consistency alone.

No graph-reachability census, failure of exact state bisimulation, bounded mutation search or finite no-halt trace proves a 252-state lower bound. Similarly, a tiny weakly universal machine is not a smaller blank-tape consistency machine unless all background/input information and its initializer are charged to the state count.

## Sources inspected

All repository paths below are pinned to `beb2c633ae57a0883d28fb6d0c75342d08cfdeda` and can be cited as GitHub permalinks.

* `Computability/BusyBeaver/Research/ZFC/candidate-permutation252/README.md`
* `Computability/BusyBeaver/Research/ZFC/choice_calibration254.md`
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/BinaryPerm252.lean`
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/BinaryZFC252.lean`
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ChoiceCalibration254.lean`
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/NativeTheory254.lean`
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254Proof.lean`
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/WFTheory.lean`
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean`
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RuntimePerm252.lean`
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Permutation252Frame.lean`
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RuntimeInstancePerm252.lean`
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DirtyProgram254.lean`
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DirtyRoot254.lean`
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DirtyReset254.lean`
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/EnumStackCount254.lean`
* `Computability/BusyBeaver/Research/ZFC/permutation252_phase_analysis.md`
* `Computability/BusyBeaver/Research/ZFC/permutation252_spare_fold_search.md`
* `Computability/BusyBeaver/Research/ZFC/permutation252_context_search.md`
