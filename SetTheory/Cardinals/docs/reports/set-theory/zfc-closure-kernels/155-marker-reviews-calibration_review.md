# Independent review of the exposed-marker K217 calibration

## Conclusion and exact object

The proposed 217-state machine has a complete ordinary mathematical calibration chain to syntactic consistency of ZFC. I found no additional consistency, soundness, well-formedness, or standard-model assumption in the new steps. The result should be stated as a **ZFC-formalizable ordinary proof with executable certificates**, not as a newly compiled exact-K217 Lean/Rocq theorem or an internal PA theorem.

The reviewed frozen identities are:

- Native table: `c902a3c5e81176230a2213d631e2e691573c167fb03e9bdb09ef5c88154f3099`.
- Canonical table: `a2b8bc2d4822962ad32819fe475a7d62b0d483bc4f41977bff292742f70b3e8c`.
- Source: `9eac900e83742470893ea433cb0868e9ff6296f905cd6f3359b7a2c0e3114655`.

The canonical machine has working states 0 through 216, initial state 0, halt label 217, and exactly 434 transitions. Its tape alphabet is `{0,1}`; the tape is two-way infinite and entirely zero initially. The native table uses nonconsecutive labels and halt 254; the checked bijection does not change the number of states.

## 1. What the logical replacement proves

Let C be the inherited numerical C222/K219 calculus and D its dominated-row replacement. D retains truth 0, numerical modus ponens, theorem-only generalization, the seven other rows, and the literal two-gated seed bundle. Only the fourth-parameter row is restricted:

`L(A,B,C,U) = ((C -> U) -> A) -> ((A -> C) -> (B -> C))`, with `U <= A`.

The 3,728-node certificate derives the unrestricted L schema from these restricted instances. Both supplied forward checkers were rerun successfully during this review. Every restricted leaf has either `U=0` or U as a literal implication subterm of A. Since `I(x,y)=4P(x,y) >= x,y`, every such leaf satisfies its side condition for every assignment of natural values. The sole normalization is `I(0,0)=0`. The certificate's metavariable named 0 is distinct from its truth constant.

Thus the finite proof certifies a universally instantiable schema. Substitution is a metalevel operation on a proof valid for every assignment; it is not an extra arbitrary-substitution rule added to the numerical calculus. Modus ponens and substitution steps can be expanded into native derivations. Induction on derivations gives, for every natural n, `D proves n iff C proves n`. This includes undecodable numbers and aliases. The restriction does not presuppose a formula decoder.

The inherited calibration supplies `C proves 1 iff a StandardZFC refutation exists`. The relevant reviewed endpoints are `Complete222.thm222_complete`, `Sound222.thm222_sound`, and their combined theorem. Both directions concern existence of finite refutations. In particular, the upper direction transports a native refutation through the decoded comparison theories to a ZFC refutation; it does not assume that all ZFC theorems are true. Keeping the exact old gated bundle and retained rows is essential to this transfer.

## 2. Why the altered source enumerates the right refutations

The common-input command calibration remains applicable because the new source has exactly the same guarded ordinal control graph and primitive operands as the dominated source. At AX, wire fields `(c,z,y,x)` produce `U=d+z`, `A=U+x`, `B=h+y`, and `C=c`. The generalized formula uses the old cached theorem h. Hence every raw AX produces an allowed row, and the top/cache/stack theoremhood invariant is preserved. Only NIP with cached code 1 can halt.

The converse is not inferred from an informal claim of exhaustive enumeration. The inherited common-input argument gives explicit strong blocks for truth, every row, the gated bundle, generalization, and modus ponens. A block for F either halts earlier or restores the underlying stack with top F and zero counter/cache. Early halting is allowed in this contract, so no proof of consistency is required while constructing blocks.

For a refutation block, prepending `AX(0,1,1,Y)` resets the counter/cache for every incoming retained tuple. The resulting candidate number is `P(3,P(1,P(1,P(Y,R)))) >= Y`. This gives a cofinal family of halting candidates. Strict draining of finite command lists then handles an arbitrary initial next-candidate cutoff. The actual seed's nonzero next-candidate and additive counter, both 3, are therefore permitted. Top, formula stack, and cache are all zero, so the required theoremhood invariant holds immediately.

## 3. The source change and physical fold

At source path `11101001001110010`, the local spine changes from

`(A,(((B,C),D),E))` to `((A,B),((C,D),E))`.

The five components have 14, 27, 53, 374, and 3,682 leaves. Each has zero escaping break count, zero escaping continue count, and no halt. This is a composition of normally returning programs. Independently computing the complete control graph with structured break/continue continuation stacks confirms equality for all 4,751 primitive occurrences, with the same register operands. The 186 primitive addresses outside AX remain literal. This supplies an all-register source equivalence, not just a common flat instruction word.

Four literal decoder-row edits implement the new source in a 218-state prefold table. The fold then identifies native states 69 and 400. Before folding, their only incoming rows respectively write 1 and 0 and move right. Thus the cell immediately left of the new head is a guaranteed context marker. On read 1 their outgoing rows already agree. On read 0, the new machine steps left into decoder state 188 and uses the exposed pair of children to recover the correct old target: 104 for marker 0 and 105 for marker 1. It returns to the old final head position after three steps and restores both inspected cells exactly.

This fold proof is valid on arbitrary tapes for computations beginning at initial state 0, because every entry obtains its marker from the preceding transition. It is not an equivalence for an arbitrarily supplied configuration already in state 69 with an unconstrained left cell. No extra state is hidden in the context: it is a tape bit written by an existing transition.

## 4. Runtime, initialization, and final composition

The frozen runtime receipt binds the exact native table and source hashes above and reports all 6,176 guarded cases proved. These quantify over independent natural register values, arbitrary natural gap, and an arbitrary nonempty finite spare list. The proof rules use literal transitions and induction over unary runs and list length. The finite case inventory was independently checked for exact ordered coverage; all duration coefficients are nonnegative and every constant term is at least 13. Thus the runtime argument supplies finite, positive simulations of source primitives. These are symbolic mathematical certificates, not bounded-value tests, and they have not been checked by a proof-assistant kernel.

An independent sparse replay verified all 312,617 startup transitions and reconstructed the complete final tape. The resulting boundary is native dispatcher 84, head -5, root source address, gap 80, registers `[3,0,0,0,3,0,0,0,0]`, and 130 spare blocks each of value 1. The representation has exactly 277 one-cells and every other tape cell zero. This verifies the physical frame, not merely the nine numerical registers.

Composition now gives

`BlankHalts(M217) iff D proves 1 iff C proves 1 iff a ZFC refutation exists`.

Taking the negation of the last existential is exactly the chosen syntactic `Con(ZFC)`. All new arguments use finite arithmetic data, finite proof transformations, and induction on natural numbers or finite lists, so they are available within ZFC. The theorem does not assert or use `Con(ZFC)` itself. No omega-consistency or semantic soundness assumption is needed to prove the equivalence. An unconditional claim that the machine actually never halts would be a different assertion and is not part of this construction.

## Review artifacts

`review_k217.py` imports no inherited source/compiler helper. It checks the literal table changes, incoming-marker premises, two-cell routing, source rebracketing and control graph, canonical bijection, full blank replay, and complete frame. Its result is `k217_review_checks.json`. The universal runtime proof was produced by the separate runtime checker; this review checked its binding and case coverage, not a second independently implemented universal runtime engine.

The separate fixed-core experiment is not a premise. Splitting general membership vacuity from the fixed-label nonlogical core is logically viable, but the measured direct sources have 210 or more distinct subtrees and do not improve this 217-state construction.

## Portable audit command

The checker takes an explicit package directory and an optional receipt filename; it contains no absolute workspace path and uses only Python's standard library:

```sh
python review_k217.py /path/to/k217_exposed_marker --output k217_review_checks.json
```

The final package layout places `baseline218.native.tm`, `baseline_sites218.json`, `prefold218.native.tm`, `k217.native.tm`, `k217.tm`, `sites217.json`, and `canonicalization.json` under `machine/`, with `startup.json`, `runtime.json`, and `runtime_cases.json` under `evidence/runtime/`. The older flat frozen directory with `runtime/` is also accepted. The six frozen table/source byte hashes are checked before the audit. The first positional path may be relative. Optimized Python is explicitly rejected before any assertions run.

## Optional future appendix: one-parameter nonlogical core

There is a rigorous formalism simplification, separate from the state saving. Put `N(X)=I(X,1)`, `V(a,b,c)=I(R(a,b),Q_c R(a,b))`, and let `J(a,b,c)=nks222(a,b,c)` have its inherited exact numerical definition. Thus the old seed bundle is `N(I(V(a,b,c),J(a,b,c)))`.

**Fixed-core theorem.** Form a calculus Cfix by retaining every old clause except the bundle clause, which is replaced by:

1. `V(a,b,c)` whenever `c != a` and `c != b`;
2. `N(J(1,3,c))` for every natural `c >= 4`.

Then ZFC proves that Cfix has a derivation of code 1 if and only if ZFC has a refutation. The unrestricted L row may also be replaced by the calibrated dominated row.

For the upper direction, `Interp222.bundle222_proj` supplies each new clause from an old bundle. The fixed labels satisfy the old inequalities when `c>=4`. Consequently every Cfix derivation is an old-calculus derivation.

For the lower direction, audit the old completeness proof modularly. Its propositional and equality lemmas in `CD222.v`, `Prop222.v`, and `G222.v` do not invoke the bundle clause. In `Interp222.v`, the only bundle invocation supplies the general fresh membership-vacuity row, which Cfix now has directly. Thus the full pure-logical interpretation is retained. In `Complete222.v`, the only additional invocation occurs at `Q_seed`: it asks for `bundle222(1,3,seed_code(phi))`. The same file proves `seed_code(phi)>3`. Cfix has the corresponding V and N(J). From these two formulas it derives `N(I(V,J))`: under the temporary assumption `I(V,J)`, obtain J by MP with V and then 1 by MP with N(J); discharge that one assumption with the ordinary K/S deduction transformation. This uses no generalization on an open assumption. The remainder of `Complete222` is unchanged. This proves the required refutation transfer.

The result claims equiconsistency, not equality of every theorem code. It removes the varying labels a and b from the nonlogical core, but retains both inequalities for the separate membership-vacuity row. Those gates cannot simply be discarded on the basis of this theorem. A direct implementation emitting `N(J(1,3,c+4))` followed by the original gated V costs 211 distinct source subtrees before further source search, so this optional theorem does not contribute to the 217-state result. Its lower proof is an ordinary adaptation of the displayed source modules, not a newly compiled Cfix Rocq development.
