# Independent review of the final strict checker profiles

## Result and limits

The reviewed programs establish a limited implementation improvement for the existing native presentation of full first-order intuitionistic primitive recursive arithmetic. They preserve the strict public contract: a complete JSON document, an exact integer/list alphabet throughout the document, and a closed canonical native Eq/D goal with zero uniformly represented by 1. The accepted public theorem language remains that of the inherited native calculus.

The current strict coordinatewise comparison changes from **317 tokens / 356 AST nodes / 597 normalized bytes** to **306 / 348 / 595**. These are minima attained by **different programs**, not a triple attained by one checker. A fourth profile, 313 / 353 / 701, is simultaneously below the prior strict token and node coordinates, with a larger byte count.

The separate compact comparison **239 / 256 / 461 is not beaten**. The compact and strict programs have different input contracts. No new logical or arithmetic axiom has been deleted, no globally simplest axiomatization has been proved, and no mathematical complexity lower bound is claimed. The mathematical constructions reused below already occur in the pinned repository; the new contribution is their composition in these measured strict implementations.

## Sources and independently reproduced sizes

The source comparison is pinned to commit `798856e4ef2d02b7f9c0f1660828c5ce58f277f2` of `VladimirReshetnikov/ProveIt`, directory `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA`. Its current incoming `ipra_validated_arity_refinement_2026-11-13.zip` supplies the strict 317 / 356 / 597 comparison. The README and some earlier article census figures are older than these incoming sources.

All four final profiles were independently remeasured with **CPython 3.12.14**, using `ast.unparse(ast.parse(source)) + '\n'`, significant lexical tokens, and every node returned by `ast.walk`. None of the four source modules contains a docstring affecting normalization.

| Profile | Reviewed source basename | Tokens | AST nodes | Normalized bytes |
|---|---|---:|---:|---:|
| Token profile | `split.py` | 306 | 362 | 668 |
| Joint token/node profile | `checker_313_353.py` | 313 | 353 | 701 |
| AST profile | `strict_conditional_major.py` | 330 | 348 | 681 |
| Byte profile | `strict_normalized_terminal.py` | 329 | 372 | 595 |

The raw source SHA-256 hashes at review time are:

| Source | SHA-256 |
|---|---|
| `split.py` | `7a904fb453c260fa6946652cecb38690946dde8c8db0bbd0cabdccd9c0f42b61` |
| `checker_313_353.py` | `b98bde1fb45865eea13c87eff47d46b73055a23e60305dd633758cbf2ce0ddd3` |
| `strict_conditional_major.py` | `d69137e9d2a3ced788423932102dddae11d9e86b85607a0110c21575dcec3258` |
| `strict_normalized_terminal.py` | `0e32e3de2c9b03aa57d1cae91bf0bf8f8a39e919c8e76b7b8622d996770c0535` |

## 1. Three-field token and joint profiles

These programs use three fields `(s,u,t)` instead of supplying a fourth independent major formula. They apply the existing three-field idea from Article Chapter 11, subsection `cert:sec:three-field`, to a later strict native checker. The empty list and integer zero are distinct case/progress markers; they must not be identified merely because both are false-valued.

Write `O_k(a;t,d)` for the inherited uniform-zero opener, and call a raw expression closed at floor k when its auxiliary reading contains no hole. At entry, the no-image opening makes the goal closed. Context entries are closed by the invariant. The neutral resource 0 is then retained.

### Soundness for every successful raw input

Induct on the finite tree of successful calls, using the article's semantic-opening, slot-exposure, freshness and zero-instance-supply lemmas.

**Endpoint match.** If `O_k(t;u,0)` equals the current goal, the checker changes the minor goal to `O_k(t;s,0)`, reconstructs the major `[s,u]` for true-valued s or `[t,t,t]` for false-valued s, and sets u to zero. The major is recursively proved in the unchanged context. Under the sorted reading these are respectively equality transport and closure specialization. The repeated major added to the context has arity 6 or 9 and reads as the neutral theorem. The minor is closed at the old floor, so allocating a fresh name later does not change its reading.

**No match, u false, s true.** The checker recursively proves s. A unary s is a paired formula; its threefold repetition opens the corresponding conditional closure at the new eigenparameter, giving the inherited D-elimination argument. At every other raw arity the repeated expression has the inherited neutral reading.

**No match, both fields false.** The checker opens the matrix at witness t before decreasing the floor. The witness therefore cannot refer to the newly allocated name. A binary matrix may receive either its base or progress instance according to the marker. Genuine compound matrices of arity 1 or 3 receive the base instance. Unexpected raw arities are handled by the neutral-reading cases already present in `cert:thm:base-sound`. Thus progress is never granted at an arbitrary compound native formula.

**No match, u true.** The checker constructs the inherited computation hypothesis H. The new mode may open H at the fresh name b rather than at zero when s is true-valued. This is justified by **`cert:lem:zeroinstance`**: if that opening succeeds, H(0) is an I0 or IS computation axiom. By freshness the old context and goal contain no b. Apply the continuation induction hypothesis in the ordinary realization, specialize b to zero, and cut the computation axiom using **`cert:lem:supply`**. H(b) itself is not assumed to be an axiom; raw dummy-slot references make that stronger assertion unjustified.

This proof covers every successful integer/list packet, including noncanonical auxiliary data. It is not just an argument for the six intended instruction tags.

### Canonical completeness

Compile an ordinary native derivation using these records:

| Inference | Record |
|---|---|
| Transport, source s, target u, template F | `[s,u,F]` |
| Closure specialization, target u, matrix B | `[0,u,B]` |
| D elimination, major M | `[M,0,0]` |
| Computation, predecessor s, seed u, body t | `[s,u,t]` |
| D introduction by cases, witness w | `[0,[],w]` |
| Equation progress, witness w | `[0,0,w]` |

Canonical term codes use scalar leaves and arities 1 or 3, whereas every canonical native formula contains a binary equation node. This excludes accidental endpoint matches for computation and introduction packets. A canonical seed is true-valued because zero is encoded by 1. Canonical computation hypotheses are already closed at the old floor, so the choice of fresh or zero image does not change them. The other canonical records realize the same native inferences, with major and continuation proofs serialized in the required consumption order. Every closed canonical native theorem therefore has an accepted three-field certificate.

The head test is made before allocation in these programs, while the compressed current four-field strict control can test after allocation. Accordingly, **identity of accepted raw certificate stacks is not claimed**. The direct semantic proof and canonical compilation establish equality of the public theorem languages.

### Final implementation refactors

Moving the hypothesis expression into h and then executing `k -= 1` preserves its evaluation at the old floor. The integer identity `~-k = k-1` holds at every call. The mode condition mentions only s, u and the current matrix, so evaluating it after the decrement is harmless; `bool(P)*new_k` is exactly `new_k if P else 0`. An uncaught rejection can happen on a different side of a local assignment, but acceptance and successful results are unchanged. The 313/353 profile changes only branch layout, opener binding, import spelling and reader placement relative to this protocol.

## 2. The AST profile

This profile retains the old four-field protocol and has exact accepted-certificate equivalence to its incoming strict control through the following local changes.

1. **Missing-image sentinel.** The default c is replaced by 0j. A visited function sentinel fails at multiplication; complex zero reaches an invalid ordered comparison with an integer. Neither value can be returned by a successful opening. The exact input alphabet excludes complex values elsewhere.
2. **Structural packet binding.** On integer/list input, unpacking four fields and the sequence pattern `[m,s,u,t]` succeed exactly on length-four lists. The recursive continuation remains outside the case suite. On a failed match the local fields are unbound, so the continuation necessarily rejects; it cannot silently return. Moving the neutral-resource append into the successful case does not affect success because q mutates a separate packet list and cannot observe the internal context list.
3. **Conditional major selection.** `s and [s,u] or [t]*3` equals `[s,u] if s else [t]*3` for every field: when s is true-valued the intermediate pair is nonempty, and when s is false-valued the triple is selected. No side effect or partial operation is introduced.

Rejection exception classes and the point of rejection may change. No exception is caught, so the accepted input relation is preserved.

## 3. The normalized-terminal byte profile

This program moves the final zero adjustment into the existing no-image opener: it opens the entire raw terminal computation candidate instead of manually adding `or 1` at the counter. This is the previously proved S3 terminal construction combined with the later S2 marker convention and strict arity refinement.

The exact supporting sources are Article Chapter 11, **`cert:sec:validated-terminal`**, **`cert:lem:closed-leaf`**, **`cert:lem:plus-opening`**, and **`cert:prop:validated-terminal(b),(c)`**.

For soundness, if the no-image opening of H returns, the plus-opening lemma makes H closed and preserves its reading. The closed-candidate lemma then says that this reading is an I0 or IS computation axiom. Equality with the opened goal proves that goal. Context and neutral entries retain their usual readings; every nonterminal logical step is inherited.

For completeness, use zero-as-1 canonical native certificates. Every closed term field is scanned in the candidate at a depth at least its valid root term depth, and every template/matrix at a depth at least three above its valid formula root. Thus the extra no-image opening is defined on all canonical instruction packets. Its computation leaves become the intended canonical equations. Hypotheses and neutral-major calls receive benign dummy packets. The existing branch-aware compiler can prune a branch that becomes terminal earlier, omitting its premise packets so subsequent calls read the correct record.

The two values chosen to mark case and progress are merely interchanged relative to the article's S3 implementation; the current equation-only guard remains. The proof does not use idempotence of no-image opening on arbitrary raw trees: that idempotence is false for the uniform-zero opener and the article explicitly avoids it.

This profile preserves the canonical theorem language, **not exact accepted raw certificates**. Additional terminal validation can reject unusual aliases, and normalization can permit other harmless aliases. The finite fixture results supplement the proof; they do not establish its universal claims.

## 4. Transfer to iPRA

The new files alter certificate recognition, not the native term/formula language or its ordinary realization. The required bridge is inherited from Article Chapter 1, theorem **`base:thm:bridge`**. Its Lean endpoints were inspected at `Lean/ConciseIPRA/BiInterpretation.lean` and `NativeBiInterpretation.lean`: `biInterp`, `native_iff_pra`, `pra_iff_native`, `native_roundTrip`, `pra_native_roundTrip`, and `native_inconsistent_iff`.

The ordinary realization has intuitionistic first-order logic with equality, the scalar iterator equations, numerical coverage, separation, and literal-equation induction. The repository proves the predecessor, equality reflection, quantifier-free induction, pairing, compilation of primitive recursive definitions, and the two term/formula round trips. Numerical domains are whole, equality is actual, and the numerical comparison graphs are x=y. Since each final profile recognizes exactly the same canonical native theorem language, those interpretations and round trips are unchanged. This supplies equiconsistency and bi-interpretability; it does not constitute a new independent formalization of the bridge.

## Final audit conclusion

The four profiles have the measured sizes stated above and defensible written correctness arguments of the stated kinds. The strict coordinate gains are real within the inspected comparison. The requested global mathematical breakthrough and a checker below the compact 239/256/461 envelope have **not** been established. No new end-to-end Lean verification of the Python parser, raw-tree decoder, allocation discipline or final checker programs is claimed.
