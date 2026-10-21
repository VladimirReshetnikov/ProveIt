# Share the later rho8 lemma

The dominated-rho8 derivation now uses **629 theorem nodes / 735 compact instructions**, down from 674 / 780. The exact unrestricted `rho8_all` theorem and its assumptions are unchanged. Both proof renderings passed their isolated exact-target kernel checks; downstream endpoint checks are recorded with the phase2 build.

The key reuse is original lemma 1013, `A → ((A → B) → B)`. Its proof is moved before five instances that originally appeared earlier. This is ordinary reuse of a proved schema: the selected dependency graph is acyclic, and each emitted proof refers only to an earlier theorem in the new order.

| Proof | Checked form | Actual scope |
| --- | --- | --- |
| [Lean](lean/README.md) | 629 direct proof nodes; 128,177 bytes | Exact theorem and five typed API clients; 8.281 s, no warnings, only `propext` and `Quot.sound` |
| [Rocq](rocq/README.md) | 735 instructions for the unchanged generic sound interpreter; 22,673 bytes | Exact theorem, then `ThmDom` caller; 3.122 s and 0.816 s, closed assumption reports |

After adoption, the [Rocq dependent check](rocq/result.json) rebuilt all seven affected modules, obtained four closed endpoint reports, and passed a focused recursive `coqchk` of the changed proof in 21.490 s. Its 230 reused objects remain bound to the earlier full check; this is not a new full recursive endpoint replay.

The maintained [plan and standard-library replay](../../../../../rho8plan/README.md) deterministically reproduce the same certificate from the unchanged Source149 input. Regeneration does not invoke a solver. Each generator still emits a kernel-checked derivation; the plan and discovery algorithm are untrusted.

[Search evidence](search/README.md) preserves the bounded AND/OR optimization, independent whole-rule check, baseline controls, and the first checker draft’s omitted variable-renaming convention. The candidate certificate was unchanged by that checker correction. Matching solver bounds concern only the finite offered rule family; no formal minimum-size theorem or net repository byte saving is claimed.

The source certificate and mathematical construction are Source149’s contribution. The global sharing selection, deterministic production plan, finite checker and Lean/Rocq integration are repository follow-up work. The original certificate and earlier accepted proof checkpoint remain available.
