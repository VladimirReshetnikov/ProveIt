# Independent review of the public K216 permuted-command source calibration

## Conclusion

**No mathematical blocker was found in the stated all-natural source-calibration theorem.** The command-level proof covers raw numerical payloads, the zero alias, the actual clean source seed with next candidate 4, and the fairness requirement needed to search beyond that cutoff. This is an ordinary mathematical review of the source theorem, accompanied by fresh finite source-identity replays. It does not supply a new proof-assistant endpoint or independently claim a binary runtime or blank-initialization theorem.

Reviewed manuscript:

`upstream-late/extracted/K216_Permuted_Commands_2026-10-21/sections/source_calibration.tex`

The fresh finite audit receipts are:

- `k216-source-permutation-210-review.json`
- `k216-source-permutation-120-review.json`

Both are produced by the archive's supplied `code/audit_command_permutation.py`, run afresh against its pinned baseline, frozen reference, and each candidate source. Replaying supplied code is distinguished here from a separately implemented checker. The mathematical review below was performed independently of the manuscript's saved reviews.

## Source identity and closure

Both fresh executions report `PASS_EXACT_SOURCE_COMMAND_PERMUTATION`. For each permutation, 6,176 guarded primitive cases agree between the structured ancestor-stack resolver and binary-address resolver. The source has 202 distinct subtrees and 4,751 primitive occurrences. The 4,593 occurrences outside the three permuted command bodies are literal, including the complete AX subtree. Every moved body has zero escaping break/continuation demand, and the ordinary continuations return to source ordinal zero without running another command body. The single halting primitive stays inside NIP.

The crucial distinction is between moving a complete closed command body and merely changing a numerical opcode table. The source checker verifies the former, including selector partitions and return wrappers, so the argument applies to all natural selectors, not only hand-encoded valid command lists. Three positive selector decrements produce the symbolic family `selector >= 3` with residual `selector - 3`.

## Independent command-proof checks

The following obligations were checked directly from the displayed command equations.

1. **DISCARD is exact.** Its `MP(1)` starts with parameter/cache zero; `I(t,1)>0` forces failure even if `t=0`. AX then has `U=A=C=1`, so the gate is zero. Nine freshly generated entries differ from falsity 1, and the saved old top is zero. Ten NIPs therefore restore the old stack with current/parameter/cache all zero.

2. **The `J(0)` exception is necessary and correctly handled.** A literal `MP(0)` at zero current/cache would succeed through `I(0,0)=0` and push an extra zero. Using the empty sequence for `J(0)` avoids that extra stack entry. For positive `u`, `I(0,u)>0` makes `MP(u)` fail and set only the parameter to `u`.

3. **All axiom selectors have the correct offsets.** A row at stack position `j` is loaded by `NIP^j`; DROP makes it current while pushing the former gate; `NIP^(11-j)` removes that pushed gate, the later generated rows, and the saved zero top. The dominated eighth row uses 8 and 3 pops, respectively. No selected logical row or quantification code is 1.

4. **Generalization uses the old cache and old parameter correctly.** After the premise block and DROP, top/cache are zero and the theorem is on the stack. `J(i)` sets the label without altering that stack. NIP then loads the theorem into the cache. AX has `U=A=C=i` and emits exactly `Q_i(X)` at position 9, before the cache increment. The final 9/2 selection restores the stack and zero parameter/cache.

5. **Modus ponens and its cleanup are correct.** The two premise blocks preserve the underlying stack. NIP/DROP/NIP put `X` current and `I(X,Y)` cached; an intervening cache equal to 1 legitimately gives earlier halting. `MP(Y)` succeeds from parameter zero and pushes the success zero. The subsequent AX has `U=A=C=Y` and a zero gate. Ten NIPs load the old result `Y`; DROP and two NIPs remove the gate zero and the MP success zero. This returns `Y` with parameter/cache zero or halts if a tested premise/result is already falsity.

6. **The soundness invariant has the right scope.** It requires theoremhood only of current code, cached code, and every stack head; the additive parameter is unrestricted. Every raw command preserves this invariant, and only NIP's cache test halts. The actual seed `(4,0,0,0,0,0,0,0,0)` is safe. The proof does not incorrectly assert soundness for an arbitrary initial cache containing 1.

## Enumeration and cutoff

The encoding correctly distinguishes the positive list cursor `enc(k::L)=1+pack(k,enc(L))` from the first candidate number `pack(k,enc(L))`. This matters particularly when NIP has selector zero and the packed payload can be zero. No empty-list ambiguity is used in the proof.

For a positive cursor, fetch first decrements it, and every later Cantor tail is no larger than its input. Thus each nonhalting command strictly decreases that cursor. The inherited arithmetic contracts terminate and preserve the next-candidate register outside fetch, so finite draining really does establish eventual enumeration of every later candidate.

The proposed prefix `Start_Y=AX(0;1,Y)` resets parameter/cache to zero from every incoming retained tuple. It need not erase the old stack: the strong proof block works over every protected old stack. Its packed candidate number is exactly

`N_Y = P(3, P(Y, P(1,R))) >= Y`.

Taking `Y >= 4` supplies a universally halting candidate beyond the actual initial cutoff. Consequently skipping the first four candidates and retaining earlier work-state data do not create a completeness gap.

## Dependency boundary

The theorem relies on the inherited all-natural arithmetic macro contracts, the exact dominated-row recovery certificate, and the prior numerical-calculus/ZFC calibration. The finite source audit proves the changed control and source identity; it does not replace those mathematical dependencies. To conclude the blank binary-machine theorem one additionally needs the exact candidate's universal runtime simulation and its blank trace to the represented source root. Those are separate checks being handled in the parent investigation.

## Relation to this investigation's residual compiler

Upstream `intake-193.md`, Source153, already credits and reviews a residual-counter calibration: its repaired reader transfers scratch residue into the unconstrained parameter before decoding, AX leaves `max(C-A-1,0)`, and MP retains an explicit input and can leave an additional failed-comparison residue. This investigation should not claim residual freedom itself as new.

The separate theorem in `residual_parameter_compiler.tex` removes MP's input entirely. Its AX setter preserves the current implication and protects the other premise on the stack while setting an arbitrary desired consequent. It has an absolute AX first argument and a weaker compiler exit contract allowing an arbitrary numeric parameter. These distinguish it from Source153's reported interface. Neither residual construction, as presently measured, improves the public 216-state permuted-command table.
