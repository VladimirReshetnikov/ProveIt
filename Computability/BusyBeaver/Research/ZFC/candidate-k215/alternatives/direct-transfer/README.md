# ST215: direct transfer through contextual reassociation

**A materially different 215-state candidate, with an ordinary blank-tape Con(ZFC) equivalence proof. The 214-state target remains unmet.**

The exact new machine has 215 working states, two tape symbols, one bi-infinite tape, and a separate halting label. It starts in state 0 on an entirely zero tape. Building on the repository's established native-calculus and arithmetic-macro calibration, the report proves

    ZFC ⊢ (ST215 does not halt on blank tape ↔ Con(ZFC)).

This packet does not contain a new compiled Lean/Rocq endpoint. Its executable universal runtime proof is an ordinary mathematical checker using literal steps, induction on unary lengths, and induction on finite block lists.

## What changed

The earlier three-command transfer parent implemented S by the 78-leaf composition DROP;NIP;NIP, with guards on both incoming cache and top. ST215 realizes the direct 35-leaf command:

    S(t,w,d,h) = HALT,                         if h=1;
    S(t,w,d,h) = (h, tail(w), d, head(w)),      otherwise.

Its inherited strong compiler already applies to this exact single-guard contract. There is no new decoding test for formula codes.

The physical breakthrough is the source reassociation

    (A, ((B,C),D))  →  (((A,B),C),D).

It preserves the entire ordinal control-flow graph, while moving CC3 to address 00111 and CD1 to 010. Those two contexts satisfy the existing compressed physical implementations. The source has 201 distinct subtrees and 4,732 primitive occurrences; source nodes are not physical states.

The final table is distinct, under rooted state renaming and global tape reflection, from all 78 unique 215-state byte files under 332 original names in the comparison corpus. That corpus includes the pinned K215 directory and twelve incoming archives. Restoring just the append-one refill bit still leaves no matches, so novelty is not only that bit.

## Verification obtained

| Obligation | Result |
|---|---:|
| Working states / transition rows | 215 / 430 |
| Universal guarded primitive cases | 6,151 of 6,151 |
| Symbolic inference steps | 1,617,630 |
| Literal rows covered | 430 of 430 |
| Minimum positive duration constant | 5 |
| Complete blank prefix | 70,506 transitions |
| Exact synthetic AX-prefix match | 177 source transitions |
| Safe initial heads / required conservative credit | 10 / 2 |
| New exact-table proof-assistant endpoint | Not claimed |

The blank run reaches native dispatcher 84, head −2, header 62, gap zero, ordinal 58, PC 00110010010110010, and logical registers (N,T,W,A,D,H,X,Y,L)=(1,0,0,0,0,0,0,18,0). The entire tape has exactly 100 one-cells and 63 zero spare blocks.

That frame matches AX(0;0,0) from synthetic stack tail 2. AX completion supplies ten theorem heads above the opaque tail. The ordinary scheduler from candidate 1 has exact conservative debt 2, leaving a permanent margin of eight. Tail 2 contains buried falsity, so this protected-tail proof is substantive.

The standalone replay freshly rederived all 6,151 symbolic cases and compared every result with the frozen receipts. Its preparation receipt is evidence/portable_full_replay.json.

## Offline reproduction

Python 3 standard library only; assertions must be enabled. No repository checkout or network is required.

    python3 -I verify.py --work /tmp/st215-finite
    python3 -I verify.py --runtime --work /tmp/st215-full

Use a fresh output directory. The first command performs finite reconstruction, two complete CFG resolutions, source comparisons, exact native and dense startup replay, all 177 source-prefix transitions, the 3,728-node logical recovery certificate, runtime metadata audit, and the independent graph comparison. It writes FINITE_REPLAY_PASS.

The second additionally rederives the complete universal primitive simulation and writes FULL_REPLAY_PASS. It took about four minutes for the full portable replay on the preparation machine; this is not a performance guarantee.

Default verification audits a hash manifest. SHA256SUMS includes MANIFEST.json; MANIFEST.json excludes itself and SHA256SUMS.

## Principal files

- [report.pdf](report.pdf) and [report.tex](report.tex): the mathematical report, complete transition appendix, independent review, and additional results.
- [machine/st215.native.tm](machine/st215.native.tm): native table, start 0, dispatcher 84, halt 254.
- [machine/st215.tm](machine/st215.tm): dense table, states 0–214, start 0, dispatcher 81, halt 215.
- machine/canonicalization.json: complete bijection between presentations.
- source/st215.sites.json: exact 4,732-row primitive occurrence list.
- evidence/blank-delta.jsonl.gz: every binary startup transition.
- evidence/AX-prefix.json: every source transition in the matched AX prefix.
- evidence/runtime.json and runtime_cases.json.gz: full universal-case inventory and exact input pins.
- proofs/: inherited complete single-guard compiler and credit proof, plus independent candidate-specific review.
- research/comparison/: inert comparison tables, exact original names, provenance, scripts, and results.
- research/physical/: bounded failed 214-state search specifications, scripts, inputs, and limits.
- research/: independently runnable checks for the additional formalism results.
- reference/transfer-parent/: unchanged inherited research packet, preserved for context and dependency review.

The mathematical theorem still uses the inherited native-calculus-to-ZFC comparison and arithmetic macro contracts. The complete proof chain and this boundary are stated in the report. A finite propositional certificate or a primitive-runtime checker alone does not prove that entire chain.

## Additional results

1. **Rotating-pop obstruction.** The literal AX order preserves a blocked-adjacency invariant. The proposed language cannot compile even the fixed theorem 20=I(0,2) under the strong compiler contract, and cannot halt from an all-zero store. This is an all-natural command-level obstruction, not a bounded experiment.
2. **Scratch-biased control correction.** The archived CC3 returns to selector 23, not scheduler 0. Its initial AX is followed by a 15-source-transition halting suffix. A valid primitive-runtime certificate does not repair this source-level error.
3. **Abstract consecutive-candidate synchronization.** An intended biased parser can have cofinally many pairs of consecutive successful candidates. Any increasing schedule with gaps at most two meets them. A separate all-natural credit proof protects the stack. This is a possible future encoding; the rejected archived table does not implement it, and ST215 does not depend on it.

The bounded physical searches found no 214-state solution. Their short-layout seed is the append-one precursor, not the final append-zero machine. The limits do not imply minimality.

## Exact identities and provenance

Native table SHA-256:

    d5237504325eee96b0040d4d9574731a1caf4bcda3d6a49e94827d9532a664e1

Dense table SHA-256:

    ead0ec3aa1c3502015faa8a077ded98be7522fa907a9df43a8052de555398375

Source SHA-256:

    212cf0ffde43c1cc22c183dd8bf0b3a699396f96c9942ee92a7cc372cd273ca9

Repository snapshot:

    75716498437bfc7291d5900cab2983a11fd54bac

See NOTICE.md, provenance/UPSTREAM.json, and licenses/ for inherited authorship, paths, hashes, and licenses. No global priority claim is made beyond the explicitly inspected corpus.

## Rebuild the PDF

With a normal TeX Live installation:

    python3 -I checks/make_transition_tex.py
    pdflatex -halt-on-error report.tex
    pdflatex -halt-on-error report.tex

The generated transition appendix is derived directly from the dense table. Typesetting is separate from mathematical verification.
