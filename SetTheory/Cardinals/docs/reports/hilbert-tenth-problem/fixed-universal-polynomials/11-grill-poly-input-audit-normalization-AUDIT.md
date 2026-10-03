# Section 5 independent normalization audit

**Verdict: PASS within the stated compiler contract.** No counterexample to persistent-phase two-generation normalization, unique-H preservation, or the published hypothetical-prefix halt condition was found. The halt conclusion uses Section 4's unique accepting-head invariant; this audit does not establish the full U15 universality premise or arithmetic composition.

## Sources actually inspected

- The local `SEMANTIC_CONTRACT.md`, Sections 4–5, read 2026-10-03.
- The [pinned bridge](https://github.com/VladimirReshetnikov/ProveIt/blob/2d887f0fa768fd67f3e545d83f8998b5780e530d/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/grill_tag_halt_bridge.md), fetched read-only through the GitHub connector. Returned blob SHA: `e42c78fabf5c0b0523563e200b52fc1f4b705c53`. In particular its Sections 3–4 distinguish a one-H cleanup proof from its valid-Genera source theorem.
- The [creator's Genera Tag semantics](https://esolangs.org/wiki/Genera_Tag), reopened 2026-10-03. Its footer identifies revision 182460, the same revision named by the bridge. The direct oldid URL initially failed in the web tool, but the current page succeeded and explicitly exposed that oldid. This confirms the phase is persistent, the halt symbol is checked in the completed generated word, more than one H is undefined, and a hypothetical next generation from the prefix before H must not itself contain H.

No upstream repository code was executed, edited, or published. The earlier local macro checker was read for context, but neither imported nor run; all numerical evidence below comes from a newly written, standalone test.

## Algebraic proof of the two-generation claim

Let O be the original nonhalt alphabet and let d be a fresh dummy. For every s in O, let P(s,p) be its unnormalized production at phase p. Here P(s,1) is empty and the length of P(s,0) is at most four. The possible output alphabet includes H.

Pad P(s,p) on the right with d to length four, obtaining t0 t1 t2 t3. Its normalized production is the pair of fresh symbols [t0,t1], [t2,t3]. Each pair symbol produces its two components at both phases and has width zero. The dummy's production is dd at both phases and its width is zero. Each original nonhalt symbol has width one. Every nonhalt production has exactly two outputs; H requires no production.

For a word W over O plus d, erase d to obtain rho(W). Start both versions at the same p. In the first normalized generation, the phase used for each original occurrence is p plus the number of preceding original occurrences, modulo two. Dummy occurrences do not alter this. This is exactly the phase used for that occurrence when processing rho(W). The output contains only pair symbols and d.

Every symbol of this intermediate output has width zero. The second normalized generation therefore leaves the phase unchanged. Each pair expands to its two components, and existing d symbols merely double. Erasing d from the result gives exactly the unnormalized generation of rho(W). Both versions end at

    p' = p + length(rho(W)) mod 2.

This proves the statement by induction across arbitrarily many nonhalting generations, including every odd original generation. It also explains why doubling the physical length does not reset the logical phase: pair symbols and dummy symbols contribute no width.

An incoming dummy produces four d symbols across the two passes. This is harmless for erasure and phase; it is not claimed to be negligible for resource counts. In fact every normalized generation doubles the physical word length. The contract correctly leaves actual table and arithmetic cost accounting unfinished.

## Odd-generation and tag-boundary issues

Two width-one FIFO reads implement a deletion-2 tag step whenever the tag queue has at least two symbols: the first emits the tag production, while the second discards the original second symbol. If a generation boundary lies between these reads, persistent phase one correctly skips the first symbol in the next generation. Resetting would instead perform another head event.

A small boundary witness illustrates the necessity of the carry. With A -> A and B -> BB at phase zero, both empty at phase one, the word ABB at phase zero produces ABB and leaves phase one. The next correct generation produces BB and leaves phase zero. Incorrectly resetting would produce ABB again and leave phase one. Section 5 uses the correct carry.

This embedding must remain restricted to the no-short-queue valid slice. A one-symbol phase-zero queue would permit an append-before-second-read interpretation that is not a legal deletion-2 step. The contract expressly relies on its no-short-queue lemma, rather than claiming unrestricted equivalence.

## Unique H and the prefix condition

Before the first H, the normalized generations alternate between an original/dummy layer and a pair/dummy layer. Literal H cannot occur in the latter. Expanding the pair/dummy layer preserves the number and order of all nondummy outputs, including H. Hence the first H generation has exactly as many H symbols as the corresponding unnormalized generation.

Section 4 supplies the needed count of one: the first active A_h is read at a canonical boundary; everything else then in the queue is canonical h-state filler. The remaining suffix of that unnormalized generation is a prefix of that filler suffix. Its active productions cannot emit another H. Previously appended output cannot contain an earlier H, by definition of this first event. An A_h in a discarded phase-one position would not be an accepting event.

The first normalized word containing H consists solely of original symbols, H, and d. Its prefix before H therefore contains only original nonhalt symbols and d. A hypothetical next normalized generation from that prefix can output only fresh pair symbols and d. It cannot output a literal H, at either starting phase. A pair named [H,d] is a distinct nonhalt symbol; it is not H. The published restriction is thus satisfied exactly, without relying on the stronger Grill cleanup theorem outside its declared source domain.

The prefix argument is actually stronger than needed: it can remove an original program's immediate-prefix hazard by delaying H for one pass. The contract still separately needs unique H, since two H symbols remain two H symbols after pair expansion.

## Applicability of the pinned bridge

The normalized initial word is the nonempty canonical configuration and contains no H. The alphabet is finite; widths are zero or one; every nonhalt production has exactly two outputs; and the first halting generation satisfies both unique-H and hypothetical-prefix conditions. These are precisely the bridge's stated source hypotheses. Nonhalting words cannot become physically empty because their length doubles each generation.

Accordingly the bridge applies at the exact corrected E word, with the normalized alphabet's N. Its symbolic cleanup formulas remain applicable. This is not a claim that a previous fixture's numerical lengths or operation counts can be reused.

## Independent tests and reproduction

Run:

    python check_normalization.py

The saved receipt `check_normalization.json` records:

- 819,907 two-generation comparisons, checking both erased output and final phase
- 585,642 inputs with odd erased length
- 409,952 phase-one starts
- 237,750 unique-H outputs whose hypothetical prefixes were checked at both phases
- Repeated expansion through eight original generations, including accumulated dummy words up to 131,072 physical symbols after the final check
- A designated accepting symbol in the phase-one discarded position, and the corresponding active phase-zero case
- An intentionally prefix-invalid original source, confirming that delayed pair expansion itself enforces the normalized prefix condition

The main exhaustive family uses every length-0-through-4 production over A, B, H for each of A and B, every nonempty input over A/B of length at most three, both initial phases, and both bare and interspersed-dummy layouts. Multiple-H outputs are tested only for algebraic identity, never certified as valid halts.

Checker SHA-256: `a4acdabd75f39d2c5e8c0f9f0ebfab1e886f21cc7f3ce0aa91edd04e7c7b9280`.

## Wording clarifications, not mathematical corrections

For an eventual literal table, specify d -> dd **at both phases**, give every nonhalt pair symbol width zero and the same expansion at both phases, and say “every nonhalt production has two outputs.” The present prose already implies these choices; H's rule and width remain irrelevant. No substantive change to Section 5 is needed.
