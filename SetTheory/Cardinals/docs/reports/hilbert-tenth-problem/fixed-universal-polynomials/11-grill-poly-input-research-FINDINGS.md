# Grill universal-input research: bounded outcome

Date: 2026-10-03. Read-only source research; no repository edits, author-code execution, numerical universal table emission, or new operation bound.

**Update:** `SEMANTIC_CONTRACT.md` supersedes the initially open accepting-head discussion below. It gives an explicit corrected right macro, an explicit left macro and rotation, the no-short-queue and unique-head proofs, exact U15/ordinary-input conventions, and the fully bounded exponent extraction. An independent mathematical check and 3,600 additional macro tests agreed. The existing arithmetic/history circuit is still not emitted or counted for this new source.

## Result

No existing numerical Genera recognizer with the current bare canonical-binary input contract was found. A concrete alternative is worth a bounded semantic construction: specialize the Cocke–Minsky 2-tag compiler to the already audited fixed U15,2 machine, adapt its unique accepting head, normalize to exactly-two-output Genera, and pay its finite unary tape encoding using the existing recoder's duration-extraction identity. This is a proposed route, not a universal Grill theorem already proved.

The important new observation is that unary input need not remain an arbitrary external computable reduction. The paid recoder can be specialized to input 1 and extended with two arithmetic comparisons to force its actual exponent to a supplied tape integer. That gives a finite positive existential power graph suitable for the exact unary blocks.

## Exact current contract

Pinned sources:

- [Reviewed exact-width loader](https://github.com/VladimirReshetnikov/ProveIt/blob/1dd95f92840097f0f7da8e7c30ad0a99eec03526/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_grill_tag_exact_width_loader.md)
- [Two-cone successor commit](https://github.com/VladimirReshetnikov/ProveIt/commit/2d887f0fa768fd67f3e545d83f8998b5780e530d)
- [Corrected halt bridge](https://github.com/VladimirReshetnikov/ProveIt/blob/2d887f0fa768fd67f3e545d83f8998b5780e530d/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/grill_tag_halt_bridge.md)

Source alphabet: fixed finite size N, a distinct halt H, nonhalt symbols y with width w_y in {0,1}. At persistent phase p modulo 2, reading y appends exactly two ordered symbols F_y(p), then advances phase by w_y. Initial phase is 0. The initial nonempty word contains no H. A valid source halt produces exactly one H, with the additional published hypothetical-prefix condition. Multiple-H behavior is outside the theorem.

The existing loaded source word is exactly LSB-first binary(x+1), x>0, using labels 0 and 1 of width one. It is not an arbitrary source word, a free word witness, a framed program/data string, or binary(x). The exact E width and canonical source-bit length are both paid. The measured 1,568-phase table rejects every input. There are two distinct arithmetic packets: the unchanged `grill_tag_exact_width_loader.md` and its review report **16,291** operations; the [factored recoder successor](https://github.com/VladimirReshetnikov/ProveIt/blob/2d887f0fa768fd67f3e545d83f8998b5780e530d/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_binary_recoder_factored128.md) and its [independent review](https://github.com/VladimirReshetnikov/ProveIt/blob/2d887f0fa768fd67f3e545d83f8998b5780e530d/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_native_binary_recoder_factored128.md) report **16,289** for the `exact_width_grill` variant, saving two multiplications. Both have 3,217 positive witnesses, 48 comparisons and degree at most 283247, and both remain this fixed nonuniversal example. Reading only the unchanged parent proof at the newer commit still correctly yields 16,291.

The corrected E compiler uses a=28(N+1), b=7a. Nonhalt E_y has length b(2-w_y), value A*2^(14y), and long terminal zero runs. All valid nonempty E concatenations satisfy the strong initial cone. The established first-empty-time and phase-alignment proofs are retained, not replaced by eventual-erasure intuition.

## Candidate: explicit finite 2-tag simulation

[Cocke–Minsky 1964, pp.17–19](https://cs.famaf.unc.edu.ar/~hoffmann/cc18/p15-cocke.pdf) gives a finite construction from a binary Turing machine, using a write/move/read control convention, to deletion-2 tag rules of maximum output length four. It encodes a configuration by

    A_i xi_i (a_i xi_i)^M B_i xi_i (b_i xi_i)^N.

M and N are the finite binary tape integers to the left and right of the scanned square, with the nearest square as the low bit. The control state already remembers the scanned symbol. An ordinary read/write/move machine is converted by a finite state refinement. No infinite nonblank background is used.

Use the repository's [explicit U15,2 ordinary-input theorem](https://github.com/VladimirReshetnikov/ProveIt/blob/2d887f0fa768fd67f3e545d83f8998b5780e530d/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/neary_woods_explicit_universal_tm.md). Its fixed 29-instruction table is an ordinary binary machine with finite tape initialization. For each c.e. set S, its finite program is fixed while its varying input is a fixed frame around equal-length bit blocks. For this route, choose the represented semidecider to read LSB-first binary(x+1), decode it, subtract one, and recognize S. This bit-order/input-shift wrapper is a finite change to the represented program, not an external per-input algorithm.

At the U15 initial head, M is a per-program constant, and the right tape integer N is the numeral of fixed-prefix + equal-length bit blocks + fixed-suffix. The fixed U15 start/read state is known. Therefore all varying initialization is described by regular block arithmetic plus a single exponent graph. A full construction must pin the write/move/read refinement, exact left/right orientation, fixed frame constants, and halt convention. The present pass did not transcribe or verify the entire Cocke–Minsky table.

### Required accepting-head lemma

For the concrete refined U15 table and every valid program slice, prove:

1. Every tag step before the intended accepting event has at least two symbols, and the published simulation maintains the exact tape integers and control state.
2. A fixed designated head event is read exactly once when U15 accepts, and never otherwise.
3. Replacing only that event's production by one fresh H creates exactly one H during its enclosing Genera generation. No other pending head event can create another H before that boundary.

The likely event is the control symbol A_h for the accepting state. The published right-move construction has a separate uppercase head lineage A -> C -> (D_1,D_0) -> A_next, with one member of the D pair deleted, while lowercase tape-counter productions cannot create an uppercase head. The left-move transcription and all phase cuts must still be checked. This is the bounded semantic gate to do first. A finite simulation census would support its implementation but would not replace the invariant proof.

## A proved normalization schema, conditional on the head lemma

First encode a deletion-2 tag rule P_y as an unnormalized Genera rule: original symbol y has width one, F_y(0)=P_y, F_y(1)=empty. Two FIFO symbol steps reproduce one tag step while the tag queue has at least two symbols. Persistent phase is essential when a generation boundary falls between the two deletions.

This does not preserve ordinary short-word halting. For example, starting aa with a->b and b->bb, the tag system halts at b; the unnormalized Genera system continues. Thus source universality alone is insufficient; the accepting-head lemma above replaces this unsupported halt transfer.

To normalize all productions of length at most four, introduce a width-zero dummy d, with d->dd in both phases. Pad every F_y(p) on the right by d to length four. Replace that length-four production s0 s1 s2 s3 by the two fresh pair symbols [s0,s1] [s2,s3]. Every pair symbol has width zero and has the phase-independent two-symbol production u v. Original widths stay one. H is never an input symbol; it occurs only as a component of a pair that will expand.

After two normalized generations, erase all d symbols. The resulting word and persistent phase equal one unnormalized generation. The first generation advances phase exactly according to the original symbols; the width-zero expansion generation cannot change it. Dummies are phase-neutral in every layer. All normalized productions have exactly two outputs.

If the unnormalized generation emits one H, it first appears in the expansion generation. At that point every symbol preceding H is original or d. Their next productions contain only pair symbols or d, never H. Hence the published hypothetical-prefix condition holds automatically. Uniqueness of H still depends on the accepting-head lemma; normalization cannot repair several H emissions.

## Paid exponent extraction: no computability oracle

The repository's [dyadic-duration recoder proof, Sections 2–3](https://github.com/VladimirReshetnikov/ProveIt/blob/2d887f0fa768fd67f3e545d83f8998b5780e530d/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_binary_dyadic_duration_recoder.md) separates exact exponent extraction from its later dyadic test. The extraction itself works on the old, nondyadic complete recoder.

Specialize a complete generic-width recoder, k>=4, to positive input 1 and spread output 1. Its established theorem supplies

    n>=2, q=2^n, B=2^(k-1) q^k,
    P=B^n, J=1+B+...+B^(n-1),

with a full positive extension for every n>=2. Add positive ell,v,g and the comparisons

    (B-1)v + ell = J,
    ell + g = B-1.

Because J=n modulo B-1, 2<=n<B-1, and 1<=ell<=B-2, these force ell=n. Conversely v=(J-n)/(B-1)>0 and g=B-1-n>0. No modification of the AND to impose ell AND (ell-1)=0 is made; imposing that would wrongly restrict the tape integer to a dyadic duration.

For N>=1 bind ell=N+1, obtaining q=2^(N+1). To include N=0 uniformly, use ell=N+2. This is a finite fixed-arity polynomial extension of an existing complete certificate. Its arithmetic, new comparisons, variable namespaces, positivity, and full finalization must be literally emitted and counted before a cost claim. No exponentiation gate or uncharged external computation is introduced.

### Exact unary E word from that power

Let the normalized source's original repeated pair U=(b_i,xi_i) have corrected E length k=2b and E numeral V. Put K=2^k. With n=N+1 above, the already computed Q=q^k is K^(N+1). Introduce positive T and bind K*T=Q, forcing T=K^N.

Let F_e=A_i xi_i (a_i xi_i)^M_e B_i xi_i, the fixed source prefix for represented program e, and put L_e=2^|E(F_e)| and C_e=val(E(F_e)). The entire source word is F_e U^N. Its exact queue input is specified by

    (K-1) X = (K-1) C_e + L_e V (T-1),
    P0 = L_e T.

These are denominator-cleared polynomial equations. T is a scale, not a hidden word witness. Program-dependent L_e,C_e are finite fixed coefficients for each S, or explicit program parameters of a universal polynomial restricted to valid slices. The source table itself remains the single fixed compiled U15 table. The right tape integer N is separately bound to the paid regular recoding of the external input. The strong cone follows from the literal E word, and the retained positive native width slack is bound to precisely P0.

## A simpler framed-block extension also exists

For any fixed E-prefix P and suffix S and two source bit blocks whose E images have equal length d, set K=2^d, M=K-1, c_i=val(E(DATA_i)), p=2^|E(P)|, Pnum=val(E(P)), Snum=val(E(S)), s=2^|E(S)|. The current canonical recoder at width d supplies Q=K^n and R=sum bit_i(x+1)K^i. Exact concatenation P DATA_bits S is forced by

    M X = p(c0+M*Snum) Q + p*M*(c1-c0) R + (M*Pnum-p*c0),
    P0 = p*s*Q.

For fixed coefficients the displayed value/width computation needs four fixed-coefficient multiplications and two additions/subtractions before residual finalization. This is only an interface delta, not a complete emitted source ledger. Signed fixed offsets are harmless because X and the native width slack remain positive supplied witnesses, and the full unit finalizer retains every equation. Parameterized frames require their own literal gate count.

This shows that fixed markers and equal blocks are not a fundamental input obstruction. It does not supply an arbitrary finite-state decoder, variable-length block map, or length-dependent counter automatically.

## Other sources checked, and why they are not plug-compatible

- [Woods–Neary 2006, Definition 4](https://arxiv.org/pdf/cs/0612089): decorated bit pairs plus a next-power-of-two length counter. The existing binary(x+1) loader does not build that counter. Its definition also treats repeating configurations as computational completion, so a finite accepting event must be identified separately.
- [Neary STACS 2015](https://d-nb.info/1365606880/34): uniform finite bit blocks, but deletion number depends on the cyclic program, rather than 2. Modulus reduction is a separate compiler obligation. The repository's later fixed binary-tag route is useful prior art, not directly a modulus-2 source.
- [Shepherdson–Sturgis 1963, Section 8.1 and Appendix C](https://www.cs.cmu.edu/~cdm/projects/ShepherdsonSturgis1963.pdf): ordinary-word FIFO computation is an excellent raw-input foundation, but does not furnish the required Genera compiler.
- [Wang 1963, Section 3](https://gwern.net/doc/cs/computable/1963-wang.pdf): finite sentinels and short lag productions give another clean source boundary; lag lookahead is not the current Genera operation and needs a compiler.
- [Cook 2009](https://arxiv.org/pdf/0906.3248): finite tag stages are potentially useful, but the surrounding Rule 110 infinite-background construction is not a finite-empty-queue theorem. It must not be imported wholesale.

## Recommended stopping condition / next scope

Authorize a semantic-only Cocke–Minsky/U15 packet first: complete literal fixed table recipe; left/right tape orientation; every nonhalting phase invariant; unique accepting-head event; the two-level normalization; exact ordinary-input word family. Stop on a failed head/input invariant. Only after that succeeds should a worker compose the regular tape-value recoder, exact-exponent extension, unary E loader, and actual Grill history, then derive a new ledger. Do not reuse the 16,289 example's ledger or the unrelated 205-operation three-phase result.
