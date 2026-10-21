# Independent review of the inherited permuted-source compiler

Reviewed input: `K216_Permuted_Commands_2026-10-21/selected/sections/source_calibration.tex`, SHA-256 `53aa8956201ed70d9aa2bb1a254b121cf742542382a1d690aea69a23c1c65669`.

This review checks the ordinary command-level argument, not the literal source implementation or a proof-assistant endpoint. The exact source CFG, numerical-calculus calibration, arithmetic macro contracts and binary runtime remain separate dependencies.

## Strong-block calculations

Write a stack as `[x;w]` for Cantor pairing, and let retained coordinates be `(top,stack,counter,cache)`. Each claimed block begins at `(t,w,0,0)` and ends at `(X,w,0,0)` or halts early.

1. Discard: MP(1) necessarily fails since I(t,1)>0, yielding `(0,w,1,0)`. AX with private label1, counter increment0, cache increment0 has A=private=1, hence top gate0. Its stack consists of eight implication-row codes, one quantifier code, saved top0, and w. None of these ten new heads is1. Ten NIPs recover `(0,w,0,0)`.
2. J(u): from top0/cache0, MP(u) fails for u>0 because I(0,u)>0. It sets counteru without stack change. The u=0 case must omit MP because I(0,0)=0 would succeed and push a zero. The stated split handles this alias correctly.
3. Axiom retrieval: after AX, the first seven stack entries are retained rows, the eighth the dominated row, the ninth a generalized incoming cache, and the tenth saved old top0. After j NIPs, DROP saves gate top, moves the selected cache to top and keeps it cached. The remaining 11-j NIPs remove the saved gate and remaining ten-j generated entries, ending with cache0 and stackw. The j=8 dominated-row formula has the correct three cleanup NIPs. A permitted bundle stays on top while ten NIPs discard the generated stack.
4. Generalization: after B_X;DROP;J(i), the tuple is `(0,[X;w],i,0)`. NIP yields cacheX and stackw. AX(i;0,0) has A=private=i, so gate0, and ninth generated entry Q_i X. Nine NIPs, DROP, and two NIPs recover `(Q_i X,w,0,0)`. This remains correct for i=0 because J(0) is empty.
5. Modus ponens: after B_X;DROP;B_I(X,Y);NIP;DROP;NIP the tuple is `(X,w,0,I(X,Y))`, unless an earlier cache test halted. MP(Y) succeeds, producing `(Y,[0;w],Y,0)`. AX(Y;0,0) gates its top to0 and saves Y as the tenth generated entry above the successful-MP zero. Ten NIPs produce cacheY, then DROP and two NIPs produce `(Y,w,0,0)`, or halt if a tested cache is1. The Y=0 alias causes no discrepancy.

These calculations establish the compiler induction assuming the stated all-natural command equations. Early halts are explicitly allowed, so none of the retrieval blocks needs an unjustified assumption that its incoming arbitrary theorem codes avoid1.

## Enumeration and cutoff

The first candidate has no outer successor; subsequent encoded commands do. The stated number `P(3,P(Y,P(1,R)))` correctly encodes AX(0;1,Y) followed by the compiled fixed suffix R under both permutations. This initial AX resets counter/cache to0 from an arbitrary retained tuple, so the following strong block applies regardless of earlier candidates. Cantor coordinate monotonicity gives this number >=Y, establishing cofinal successful candidates beyond the genuine cutoff4. After the first command, each positive proof-list cycle decrements before consuming fields, so its residual is strictly smaller. Empty/zero tails and tag-zero commands do not invalidate draining.

## Outcome and limits

No defect found in the explicit compiler, zero-alias treatment, cofinality, or cutoff argument. A new source with the same primitive/guarded ordinal CFG as this permuted source inherits these command semantics by a store-preserving bisimulation; it need not re-establish theorem decoding. A new physical table additionally needs its own whole-tape primitive simulation and a valid blank-start source frame. This review does not certify any proposed215-state table by itself.
