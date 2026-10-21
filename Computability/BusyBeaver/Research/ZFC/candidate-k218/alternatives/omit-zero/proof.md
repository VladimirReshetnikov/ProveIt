# Ordinary proof of the omitted-push alternative

The underlying native numerical calculus and its inherited ZFC consistency calibration are unchanged. The new obligation is to show that the changed proof enumerator remains sound and complete, then connect its own source and table to that enumerator. This is an ordinary proof; no modified Lean/Rocq theorem is asserted.

Write a command-boundary tuple as `(t,S,d,h)` and `I(A,B)=4P(A,B)`, with Cantor pairing `P`. For `B=d+x`, successful MP recognizes `h=I(t,B)`. The old command returns `(B,P(0,S),B,0)`; the new one returns `(B,S,B,0)`. Failure still returns `(0,S,B,0)`. Leaving a theorem stack unchanged preserves soundness. DROP, NIP, AX and the native axiom bundle retain their original contracts; a NIP halt still requires a theorem cache equal to falsum 1.

Completeness uses the inherited strong block contract: from arbitrary top T and stack S with d=h=0, a compiled derivation halts early or returns its conclusion X with exactly the old stack and zero d,h. Leaf and GEN blocks remain valid. Discard forces MP failure by comparing cache 0 with `I(T,1)>0`, including T=0, so it does not use the changed successful branch.

Only the successful-MP compiler tail changes. After deriving its premises and applying new MP, the retained tuple is `(B,S,B,0)`. The reset `AX(B,0,0,0)` has selector/matrix c=B, so its gate is0. Let L be its nine generated theorem entries. The cleanup is now:

```text
(B,S,B,0)
  -- AX(B,0,0,0) --> (0,L::B::S,0,0)
  -- ten NIPs    --> (0,S,0,B)
  -- DROP(0)     --> (B,0::S,0,B)
  -- one NIP(0)  --> (B,S,0,0), or halt if B=1.
```

The original tail had two final NIPs to remove two saved zeros. Omitting the dummy push requires deleting its last NIP. All earlier halts are permitted by the compiler contract. Induction on a finite native derivation therefore supplies a correct modified block without assuming that arbitrary original stack entries are theorems. Formula safety is needed separately for the soundness direction.

Finite command packing and the scheduler are unchanged. A prepended AX can reset counter/cache while a free field provides arbitrarily large codes for the fixed compiled refutation and final halt test. Positive proof lists drain, so every finite initial candidate cutoff eventually reaches a successful code if a refutation exists. The accepted startup's top/cache/stack are 0, hence theorem-safe, while its candidate and additive counters 3 are allowed.

The exact source deletes the closed 19-leaf PUSH at address 111110 and promotes its seven-leaf COPY sibling 111111 to 11111. It has 4,725 leaves and 205 distinct subtrees. The physical edit is only native 164/1, from 1R98 to 1R114. This is an intentional change to source behavior, not a claim of ordinal-trace equivalence to the baseline.

The separately preserved fresh source/relabeling checks, 6,142 arbitrary-natural primitive contracts and complete 312,909-step blank trace bind these command arguments to the exact published table. The endpoint contains all nine register words, root address, header/gap, 130 one-valued spares and the entire zero exterior. Composing those bridges with inherited native-calculus calibration gives the ordinary ZFC-formalizable blank-nonhalting/Con(ZFC) equivalence. The unchanged 218 state count and future optimizations are separate from that theorem.
