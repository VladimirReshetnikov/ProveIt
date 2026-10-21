# Forced transfer at each refill: a distinct 215-state scheduler candidate

This candidate is NOT the published ZC215 scheduler, and it does not have a zero-debt proof. It retains the ST215 three-command language (short S, MP, AX). Its only source edit inserts CB1 after the refill scratch-restoration loop. In the ST source's enclosing association this CB1 goes to selector ordinal24, not root0. This difference is intentional in the interpretation below, not hidden by a claim of source equivalence to ZC215.

## Exact source binding

The old source SHA256 is 212cf0ffde43c1cc22c183dd8bf0b3a699396f96c9942ee92a7cc372cd273ca9. The new SHA256 is b64d9fa23d97e7c81154468e9a62a5d8e12b39709d2a4d45c5ca9a4e40ca51ce.
At path0000111 the old H0 loop is replaced by (H0,CB1). The audit checks literal equality elsewhere, and every old ordinal CFG edge under j(i)=i for i<9 and j(i)=i+1 otherwise. The only changed old edge is the zero case at ordinal7; it enters the inserted CB1 at9 instead of the reader. That CB1 enters selector24. There is no altered AX or MP formula, no removed freshness condition, and no changed short-transfer guard.

At every completed command, selector register A=R3 and scratch X=R6,Y=R7 are zero. The first selector decrement makes A zero for S and MP; AX clears its remaining binder parameter. These are inherited exact ST command contracts.

## Refill and actual sequence

At a root boundary with residual L=R8 zero and counter N=R0 equal to n>0, refill copies n into L, raises N to n+1, and clears X. The new CB1 skips the reader and enters selector with A=0. Thus it executes one S. The literal S subtree accesses only registers1,2,5,6,7; it cannot change N,A,L. Returning to root then decrements positive L and reads raw candidate n-1. Normal positive residuals inside a candidate are still decremented in exactly the old manner.

Consequently, starting at N=1,L=0,A=X=Y=0, the command sequence is

    S;W(0);S;W(1);S;W(2);...

until a halt, where W is the ordinary three-command predecessor-cursor parser. The exceptional n=0 refill would execute an extra S and refill again, but the actual startup counter is1 and remains positive.

## Completeness

The source command semantics and every inherited ST strong compiler block are unchanged. The compiler's contract is from arbitrary numerical top and stack with D=H=0. Any incoming tuple is reset to that interface by a leading AX command; its chosen formulas and saved heads need not have any particular values for this completeness argument.

Encode the finite word consisting of that resetting AX followed by a compiled native refutation. The ordinary exact parser/encoder inverse supplies a natural raw code for this word, including zero-valued fields and predecessor continuations. Every raw code is visited by the new scheduler. The additional S immediately before this candidate either already halts or changes only the arbitrary incoming tuple, which the leading AX handles. Hence a native refutation still implies a halt. No theorem equality stronger than the inherited numerical calibration is needed.

## Soundness and startup obligations

Soundness needs a protected reserve because forced S consumes one head per candidate. It does NOT follow from ZC's DROP-to-NIP injection: this language has no separate DROP command. The exact grammar's initial three candidate words S,MP,S;S give a conservative deficit of six after including their three forced S commands. The forced S before the first AX candidate then takes the deficit to seven. The independent credit reviewer reports an all-natural debt-seven proof; its separate receipt must be included in the completed calibration.

Fresh binary startup checking reports blank state0 reaches the same ST AX bridge, with ordinal shifted by1: after70,506 physical steps, dispatcher84, head-2, ordinal59, registers[1,0,0,0,0,0,0,18,0], gap0. The independent177-source-step AX bridge begins at ordinal26 with [1,0,2,0,0,0,0,0,0]. It supplies the inherited ten protected theorem heads above its old numerical tail. This paragraph records the separate runtime worker's receipt; it is not recomputed by the source audit. Start74 is not a valid replacement startup.

Raw allocation uses215 states and changes only native8/read1 from1R13 to1R103. Full arbitrary-value primitive runtime and all-natural protected-credit checks are separate required evidence layers. Their completed results are recorded below; the raw count or finite grammar experiment alone would not establish calibration.

## Completed calibration theorem

The separate universal primitive-runtime replay has now passed all6,152 guarded cases for the exact table SHA256 2bfeff91aadd2da3d942a5e7d03b280354a841c0961eace5b43b73da764cecac, with zero spare append. The exact startup receipt is research215_round7_boundary/ZERO_ST_STARTUP.json. The all-natural bound and checked finite base are research215_round6_credit/FORCED_TRANSFER_CREDIT_THEOREM.md and FORCED_TRANSFER_CREDIT_BASE.json. These are distinct evidence layers, not deductions from the source-node count.

Complete the synthetic AX command whose177-instruction prefix is the established blank bridge. Its input is N=1,T=0,W=2,A=D=H=X=Y=L=0. The inherited all-natural AX contract gives at its root return N=1,L=0,A=X=Y=D=H=0, theorem top, and ten explicit safe heads above numerical tail2. AX contains no halt primitive and terminates on all natural arguments by its established arithmetic contracts. The actual blank execution is the suffix of this same exact source computation after the identified frame, so it reaches this root boundary too. This argument does not need to execute astronomically large numerical AX outputs concretely. The extra safe-zero wrapper present in tail2 is not needed for the conservative ten-head reserve.

At every candidate boundary the next counter is positive. Every ordinary command's finite source computation terminates or halts. Within a parsed candidate each positive residual is decremented before decoding; the remaining nested Cantor projections are at most that decremented value. Thus candidate continuations strictly descend and cannot trap the scheduler in an infinite single candidate. Every completed candidate reaches residual zero and the next refill, so the exhaustive schedule described above is operational, not merely a syntactic list.

The debt-seven theorem ensures that at least three of the ten initial explicit theorem heads remain after any nonhalting command prefix under conservative accounting. In particular every attempted S pop has an explicit safe head available and never reads opaque tail2. The usual theoremhood induction applies to top, cache and explicit heads. Any halt therefore gives a native refutation, and the inherited numerical-calculus calibration gives inconsistency of ZFC. Conversely a ZFC refutation yields a native refutation, whose reset-leading strong-compiler word is eventually executed by exhaustive enumeration, hence causes a halt unless an earlier halt already occurred.

Therefore this exact215-state binary, begun in state0 on a blank tape, halts if and only if ZFC is inconsistent, subject to the same explicitly inherited numerical-calculus calibration as ST215. It is a materially different scheduler alternative: it inserts an actual transfer before each raw candidate, not merely a reassociation or faster decoding of the same command trace. It is not a214-state construction, and its debt is seven rather than zero.
