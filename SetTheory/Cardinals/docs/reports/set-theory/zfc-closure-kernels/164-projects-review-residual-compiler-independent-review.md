# Independent review: retained gate residual and parameter-free MP

## Reviewed claim and scope

The command interpreter specified in `formalism-work/residual_parameter_compiler.tex` has the same refutation predicate as the unchanged native numerical calculus, assuming the displayed command contracts and the inherited exhaustive candidate shell. The proof is valid with the **one-sided** residual

\[
\kappa(c,a)=\max(a-c-1,0).
\]

It does not require an absolute difference. The only residual identity used by the proof compiler is `κ(0,v+1)=v`.

This review is a mathematical verification of the interpreter proof and of the local comparison change. It is not a proof-assistant certificate, a full source-emitter verification, an exact-table runtime certificate, or a state-count claim. The abstract command contract, source implementation, and physical machine remain distinct obligations.

## Literal comparison change

The reviewed source builder is `encoding-work/build_residual_d.py`, acting on `encoding-work/mp-only/transplant.json`. Its second comparison is extracted from old ordinal interval `[4578,4590)`. Replacing its H-clearing loop by the transfer H→D gives the following local CFG. Here H is register5, X is register6, D is register4, and the current theorem T is register1. `dec R` branches to its zero target if R was zero; otherwise it decrements R and takes its positive target.

| Local ordinal | Operation | Zero / only target | Positive target |
|---:|---|---:|---:|
|0|dec H|4|1|
|1|dec X|3|2|
|2|jump|0|—|
|3|jump|5|—|
|4|dec X|11|5|
|5|dec H|8|6|
|6|inc D|7|—|
|7|jump|5|—|
|8|dec X|10|9|
|9|jump|5|—|
|10|exit|—|—|
|11|dec T|exit|12|
|12|jump|11|—|

The entry condition is `(H,X,D,T)=(a,c,0,t)`. Its universal behavior follows by three cases.

* If `a=c`, the first loop consumes both counters together. Both guards then see zero, so the final loop clears T. The result is `(H,X,D,T)=(0,0,0,0)`.
* If `a>c`, the paired decrements consume c units from each counter. One more H decrement is performed before the empty-X guard exits. The remaining `a−c−1` units of H are transferred to D. X stays zero, T is retained, and the result is `(0,0,a−c−1,t)`.
* If `c>a`, the paired decrements consume a units from each counter. The next H guard is zero and one extra X decrement leaves `c−a−1` in X. The H→D transfer is empty, the cleanup clears X, and T is retained. The result is `(0,0,0,t)`.

All loops terminate because their decremented counters are natural numbers. This proves the local contract for arbitrary inputs, independent of any finite test bound. The previous source instruction transfers A from D to H, so D is zero at entry. The other proposed source changes—consuming the last old-U load and deleting the MP read—must still be checked in their exact emitter/control context.

## Stack arithmetic and aliasing

Write `[x]S=P(x,S)`, using Cantor pairing. Every macro calculation uses only the exact inverse equations

\[
\operatorname{unpair}(P(x,S))=(x,S),\qquad P(0,0)=0.
\]

Thus `[0]0=0` is harmless. A displayed prefix is an algebraic expression in the old stack S; it need not be a uniquely delimited finite list. Popping the displayed prefix restores S exactly, including S=0. The alias `I(0,0)=0` is harmless for the same reason: MP checks numerical equality, and the positive case is constructed with exactly the same `I(a,b)` expression on both sides.

The nine newly emitted AX entries are never1. The eight rho entries and gated bundle are implication codes; the GEN entry has tag2. This constructor-tag fact is stronger than a consistency assumption and is needed for the exact reset theorem.

## Exact block calculations

Use state `(T,S,D,H)`, and let `N` denote NIP. The cache is tested for1 **before** NIP pops its next entry. This distinction makes the reset work even when the initial current theorem or cache equals1.

| Block | Entry condition | Result, unless noted |
|---|---|---|
|`AX(0,0,0);N^10`|Arbitrary state|`(0,S,0,T)`|
|`RESET=(AX(0,0,0);N^10)^2`|Arbitrary state|Exactly `(0,S,0,0)`, with no halt|
|`SET(v)=AX(0,0,v+1);N^10;DROP;N`|`H=0`|`(T,S,v,0)`; halts exactly when old `T=1`|
|`N^j;DROP;N^(11−j)`|After AX from current0, for `1≤j≤9`|Chosen j-th new entry current, S restored, H=0|

For SET, the first gate is0 because B=C=0. After the ten pops the cache contains old T, while current T is0 and D=v. DROP restores old T as current and pushes0; the final NIP either detects old T=1 or pops that0. No old stack entry is lost.

For selection, after j pops the remaining prefix has `10−j` entries. DROP pushes the gate, leaving exactly `11−j` entries to remove. The last is the old current0, so the final cache is0. This includes the GEN position j=9, whose cleanup consists of two NIPs.

## Derivation induction

The correct contract is universal in **all four** input values: a proof block for X either halts or maps `(T,S,D,H)` to `(X,S,D',0)`, for some unrestricted D'. This universality permits one premise to sit below the other proof block's temporary output.

Truth is compiled by RESET. A native rho row is compiled by resetting, setting its fourth parameter U, executing AX with absolute A and independent B,C, then applying the selection block. A native bundle uses RESET, its gated AX, and ten pops. These blocks preserve the original S exactly.

For GEN, after its premise block and SET(i), the state is `(H,S,i,0)`. DROP;NIP makes it `(0,S,i,H)`. AX(0,0,0) emits `Q_i(H)` in position9 and returns gate0. Selecting position9 gives `(Q_i(H),S,0,0)`. If the premise block or setter already halts, the contract's alternative is satisfied.

For MP, execute the first premise block, DROP, the implication premise block, and SET(B). The resulting state is `(I(A,B),[A]S,B,0)`. The next NIP;DROP;NIP produces `(A,S,B,I(A,B))`, unless it halts because A=1. The parameter-free MP then succeeds, producing `(B,[0]S,B,0)`. Its final cleanup NIP restores S and leaves H=0. The success push of0 is essential to that last cleanup count.

The induction uses no rule of uniform substitution and no formula decoding. Its arithmetic parameters range over all natural numbers, including junk formula codes.

## Soundness and enumeration

The numerical parameter D is intentionally absent from the theoremhood invariant. Current T, cache H, and every accessible stack entry are native derivable. DROP and nonhalting NIP preserve this invariant. Successful MP applies the native rule; failed MP returns truth. AX emits native rho instances, a GEN instance of the old cache, and a gated bundle or truth. The residual only changes D. A NIP halt therefore witnesses derivability of1.

Conversely, a native derivation of1 has a universal proof block. If it returns, DROP;NIP;NIP halts. Hence some finite command word halts from every work state.

For the candidate shell, define `E([])=0` and `E(c::p)=1+pack(c,E(p))`. The corresponding first raw candidate is `E(word)−1`; subsequent command cursors are positive E-values. Every continuing command consumes its positive cursor by decrementing once and taking Cantor tails, so the cursor strictly decreases. This includes the zero aliases and the final MP code. An arbitrary AX prepended to a universally halting suffix preserves universal halting and can make the candidate code arbitrarily large. Thus skipping any fixed finite initial candidate interval does not weaken completeness.

Together these establish exact equality of refutation predicates at the command level. Composing with the repository's accepted native-calculus/ZFC calibration gives the intended consistency comparison for a correctly implemented exhaustive interpreter. The source and physical runtime obligations are not supplied by this semantic argument.


## Final checker replay and opposite residual

The final corrected `check_residual_contracts.py` was inspected and replayed independently, producing `residual-contracts-replay.json`: 4,619 exact integer cases passed. It now refuses disabled assertions and includes protected falsity stacks in the selection and induction cases. Its HOLE operations represent the inductive hypothesis; they are not machine instructions.

For the alternative residual `κ'(c,a)=max(c−a−1,0)`, use `AX(v+1,v+1,0)` in SET(v). From cache0, this sets B=C=v+1 and A=0, so the gate is0 and the residual is v. The reset, row selection, GEN, and MP arguments are unchanged except for this setter. The final replay includes432 cases for that alternative.
