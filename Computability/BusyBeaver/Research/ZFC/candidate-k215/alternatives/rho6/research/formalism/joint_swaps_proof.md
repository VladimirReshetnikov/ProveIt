# Row-local parameter swaps on the exact accepted K215 source

## Result and precise scope

This note proves source-level calibration for three literal K215 variants. `joint24` simultaneously interchanges the B and C parameters in the quantifier distribution row rho2 and quantifier commutation row rho4. `joint246` also changes the formula parameter of rho6 from C to B. The third variant, `rho6`, makes only that latter change. The joint24 and joint246 source files have respectively SHA-256

- `0dc97dd296355d25b5dbb1bdaec1b3ece175074e9e92f5e79ca8b024874b82cc`;
- `96293da14c11f015f4f7aee13b3d5de04138feea6c55e1627cfe9f653126af5b`.

The rho6-only source has SHA-256 `19da13e482ea0f3d57432aad852bdf2448093e58a6e3b3873ac744eae7440693`.

All three have 202 distinct source subtrees, 4,751 primitive occurrences, 6,175 guarded control-flow edges, 6,176 runtime cases when the halt case is counted, maximum depth 47, and maximum zero run 6. A source subtree count is not a physical machine state count. A binary allocation still needs the quantified primitive-runtime theorem and a calibrated exact blank initialization before a blank nonhalting equivalence follows.

The row-permutation idea has predecessor work in the Source163 investigation on earlier 216/217 sources. This note does not claim to invent that symmetry. Its new concrete inputs are the exact accepted combined215 source and the explicitly reconstructed simultaneous variants. A successful new 215-state binary allocation and its full certification would be the machine contribution.

## The numerical calculus and exact emitted formulas

Let

    P(x,y) = (x+y)(x+y+1)/2 + y,
    I(x,y) = 4 P(x,y),
    Q_i x = 4 P(i,x) + 2,
    F = 1,  T = 0,
    N x = I(x,F),  Ex_i x = N(Q_i(N x)).

These are functions on all natural numbers. In particular I(0,0)=0; no syntax or well-formedness assumption is used. The accepted dominated calculus has theorem-only generalization, modus ponens, the exact gated theory bundle, and the retained logical rows, including

    rho2(A,B,C) = Q_A(I(B,C)) -> (Q_A B -> Q_A C),
    rho4(A,B,C) = Q_A(Q_B C) -> Q_B(Q_A C),
    rho6(A,C)   = Ex_A(Q_A C) -> C.

The final propositional row remains

    rho8(A,B,C,U) = ((C->U)->A) -> ((A->C)->(B->C)), U <= A.

`rho6` emits rho6(A,B) in place of rho6(A,C). `joint24` emits rho2(A,C,B) and rho4(A,C,B) in their original stack positions. `joint246` additionally emits rho6(A,B). The remaining rows, GEN value, truth behavior, gated bundle and gate are unchanged.

Each changed family is exactly the previous family as a set of numerical codes: (A,B,C) maps bijectively to (A,C,B), and the unused third parameter in rho6 is free. Therefore the old and new calculi derive exactly the same natural numbers, by induction on finite derivations replacing only an axiom leaf's parameter tuple. In particular they have the same refutations. This does not assume a substitution rule on arbitrary derived formulas, nor a formula-renaming theorem, nor that all three emitted rows are changed under one global substitution. The replacement is local to the axiom leaf being used.

The inherited dominated-row recovery certificate and native-calculus calibration identify this common refutability condition with syntactic inconsistency of ZFC. They remain inherited premises; the finite source checker does not reprove those mathematical results.

## Literal source binding and all-natural macro contracts

The input is the accepted `candidate-k215/sites215.json`, SHA-256
`17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba`.
At the formula-construction phase register 4 stores A, register 5 stores B, and register 3 stores C. Registers 1,2 are current formula and theorem stack; registers 6,7 are scratch. A closed parameter-load macro saves the previous current value on the theorem stack, copies the selected parameter into current, and restores the parameter and zero scratches. The implication macro combines the top pair of formula operands using the literal Cantor constructor; subsequent increments implement the other constructor tags. These are exactly the inherited source macros.

The source modifications interchange CI/CD operands 3 and 5, and nothing else, in these half-open ordinal intervals:

| Row | Interval | Old postfix constructor word | New word |
|---|---|---|---|
| rho4 | [1467,1766) | `abcQQbacQQI` | `acbQQcabQQI` |
| rho2 | [2062,2412) | `abcIQabQacQII` | `acbIQacQabQII` |
| rho6, optional | [888,1171) | `aacQFIQFIcI` | `aabQFIQFIbI` |

Here lowercase letters load natural parameters, and I/Q are numerical constructors; F pushes literal falsity1. `check_joint_swaps.py` derives the helper macros from the pinned accepted table/source decoder relation, verifies every closed macro tree, matches the entire primitive word of each interval, and independently parses its postfix expression. It checks that renaming registers 3 and 5 in a load tree yields the exact preexisting other load tree. The implication and constant constructors contain neither register, so they are unchanged.

The all-natural justification is register equivariance of the primitive operations: under a bijection of register indices, increment and guarded decrement commute with renaming, while break/continue/halt do not inspect registers. Thus every inherited load proof transfers to its exact renamed tree. Its loops terminate by the same natural-number measures, with the parameter value renamed. No bounded arithmetic sample is the reason this transfer is valid.

The two independent whole-source control resolvers agree for each variant. All 4,751 opcodes and all 6,175 guarded destinations are unchanged; only four CI/CD operands differ for rho6, sixteen for joint24, and twenty for joint246. Altering which register is tested changes execution, but the retained macro contracts prove exactly the new constructor output at each row boundary. At each changed row exit, the parameter registers, scratches, proof cursor, and control continuation are restored exactly as before. The current formula and theorem stack differ precisely by the specified replacement row, with the same stack effect and no additional input consumption. Each row consumes no extra proof-list fields, leaves every parameter restored, and produces exactly one formula value with the same stack effect. Therefore the outer AX contract has precisely the changed row outputs stated above and no other effect.

The parameter transformations do not preserve the literal code emitted by one fixed AX argument triple. They preserve the entire axiom family. This distinction is why the proof uses a repaired axiom-selection compiler rather than an incorrect equality-of-all-command-traces assertion.

## Exact command language and soundness

At a command boundary use tuple (t,S,d,h), where t is current theorem, S the Cantor-coded theorem stack, d an unconstrained numeric counter, and h the cached theorem. The accepted order210 commands are NIP0, DROP1, MP2 with a numeric field, and AX(c+3,y,x). Write [x]S=P(x,S).

The alternative command order120 interchanges the NIP/DROP tags: DROP0, NIP1, MP2, with the same AX fields. Every named-command block and arithmetic argument below applies unchanged to that order; only the wire names of NIP and DROP differ. A literal source/table binding is still needed for that second presentation.

The small commands are unchanged:

    MP(z): let b=d+z; if I(t,b)=h return (b,[0]S,b,0),
                            otherwise return (0,S,b,0).
    DROP: return (h,[t]S,d,h).
    NIP: halt if h=1; otherwise unpair S as [x]S' and return (t,S',d,x).

AX has U=d, A=d+x, B=h+y, C=c. It returns current g(A,B,c), counter/cache0, and stack

    [r1,r2',r3,r4',r5,r6',r7,r8,Q_U h,t]S,

where primes indicate exactly the selected row changes. The gate g is0 if c=A or c=B and otherwise the exact original bundle. All emitted rows and the bundle are implication codes, hence never1; Q_U h has residue2, hence is never1. These literal tag facts hold even for arbitrary junk inputs. The accepted U<=A restriction is untouched.

The theoremhood invariant is unchanged: t,h and every iterated stack head are derivable. Each modified row is an old admissible axiom instance. All remaining commands and fields have their accepted soundness proofs. A NIP halt therefore requires a theorem1. Only this safe-seed soundness argument assumes theoremhood; arbitrary work states are permitted in the completeness helper blocks below.

## Strong compiler and exact parameter recovery

Use the accepted strong block contract: starting at any (t,S,0,0), a compiler block for X either halts or returns (X,S,0,0). The accepted Discard block uses MP(1), AX(1;0,0), then ten NIPs; MP must fail against cache0 because I(t,1)>0. The AX gate is0 and its nine generated stack entries are not1. The changed logical rows retain that tag property, so Discard is unchanged.

After Discard, current/cache/counter are all0. To select an unchanged row with parameters (A,B,C), use the original AX fields (c=C,x=A,y=B), then the accepted stack-selection suffix for that row. To select rho2(A,B,C) or rho4(A,B,C) in either joint-swap source, use instead

    AX(c=B; x=A, y=C).

The actual tuple entering the emitter is (A,C,B), so the new row is rhoj(A,B,C), exactly the desired literal natural code. To select rho6(A,X) in rho6 or joint246, choose

    AX(c=0; x=A, y=X).

Its changed sixth slot is rho6(A,X). The unused actual C parameter can be0. Selecting rho6 in joint24 uses the unchanged original recipe. The row selection suffix only relies on the order/count of emitted entries and their being different from1; these facts remain true, regardless of the unrelated gate value for the adjusted tuple.

For an unrestricted rho8 derivation, first apply the inherited fixed dominated-row proof translation. To select a required dominated rho8 instance U<=A, use the original J(U) setter and original AX(c=C;x=A-U,y=B) block. The source U copy and row8 are unchanged. Bundle leaves likewise use their original fields and gate witnesses. GEN and MP compiler steps are unchanged because they depend only on the ninth GEN position, old current position, zero gate choices and safe constructor tags; no step uses the internal values of the discarded logical rows.

For completeness, the generic selector for stack position j is

    NIP^j; DROP; NIP^(11-j), 1<=j<=9.

Starting from AX with old current0, it returns the chosen row as current, restores the exact old stack, and clears the cache. The ten pushed values are the nine safe rows and old current0. This works with the literal pairing alias P(0,0)=0: each push/pop identity is used arithmetically, not as an assumption that an encoded zero stack has positive length.

Induction on a finite native derivation now gives a strong compiler block for every native theorem, with only the changed axiom-field recipes above. The original terminal DROP,NIP,NIP suffix detects theorem1.

## Cofinal search and permitted initialization

The accepted outer scheduler and all field readers remain literal. Positive proof-list pointers decrease between commands, and every arithmetic command terminates on all natural inputs, so each nonhalting candidate finishes and the candidate counter continues increasing.

For a compiled refutation tail with finite code R, prepend the original padding command AX(0;x=1,y=Y). It sets counter/cache to0 from every incoming retained tuple and emits only safe rows; the subsequent strong block accepts arbitrary current and stack. Its first-candidate number is exactly

    N_Y = P(3,P(Y,P(1,R))) >= Y.

Thus the family is cofinal above every finite starting counter. If a native refutation exists, a halting candidate eventually appears. Conversely safe-seed halting gives a native refutation. The accepted K215 calibrated startup has current/cache/stack0 and next candidate4, so it meets the source theorem; a changed physical machine must establish its own exact startup into this or another permitted frame.

Combining an independently established binary runtime and permitted startup with this source theorem gives, by ordinary reasoning formalizable in ZFC,

    not Halts(M,blank) iff Con(ZFC).

This note alone supplies no new proof-assistant endpoint and no unconditional nonhalting claim.

## Bounded source census

`row_combo_search.py` exhaustively considers the 6^7=279,936 independent permutations of natural parameter registers3,4,5 in the seven retained ungated row spans, preserving the accepted literal source association. Hash-consed source trees and exact subtree unions count distinct nodes. The minimum is202, achieved at exactly four parameter recipes: identity, joint24, rho6-only, and joint246. All four minimum literal source metrics were independently recomputed using the accepted tree utility. This is exhaustive only for the stated finite family and fixed association; it is not a source-program or TM state lower bound.

The search finished in 11.111 seconds in this run. Its exact histogram is retained in `row_combinations_results.json`; all279,936 recipes were evaluated. The initial source-certificate invocation had a Python lexical-spacing typo and failed before writing outputs. The corrected invocation succeeded; that authoring failure has no mathematical effect and is not claimed as a successful check.
