# Exact all-length splice and halting-equivalence corollary

## Review status and dependencies

The literal topological splice and its arithmetic ledger are complete and checked. The all-length mathematical theorem below additionally uses the independently developed pair-recoder theorem in the sibling fixed-digit-dilation packet. That theorem's Pell/Lucas proof is a separate review obligation; finite word tests or a correct splice alone do not establish it. The original `PROOF.md` remains a valid fixed-length/conditional-wrapper result independently of that obligation.

Pinned pair source for this splice:

    pair_inline-dag.json file SHA256
    a8fbf064395d2fac5aa041a4c54826938ea2645fba793e0de7500e19f7ca4567

`compose_initialization.py` reads this own-code arithmetic JSON as data. It executes neither a recoder source script nor any upstream program, saved ant schedule, Pell library, or downloaded proof program. Its receipt records the source hash. The separately cited theorem must concern this exact arithmetic source or establish an exact replacement identity.

## 1. Pair-module contract needed

For G>=2 and arbitrary positive RawLeft,RawRight, let L and R be their unique binary-sentinel lengths:

    RawLeft=2^L+sum ell_j*2^(L-1-j),
    RawRight=2^R+sum r_j*2^(R-1-j),

with nearest-head-first bits and empty word code 1. The required module has 392 strictly positive internal witnesses. Its 228 equations, after its three output equations are turned into wire aliases, have exact projection

    A=G^(L+R),
    B=G^R,
    T=G^(R+1)*sum ell_j G^j + sum r_j G^(R-1-j).

The outputs A and B are positive; T is nonnegative and can be zero. All three are arithmetic expressions in module inputs and its positive witnesses. They are not newly supplied variables in the inlined source.

The module source contains 454 multiplications and 601 additions/subtractions, hence 1055 operations. Removing the three comparisons A=expression, B=expression, T=expression removes three equations only; equality assertions do not themselves cost arithmetic gates, and **no operation is deleted**. The existential witnesses for these three expressions were never part of the 392, so none is subtracted from that count.

## 2. Literal topological splice

The complete initializer has external ports

    RawLeft, RawRight; W, Wp, Q, InitialHead, InitialMemoryPlus.

The first two are raw positive inputs. The remaining five are inherited positive parent-history ports/wires with the geometry assumptions in `PROOF.md`; they are not added to the component's 396 new witnesses.

The exact source order is:

1. Begin the fixed wrapper. Its node 25 is G=W^576000, already computed by one 23-multiplication binary chain
2. Complete its initial geometry expressions through node 31
3. At the first use of the A output, insert every recoder arithmetic node in order, remapping its G input to the already-existing node 25, and its raw ports to RawLeft,RawRight. Recoder witnesses receive a distinct `Recoder:` name prefix
4. Assert all 228 recoder equations, with their references remapped to the inserted nodes/witnesses
5. Substitute the recoder expressions for A,B,T, and continue the wrapper

The recoder occupies arithmetic nodes [32,1087). In the current exact source the output aliases are

    A -> node 1083,
    B -> positive existing witness Recoder:R_radixPower,
    T -> node 1086.

The wrapper then constructs G^(L+R+1) as A*G in one multiplication. That multiplication is already included in the 2,305,332-operation wrapper count. The shared G chain is not repeated. No forward reference, quotient instruction, digit extraction instruction, exponent oracle, or zero-to-positive adapter is introduced by the splice.

`PairSource` validates operation names, local source order, references, witness uniqueness, and the exact three declared output aliases. The host DAG validates every resulting arithmetic reference and every equation endpoint. Both use literal +,-,* gates only and explicitly reject optimized Python. These checks establish the syntax/topology of this own fixed source; they are not a claim to parse arbitrary adversarial expression languages.

## 3. Exact all-length initialization theorem

Assume the pair-module theorem above and the pinned parent geometry. Then the composed source has a positive solution exactly when there are integers a>=2 and k>=L+R+1 such that

    w=1+a*u, h=2*k*v,
    InitialHead=3^u W^(k*v),

and InitialMemoryPlus-1 is precisely the frozen periodic ant background on that rectangle, altered by the frozen anchor and the literal input loader for the raw sentinel words, then translated by (u,kv) in normalized coordinates. Here u=481238074400, v=576000.

Proof of soundness. The pair theorem gives the unique word lengths and the three correct expression outputs. Since G=W^v, substituting those expressions into the wrapper reproduces exactly the formulas established in `PROOF.md`, sections 2--4, with n=L+R and m=n+1. In particular H=P*A*G implies k>=m with P=G^(k-m), and T is exactly the polynomial for reverse(ell),0,r. The geometric, background, anchor and input proofs therefore apply without a length-dependent source. The image is a ternary Boolean word on the whole rectangle; there is no extra finite-background promise.

Proof of completeness. Given such a board and the two raw inputs, the pair theorem supplies all its 392 positive witnesses and the asserted outputs. The wrapper's four positive witnesses are

    Xextra=(3^(a*u)-1)/(3^u-1)-1,
    H=W^(k*v),
    K=(G^k-1)/(G-1),
    P=G^(k-L-R-1).

They are positive, including P=1 at the tight boundary k=L+R+1. The proof of the fixed wrapper supplies every equality, and the recoder equations use the very same G expression and the same raw codes. There is no auxiliary-name collision and no further compatibility constraint.

The old fixed-length source is still useful as an independent algebraic reference and regression fixture; the inlined all-length source is one fixed finite arithmetic relation.

## 4. Initialization ledger, separate from history and endpoint

The exact initializer counts are

    2,305,332 + 1,055 = 2,306,387 operations,
    1,152,738 + 454 = 1,153,192 multiplications,
    1,152,594 + 601 = 1,153,195 additions/subtractions,
    6 + 228 = 234 equations,
    4 + 392 = 396 new strictly positive witnesses.

A,B,T are expression aliases, so no three additional existential coordinates and no Tplus subtraction occur. The nonnegative quantity T is never quantified as a positive raw port. The host's five parent values remain inherited ports. These conventions are essential to the count.

The combined source SHA256, hashing every gate and equation in order, is

    503215b20d317cfb9e6e40ec82eb26044afbdedf26f37e03029bcd7dc0a04130.

The source uses free prescribed fixed coefficients under that ledger. The pair source adds the literal numeral 4; the strict prefix from `PROOF.md` already builds 2, so add one operation 4=2+2. Its combined literal-1/3 prefix is therefore

    277,193,130,853,952,587M
    277,193,130,853,952,485A
    554,386,261,707,905,072 total extra operations.

The strict all-length initializer total is **554,386,261,710,211,459** operations. This is an exact deliberately unoptimized finite source grammar, not an expanded or executed 10^17-gate artifact. The prefix adds no existential witnesses or equations. It does not pay the inherited history's fixed numerals or a final sum-of-squares combination.

The history's 174 operations, its 61 positive unknowns, its five positive parameter ports, and the endpoint selector's separate arithmetic/witnesses are not included here. Consequently these initialization figures are not numerical universal equation bounds or optimized record claims.

## 5. Qualitative existential-composition corollary

Under the pinned 174-operation bounded-history theorem, the fixed literal-interface theorem, the pair-module theorem, and the separately proved normalized endpoint selector, existentially bind all five non-raw history parameter ports

    InitialMemoryPlus, FinalMemoryPlus, InitialHead,
    FinalHead, FinalSignPlus

and use the parent's existing W,Wp,Q witnesses in the initializer. This gives one fixed positive Diophantine relation on (RawLeft,RawRight) which holds exactly when the pinned U15 machine, started in A scanning 0 with the decoded nearest-head-first words, reaches J1.

Soundness. Every solution of the history component describes a positive number of ordinary no-escape ant steps, starting with the initial Boolean word and a north-facing even-parity head. The initializer proves that this word and head are exactly a translated finite restriction of the infinite initialized literal interface. Since no history step leaves the board, induction identifies it with that infinite run. The endpoint selector imposes the single reachable normalized residue-and-heading predicate. Its residues are unchanged by the translations u and kv. The literal interface's acceptance soundness then gives U15 halting. Existentially choosing a final memory does not weaken this implication; the parent proves it is the actual final Boolean board.

Completeness. If U15 halts, the literal interface reaches the required physical event after a positive finite number of ant steps. Choose a>=2 and k>=L+R+1 sufficiently large that the whole prefix lies in the rectangle after translation by (u,kv), as proved in `PROOF.md`. The initializer theorem gives its 396 positive witnesses. The parent-history positive converse supplies all of its witnesses, with InitialMemoryPlus and FinalMemoryPlus one greater than the actual nonnegative Boolean board words, InitialHead and FinalHead positive powers of three, and FinalSignPlus=1 at the white/east accepting endpoint. The endpoint converse supplies its positive witnesses. Therefore all joined equations hold simultaneously.

No initial zero-time acceptance is needed: the literal interface explicitly excludes its acceptance predicate at initialization. Every port that is existentially bound here is genuinely positive, so no implicit nonnegative-to-positive adaptation was omitted in this qualitative statement.

This closes the raw sentinel pair to initialized literal-ant history interface qualitatively. It does not implement an arbitrary-program-to-U15-word compiler; that remains the published dependency already isolated in Report40. It does not claim new qualitative turmite universality, physical ant halting, or a smaller universal operation record. Turning all joined equations into one polynomial and publishing a complete merged numerical ledger would be a separate, straightforward but explicitly unpaid accounting step here.

## 6. Completed own checks and their limits

- Both complete 2.3-million-gate wrapper variants were streamed and checked before the splice
- The full 2,306,387-gate composed initializer was streamed, topologically validated, and hashed
- Forty-eight independent signed, off-solution assignments compare every spliced residual with separately evaluated recoder equations plus wrapper residuals, after substituting the exact output expressions
- Eight malformed arithmetic JSON mutations are rejected
- The shared G chain is counted once; its earlier source reference and the three actual output aliases are recorded

These checks prove literal-source correspondence and catch composition mistakes. They do not replace the pair theorem's all-integer Pell/Lucas proof, instantiate its astronomical witnesses for arbitrary inputs, run the dense periodic ant board, or execute the strict giant constant prefix.
