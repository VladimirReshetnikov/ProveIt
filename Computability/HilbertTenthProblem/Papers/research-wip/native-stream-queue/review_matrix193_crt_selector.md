# Independent review of the integer CRT matrix selector

**PASS, with no requested author change.** This review authenticates and reads the complete frozen [helper](matrix193_crt_selector.py), [receipt](matrix193_crt_selector.json) and [proof](matrix193_crt_selector.md). It independently checks the arithmetic construction, all four local source arrays, both saved positive-history arrays and the stated mathematical domains. No predecessor or archived program was executed or imported.

| Frozen author file | SHA256 |
| --- | --- |
| matrix193_crt_selector.py | eb2449443cb61ee7b158d2727a15bc94d83b41c56a20a53bbc8072a3510409b6 |
| matrix193_crt_selector.json | 7c2c1f5330838eb942fb36a15961920f079cd4fd2a306732ca9d8ae589383455 |
| matrix193_crt_selector.md | 3e8e8323f98712db79d791c80e0f8acf1f859231fbf80f02742fab6dd44d733c |

## 1. Unrestricted integer argument

The six fixed CRT tables use the same selector. For L a positive multiple of 96! and m_i=1+(i+1)L, a common divisor of distinct m_i,m_j is coprime to L and divides j-i. Since j-i divides L, that divisor is 1. The shift T=1+max|entry| and L>2T place every shifted table entry strictly between zero and its modulus. An independent incremental CRT calculation, different from the author's sum of idempotents, reproduces all six complete fixed integers from the inherited 96 paired matrices.

The interval lemma is correctly restricted to integer witnesses and uses the explicitly identified four-square existence theorem. First z(95-z)=sum of four squares forces the integer z into 0 through 95. Only then is h=L(z+1)=m_z-1 known positive. Each equation v(h-v)=sum of four squares gives 0<=v<m_z. Together with the computed v=C-m_z*q and integer q, uniqueness of the least nonnegative remainder proves all six selected coefficients exactly. This is a paid polynomial construction with fixed compiled numerals; no variable remainder oracle or division is used.

For a selected determinant-one matrix [[a,b],[c,d]] with a nonzero, the residuals p-au-cv and aq-bp-v imply the complete row action. Indeed the second is a(q-bu-dv)-b(p-au-cv), and a can be cancelled over the integers or reals after the matrix has been recovered. The actual table has 192 such pivots, each 1 modulo 5. No cross-pair choice is allowed.

The sum of eleven residual squares is nonnegative over all real ports. Its integer existential zero relation is precisely the matched table relation. The note correctly does not claim real transition exactness: its rational quotient example makes all six recovered coefficients zero and maps nonzero rows to zero. The saved square decompositions and the complete example check directly. Global real nonnegativity remains sufficient for the later conjunctions; it does not remove the integer hypothesis from lookup recovery.

In the supplied-remainder alternative, the six additional residuals force the supplied remainders. Substitution of the computed remainders kills those residuals and gives a complete all-value polynomial identity with the computed source, in both the synchronized and countdown modes. This is stronger than a zero-set correspondence and does not require a matrix identity on solutions.

## 2. Independent literal-source checks

A fresh data-only checker used no author functions. It authenticated all six dependencies, compared the entire saved transition table and initializer/endpoint to the pinned parent, independently checked all 4,560 modulus gcds and all 576 residues, and recovered the full CRT numerals by successive two-modulus CRT combinations. It also checked every determinant and pivot.

The checker interpreted each actual source in a sparse polynomial ring, treating state ports, auxiliary ports and fixed-numeral bindings independently. It separately wrote the eleven or seventeen residual formulas, their full sum of squares and the full five-square LOAD factor. Every residual and complete output agrees coefficient by coefficient:

| Complete source | M | A | Total | Exact degree |
| --- | ---: | ---: | ---: | ---: |
| Computed synchronized | 61 | 67 | 128 | 8 |
| Computed countdown | 73 | 81 | 154 | 10 |
| Supplied synchronized | 67 | 79 | 146 | 4 |
| Supplied countdown | 79 | 93 | 172 | 6 |

The four sources total 600 paid rows and 34,881 full output coefficient entries. The independent audit checks closure, fresh producer names, output binding to the last row and liveness of every row, supplied port and named fixed numeral. It additionally compares twelve complete rational off-zero evaluations. This is full saved-source checking, not a component-cost estimate or weighted metadata census.

Exact degree is attained on the stated actual source lines with fixed coefficients genuinely specialized. In supplied mode the leading coefficient is 1 at degree 4. In computed mode q_K0=z=t gives the positive leading coefficient L^4 at degree 8. Setting n=t and next_n=0 adds the nonzero factor (t-1)^2, proving degrees 6 and 10 for the countdown variants. The independent line expansion confirms these coefficients. No intended-zero equality is used to lower a formal degree.

The two complete positive-history arrays were independently reconstructed by copying the actual local source after one subtraction per distinct supplied signed coordinate, sharing adjacent state coordinates, then copying the endpoint and adding all local outputs. Both arrays match literally: 202=76M+126A at h=1 and 397=149M+248A at h=2, totaling 599 rows. All their rows and ports are live. The general degree claim remains an upper bound after initial substitutions.

## 3. Countdown, positive witnesses and uniform contexts

The unchanged 26-row wrapper is E_load*(U+n^2+next_n^2). Both factors are nonnegative on all real tuples. Thus over integers its zero relation is LOAD, or the exact matched TILE at zero counters. A LOAD imposes no CRT auxiliary requirement. Starting from the unchanged integer initializer and natural input x, loads decrease the counter by one and tiles require zero; endpoint zero therefore forces LOAD^x followed by TILE steps. A load after a tile cannot return the counter to zero. This argument permits signed counters and does not assume their nonnegativity.

At fixed h, five next-state coordinates plus 35 auxiliaries per step give 40h signed witnesses. Summing the h local nonnegative polynomials with the seven-row endpoint pays h joins and gives 155h+7 operations. For a finite signed list, choose a shared positive integer s greater than the negative of its least entry and zero; each p_j=s+v_j is positive. Conversely p_j-s is an integer. The 40h distinct subtractions are all paid, yielding 195h+7 operations and 40h+1 positive witnesses. The ordinary input is not shifted or charged as a witness. Degree at most 10 and the two complete saved examples agree with the source.

The uniform-context claim is justified by the inherited group, rather than inferred from the numerical fixture. The pinned context proof retains H_i,G_i,C in H', and synchronized preprocessing uses C^(-1)H_i C. The pinned Gamma1 recoding puts H' inside Gamma_1(5), so all those first entries are 1 modulo 5 and cannot vanish. For larger fixed context matrices the proposed positive multiple of 96! exceeding 2T preserves the CRT proof and the same gate schedule. This proves a uniform fixed-context local upper bound under the inherited simulation theorem; it is not a new arbitrary-program compiler execution.

The note correctly separates finite duration from unbounded fixed-arity packing, and distinguishes the emitted numeric fixture from arbitrary compiled contexts. There is no new universal-operation bound and no assertion that either saved short duration accepts the fixture. The 84-operation universal result is unaffected.

## 4. Provenance and replay scope

The six direct predecessor pins were authenticated as inert bytes:

| Dependency | SHA256 |
| --- | --- |
| matrix193_gamma1_recode.md | 6349644283548af96f4a9582ee32d959a123c81bf1c2f902c45874ae45c96742 |
| matrix193_context_absorption.md | d7492809ba00a011c8280172bb016f96f3f6c240de6a823ed717d82bda5e4f4b |
| matrix193_synchronized_rows.md | ab768aa392841add5dc6dfcd8ed62564ca17fae2fe80e5ec39f1f4ceb36559d2 |
| matrix193_unimodular_selector.py | 34c98040cf2d20d88fbfdfe7e71ae88d6904547a5ab8102c0805c71d6bccc456 |
| matrix193_unimodular_selector.json | c03bc63e10398bb53e19fd1ad6f755fa132164379dce10c523de3ea0dd598e1c |
| matrix193_unimodular_selector.md | 87ee28420daa8d722b495137a9e76b316a74e95c64c94f656f592849f06640b2 |

This review reread the relevant context closure, first-row, synchronization and parent countdown passages. It does not independently re-prove the earlier faithful group encoding or semidecider simulation, and does not claim a new formalization of the four-square theorem.

Fresh normal and -O runs of only the new frozen author helper from / passed exact receipt comparison against the pinned data root. The source uses explicit exceptions and recursive type-exact receipt equality, rejecting duplicate keys, noninteger JSON numeric syntax and nonfinite numbers. No frozen predecessor, repository file or Git state was altered.
