# Independent review of the complete113 selective gap family

**PASS.** The frozen [author source](complete74_gap_selective_projection113.py), [receipt](complete74_gap_selective_projection113.json) and [proof note](complete74_gap_selective_projection113.md) implement the stated complete positive-zero transformation. The default polynomial costs **113=53M+60A**, uses **24 positive witnesses** and **13 residuals**, and has **exact degree28** for every admissible fixed compiler slice. No author correction was requested.

The [independent checker](review_complete74_gap_selective_projection113.py) and [receipt](review_complete74_gap_selective_projection113.json) authenticate the complete author trio and nine inherited source/receipt/proof files. They independently reconstruct all256 emitted circuits, their current comparison maps and entire sum-of-squares finalizers. The checker executes the authenticated author's public API only for bounded contract checks; its source reconstruction, coefficient algebra, leading forms, ledgers, graph evaluations and frontier calculation do not call the author's proof or verification routines. Historical compiler modules are not imported.

## Coordinate theorem and the order of its proof

In the actual raw30 parent, write X=wq³, Y=sq³ and L=XY²k. The supplied k remains an independent witness unless its particular definition is selected. The parent first equation is L(L+k)=tau²−1. The new variable g restores tau=L+g, and exact expansion gives

    L(L+k)−((L+g)²−1) = 1−g²−L(2g−k).

The new comparison reverses the historical L9/R9 operand order, so its residual is precisely this expression, with no sign discrepancy. Source reconstruction checks that the removed first_next register and old tau have no unrelated live consumers.

For every positive new tuple, L>0 and the restoration tau=L+g is positive. For an old positive zero, the first equation itself gives tau²−L²=Lk+1>0; hence tau>L and g>0. This establishes the inverse's domain before invoking any parent universality or native Pell theorem. It does not assume that a gap is already positive because it later acquires a typed computational interpretation.

Every one of the eight permitted graph definitions is triangular and positive on the whole retained positive domain:

    q=(B−1)Jrep+1, C=Z+W, k=eta+zeta,
    a=XY+Y, c=kY+eta,
    d=X+a*c+ga*(4a+3),
    kappa=twice_cell_bits*x+inner_bits+delta*(a²+4a+3),
    mu=W+a*kappa+rho*(4a+3).

This remains true for arbitrary subsets in the prescribed order. The default selects q,C,k,d,kappa,mu, retaining a,c. Deleted comparisons vanish identically on the graph; the local expansion handles the first retained comparison, and literal substitution handles every other retained row. Thus the **entire parent SOS after restoration equals the child SOS on all integer or rational tuples**, and in fact over every commutative ring. The positive graph maps are mutually inverse on the complete positive zero sets.

This is a graph identity, not equality at unchanged coordinates. Projecting a positive off-zero parent tuple can produce a nonpositive g; the public positive-mode projection correctly rejects that case. A separate signed mode retains the algebraic map. Similarly, arbitrary positive numeral ports need not encode a valid compiled program; the inherited universal language interpretation applies to the established fixed-program recipe.

## Full source and costs

For all256 subsets, the independent checker reconstructs each source row from the authenticated raw74 packet, applies only the selected aliases and the five changed/added gap definitions, and separately reconstructs the full finalizer. It checks every retained/deleted comparison index, exact supplied-coordinate set and live dependency closure. All75 certificate operations remain live.

With n selected definitions, the literal counts are

    witnesses = 30−n, residuals = 19−n,
    certificate = 75 = 40M+35A,
    complete SOS = 131−3n = (59−n)M+(72−2n)A.

The q substitution exchanges q−1 for repunit+1 and preserves the certificate count. Residual subtraction, squaring and final accumulation are paid, as are all multiplications by fixed numerals. All24 default witnesses, x and all six fixed program ports occur in the complete source. There is no omitted endpoint, input relation or scale condition.

The independent circuit census covers19,200 certificate rows and30,464 live complete gates. Four numerical graph cases per form give1,024 whole-polynomial equalities and19,456 individual parent-residual checks, including256 rational cases and256 unconditional positive restorations. These supplement the symbolic row reconstruction; finite evaluations are not the proof of universal equality.

## Exact degree, uniformly in the program

The independent leading-form calculation retains all six fixed compiler numerals as formal coefficient variables and all supplied input/witness coordinates as degree-one variables. It uses a separate sparse multivariate polynomial implementation. The only degree reductions beyond ordinary propagation use the explicitly expanded identity

    (a*z+v)²−(a²+H)z²−1 = 2azv+v²−Hz²−1.

This is applied to the actual main norm only when d is eliminated, and to the actual input norm only when mu is eliminated. The checker verifies the actual defining rows and substitutions; it does not reduce modulo any residual equation.

It reconstructs the complete highest homogeneous SOS polynomial for every one of the256 forms. Each maximal residual's leading coefficients exclude every fixed program numeral except b=B−1. Setting ordinary coordinates to t and g to3t leaves an attaining coefficient polynomial in b with coefficients of one sign. Consequently it is nonzero for every b>0. Together with the exact polynomial upper bounds and the sum of real squares, this proves all256 recorded exact degrees uniformly, rather than only at one program or at a few numeric specializations.

For the default, the residual degree bounds independently match

    1,5,4,14,5,9,8,8,6,10,2,3,7.

The whole degree28 homogeneous part is exactly

    b^18*w²*s^4*(eta+zeta)²*Jrep^18*(2g−eta−zeta)².

The checker compares this closed form coefficient by coefficient with its independently propagated complete leading polynomial. Only the first residual reaches degree14. Its specialization has coefficient −8b^9, and the complete SOS has coefficient64b^18 at degree28, so there is no exceptional admissible fixed program slice.

## The finite frontier and public contracts

All256 subsets occur exactly once. The independently computed family frontier is113/28, two distinct110/68 forms, and107/84. Comparing to the authenticated earlier operation/degree catalogue adds only113/28:

    86/179,87/135,88/123,89/113,90/109,91/102,92/80,
    93/72,94/62,95/54,96/50,97/48,98/44,113/28.

The earlier points have19 witnesses; the new point has24. This is a finite achieved tradeoff catalogue, not an optimality claim. The separate74-operation comparison bound and86-operation one-polynomial bound are unchanged. Later unit-grouping successors are outside this frozen review.

Public API checks cover nine representative complete packets and graph roundtrips,172 malformed calls including nine warm dependency-pin changes, four defensive-copy checks, and a separate optimized-Python rejection. Malformed cases include missing packet fields, every default polynomial row's changed operation, reordered/duplicate/incorrect selector types, nested list/tuple changes, float ledger aliases, Boolean operands, an altered parent comparison, incomplete or surplus assignments, noninteger inputs, non-Boolean signed flags, off-graph input to projection, and nonpositive restored-gap boundaries. The author authenticates complete typed packets and rereads pinned parent bytes; it has no mutable canonical cache. These are bounded API tests, not a general process-security audit.

No full accepting universal Pell witness was materialized. Universal correctness follows from the proved complete positive-zero bijection with the authenticated parent. The author note's finite first-norm examples are accurately distinguished from full compiled-program witnesses.

## Reproduction and pins

Use only Python's standard library, with the maintained dependency directory and the directory holding the frozen author trio:

```sh
python3 review_complete74_gap_selective_projection113.py \
  --root /path/to/native-stream-queue \
  --subject-root /path/to/native-stream-queue \
  --expect review_complete74_gap_selective_projection113.json
```

`--output PATH` writes the deterministic independent receipt. The author source, receipt and note pins are respectively:

    573f1e8b0c89ef039a2a7fc40bad959cf7e362bcec4c96b3536974e7b71316c4
    2636f00a9e67f53a144986382442f456427257d498e33960e023e9c986b6b9c3
    3539d2fa0721eb8448409d075261a6508cc7adc1d887e3905cfeaed737396afa

The saved independent receipt records its own checker source hash and all dependency pins. Writer and fresh read-only replay from another working directory pass. This review changed no author artifact or repository file.
