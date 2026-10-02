# Exact degree1936 for the emitted packed U15 polynomials

The published653 baseline, its652 state relabel, the647 computed-truth construction and its646 state-relabel composition all have **exact total degree1936**, with the four ordinary-input program numerals fixed. This applies to their raw-tape forms and to both computed-truth constructions' tagged parents as well. It is a separate degree certificate: the original compiler packets, receipts and upper-bound-only metadata remain unchanged, and no arithmetic operation count is improved here.

The [standalone checker](u15_packed_exact_degree1936.py) authenticates the compiler sources before importing them, rebuilds each complete literal polynomial and checks its SOS finalizer. Its [receipt](u15_packed_exact_degree1936.json) records every emitted source hash, formal upper bound and exact nonzero modular leading coefficient. Imports temporarily isolate sibling module names and restore the caller's original modules and path.

| Source and constructor | Raw operations | Ordinary-input operations | Exact degree in both forms |
|---|---:|---:|---:|
| `u15_packed_two_tape_history.build` |410|653|1936|
| `u15_packed_state_relabel652.build` |409|652|1936|
| `u15_packed_computed_truth647.build` |404|647|1936|
| `u15_packed_computed_truth647.tagged_parent` |413|656|1936|
| `u15_packed_composed_truth646.build` |403|646|1936|
| `u15_packed_composed_truth646.tagged_parent` |412|655|1936|

## Literal leading term

All moving supplied coordinates have degree1; fixed program numerals and integer literals have degree0. The complete source propagates bounds using addition of degrees at multiplication and maximum at addition/subtraction. This gives an upper bound1936, independently rechecked without using any equation true only on the zero set.

Let brackets denote highest homogeneous parts. The paid source has

    deg B=1, deg J=1, deg P=2,       [P]=[B][J],
    q=16 B P^34,                   deg q=69.

The highest controller region in the joined output is `P^5 * E28 * P^28`. Since `E28=edge28-1`, its highest part is `edge28 * [P]^33`, of degree67. The actual padded output is `F3=16 Zjoin+8`, so

    [F3]=16 edge28 [P]^33,         deg F3=67.

The actual Horner rows `native__bs_p0` through `native__bs_packed` compute

    r=F0+q F1+q^2 F2+q^3 F3.

For the baseline, relabel and tagged parent the first three truth fields are supplied coordinates of degree1. In the647 graph substitution, their propagated degrees are at most69,68,68, respectively. In every form, the last term uniquely dominates:

    [r]=[q]^3[F3],                 deg r=274.

The literal positive-scale and graph rows then give

    X=q(r+bound_beta),             deg X=343, [X]=[q][r],
    s=2 odd_half+1,
    Y=s q,                        deg Y=70,  [Y]=2 odd_half [q],
    k=eta+zeta,                    deg k=1.

The checker authenticates the actual row chain from `native__bs_X_bound` and `native__wn2` through `native__UM`, `native__UM2`, `native__scaled_norm_coefficient`, `native__ksn2`, `native__ratio_product2` and `native__L9`. The retained comparison `native__L9 = native__R9` has residual

    R=((XY)^2+X)*(Yk)^2 - tau*(tau+1).

Its unique highest term is

    [R]=[X]^2 [Y]^4 [k]^2,
    deg R=2*343+4*70+2*1=968.

Every displayed factor is a nonzero polynomial. In particular this residual has exact degree968; it is not merely assigned that formal bound. Its square occurs literally in the final polynomial. The real sum of squares of residuals cannot cancel its highest homogeneous square, so the complete polynomial has degree at least1936. Together with the emitted upper bound, this proves equality.

One other residual is assigned upper degree968 by naive propagation, but its leading coefficient cancels. The audit does not silently lower intermediate bounds after a cancellation and does not infer exactness merely from propagation. The nonzero `L9-R9` leader is the necessary lower-bound evidence.

## Finite exact certificate and all fixed program slices

For a particularly simple univariate certificate, set every moving supplied coordinate to t and every fixed program numeral to1. This is a polynomial substitution, not a claim to satisfy the Diophantine equations. The highest parts of B,J,P are

| Interface | [B] coefficient | [J] coefficient | [P] coefficient |
|---|---:|---:|---:|
| Raw half tapes |192|29|5568|
| Ordinary input, fixed program numerals |128|29|3712|

The checker propagates the exact coefficient at each gate's independently computed upper degree, modulo1000000007 and1000000009. A zero coefficient is retained as zero; no uncertain degree adjustment is made. Nonzero output coefficients are consequently rigorous witnesses of nonzero integer coefficients. Every form has the following full-output degree1936 coefficients:

| Interface | Mod1000000007 | Mod1000000009 |
|---|---:|---:|
| Raw |283741031|846402814|
| Ordinary input |417991546|494276243|

The independent dependency analysis follows which fixed program numerals could affect the coefficient at each formal upper degree. A sum retains only branches of maximal degree; a product takes the union of the factors' dependencies. The complete output's highest coefficient has an empty fixed-program dependency set. Thus choosing their values1 loses no generality for this coefficient: degree1936 holds for every fixed positive numeral quadruple, including every valid universal program slice.

The state relabel only changes lower-degree controller forms. The647 tags alter the two input joins but leave the output join/F3 and scale unchanged. Its computed truth fields remain below the dominant q^3F3 term. These source facts explain why all six constructors have the same degree and the same displayed slice coefficients.

## Reproduction and scope

Run from any current directory, with the repository's usual Python environment and the supplied source paths:

    python u15_packed_exact_degree1936.py \
      --root /path/to/native-stream-queue \
      --computed647 /path/to/u15_packed_computed_truth647.py \
      --computed646 /path/to/u15_packed_composed_truth646.py \
      --expect u15_packed_exact_degree1936.json

Omitting both optional computed-truth paths audits just the two published baseline/relabel constructors;646 requires647 to be included too. `--output` writes a fresh receipt. The artifact contains no fixed `/tmp` path, symbolic-CAS expansion, timing field or search. It uses only exact integer modular arithmetic and the actual emitted source. Compiler SHA256 pins are embedded and repeated in the receipt; the original upper-only packets are checked to remain upper-only.

This is an independent degree analysis of the named frozen sources. It neither reproves the native Pell/ordinary-input representation nor constructs complete positive Pell witnesses. It does not assert a minimal degree, a best state encoding or a smaller universal operation bound.

The frozen audit passed on all12 emitted forms with24 nonzero modular certificates. A fresh read-only replay reproduced the complete deterministic receipt. The separately reviewed row-chain proof and conservative fixed-program dependency analysis agree with those certificates; the compiler metadata was not changed.
