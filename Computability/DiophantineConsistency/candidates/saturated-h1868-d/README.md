# The saturated H1868 equation in954 operations

`equation9.json` is exactly the same integer polynomial as the arriving
1086-operation H1868 saturated-radical equation. It has nine strictly
positive inputs b,g,h,s,w,C,i,j,n, exact degree999518, and **954 live binary
operations**. No variable, coefficient, domain or zero set is changed.
This saves132 operations while preserving the lower-degree endpoint.

The parent already computes D=(A^2-1)C^2+1. Reducing its333-term corrected
majorant by A^2*C^2=D+C^2-1 gives263 terms in A,C,D,i,Z. The selected Horner
order is Z,i,D,C,A. D remains a shared polynomial value, not an additional
unknown or an equation premise. All120 Horner orders were checked;954 is
the smallest count within this finite family, not a global optimum.

`rewrite.json` certifies the exact local identity and a complete retained
gate remap. `reduced_table.json` specifies every new monomial;
`HORNER_CHOICES.json` records every tested order. The final literal DAG uses
only binary addition, subtraction and multiplication, including all squares
and scalar products. Constant leaves and register reuse are free under the
same cost convention as the parent. Every node and declared input is live.

The complete original31 tuple and all12 materialized signed leaves are
included. No compact54 coefficient is substituted into this H1868 source.
MF_source is already shifted once. `PINS.json` authenticates the raw archive
members, including all payload bytes, source/kernel tables, parent circuit,
majorant and full shifted positivity certificate. The large certificate is
stored as a gzip of its exact original JSON bytes.

The archive is `ConZFC_Saturated_Certificates_2026-10-24.zip`, arriving at
d42be5cd87, SHA256
`dd462410bc9dee18a7b71cb0e5cedd2a4c615f7722fd7fe474303b8110af80fc`.
The raw1086-operation parent SHA256 is
`2c26978d50fc23724e9b678e06c65afc531f50946e101df2a1347ed9411ab08d`.
Original ordinary proofs and the license are retained under `source/`.

One correction to the retained ordinary text is recorded in `PEER_REVIEW.md`:
the population formula's coefficient of k is **4220**, although two printed
occurrences say4210. The delivered threshold parameters are correct. Their
unexpanded formulas agree exactly, for every k. The majorant correction is
**297874*C^24*i^6*Z**, distinct from the earlier H2082 correction2^20.

From the repository root, using Python3.12 or newer and the standard library:

```sh
python3 Computability/DiophantineConsistency/tools/build_saturated_h1868_d.py --check
python3 -O Computability/DiophantineConsistency/tools/build_saturated_h1868_d.py --check
```

Both checks reproduce every mathematical artifact byte for byte. Besides
the D rewrite, the tool checks every source/ratio/Pell/norm register as an
exact free-register identity and every complete kernel/weight/target
polynomial. It binds the whole333-term parent majorant, all12 leaf values,
all22 source extraction identities, the complete radical defect and positive
coefficient certificate, exact degree attainment, and the symbolic population
threshold. Modular samples are not used to justify these identities.

The ordinary proof of the new saturated H1868 finalizer was peer-reviewed;
see `PEER_REVIEW.md`. Its Con(ZFC) interpretation still composes with the
named native/source/refutation interfaces. No new Lean or encoded object-ZFC
derivation is claimed. All original archives and frozen candidates remain
unchanged, in accordance with the formalization pause.
