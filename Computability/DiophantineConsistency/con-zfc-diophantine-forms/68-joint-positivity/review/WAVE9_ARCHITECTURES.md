# Wave 9 architecture review

## Exact source boundary

Main reviewed: `9cca523d9f27ad39d52993f4065cbd7e58f8bdd4` (2026-10-23 21:16:10 UTC).
Arrival: `0c6be9a074d8905b22015e93c5c9d28eda36e95e`; placement: `a2cd79b9120fc75f48dcbef6e38d0f8b18d64d49`.
Eight archives are sources 60–67. `SOURCE_PINS.json` preserves original URLs, Git blob hashes, sizes and SHA256. Archive CRC, unique safe paths, all eight Git blobs and 1,800 manifest entries pass. No downloaded code was imported or executed. An independently authored inert JSON reader checks 108 recognized circuits: no dead arithmetic gates and no supplied operation-count mismatch. Degree claims below are manuscript claims, not newly certified exact degrees.

## Contributions and mechanisms

| Source | Main genuinely distinct mechanism | Claimed examples (domain / variables / degree / gates) |
|---|---|---|
| 60 Positive Gap | P=p+eta+zeta, tau=p+t, L=q²−1 replaced by S=q²; 89→86 records, square becomes pair; W100,H2047 | positive9 /1797796 /465; positive15 /24 /89 |
| 61 Congruence Carriers | successive q³, q⁵ divisibility recovery; divided auxiliary norm; mod4 unit-product finalizer | positive13 /34 /93; positive12 /118 /104; positive12 /172 /103; integer37 /6; integer34 /8 |
| 62 Sign and Norm | center root before norm; common-sign rank recovery; move square guard from q to X=8rho² | positive13 /114 /83; integer42 /4; integer35 /6; integer30 /8; positive9 /1834516 /453 |
| 63 Sign Recovery | common-sign rank recovery; absorb quotient into integral root; identity-deflated Pell majorant | integer42 /4; positive14 /34 /87; positive9 /1573266 /504 |
| 64 Structural Reductions | adaptive modulus Y²; delayed q-sign recovery using X=2u²; combined eta*zeta positivity | integer41 /4; integer36 /6; integer31 /8; positive14 /30 /83; positive9 /1781068 /470 |
| 65 Shared Taps | equal complete coefficient records share a position, 89 records→84 positions, H1873; successive carrier modulus4q²Y | positive9 /1675396 /458, /1738228 /457; integer10 /7428120 /525; positive14 /26 /92, /30 /85 |
| 66 Gap Congruence | gapN/gapNq85–86 record sources, global addition chains, T6 bound, leadless carry, one-stack local proof source | positive9 /1845940 /444 through /1503378 /483; integer10 /3507876 /494 or /3547076 /490; positive15 /24 /88 |
| 67 Oriented Guards | w=4u² allows joint eta*zeta guard; W108 with kernel orientation; higher Pell majorants; adaptive4qY | integer42 /4, integer36 /6, integer32 /8; positive9 /1731700 /462 or /1494006 /487; integer10 /3327556 /519; integer13 without Sun /10461744 /519; positive14 /30 /87 |

Important tradeoffs: source64's integer41 quartic is the lowest-variable quartic in this wave. Source62's integer35 sextic and integer30 octic beat source64's companion counts. Source61 has much lower positive12/13 degrees at greater gate counts; source62's positive13 degree114/83 remains cheaper. Source65's positive14 degree26/92 is lower degree than source64's degree30/83. Source66 remains lowest-gate nine-positive and ten-integer among the displayed new points; source67 has slightly lower minimal nine degree at more gates and lower ten degree at more gates. No total order or global minimality follows.

## Synthesis opportunities, not completed results

1. Shared coefficient positions (65) have not been combined with 66's 85/86-record positive gap sources. This could reduce packing height further, but it is incremental and requires exact collision identities, source bounds and unconditional positive-leading-word proof, not simply unioning position lists.
2. Source64's delayed-sign source and source62's centered/root-relocated elimination are compatible in spirit. Naively composing the existing elimination lists gives only 35-variable sextic and 30-variable octic again: source64 lacks source62's separate w=4u² definition and cannot delete that extra coordinate. It is not automatically a 34-variable sextic/29-variable octic.
3. New global proof-certificate compilation is the strongest truly separate path. Source66 supplies an explicit one-stack local polynomial, but its bounded-universal closure remains an uncompiled/unmaterialized constructor. Source67 only proposes fixed-input universal-machine boundary compilation. Neither is a completed new small consistency equation.
4. Direct binary disjointness is expressly raised in source62 but not implemented: binomial(S+T,S) odd instead of a larger central-binomial rank. A new low-cost polynomial interface would be substantial, but the carry identity alone does not provide it.

## Routes already investigated, to avoid rediscovery

Source67 alternatives/REVIEW.md discusses Carl–Moroz direct provability (15-axiom Gödel–Bernays without Choice plus equiconsistency), fixed-input Neary–Woods small universal machines, constructive Coq DPRM/FRACTRAN, and proof verification rather than enumeration. It reports no completed competitive endpoint. Its cited Carl–Moroz explicitization is enormous: 14,558,112 integer witnesses and a 877,757,576-decimal-digit constant. These are attributed literature figures, not independently reconstructed here.

Unordered FRACTRAN is not a sound universal replacement: arbitrary applicable fraction transitions are vector-addition-system reachability and lose priority/zero tests. Weak universal Turing machines require a genuine infinite-background boundary theorem. Finite-model search cannot replace ZFC-refutation search. A finite equiconsistent presentation still pays for syntax checking and proof translations.

Source60 rejects two auxiliary congruence substitutions as degree-increasing (to28 rather than24), and warns that eliminating w from X=wq through transport yields only q|XC, not q|X. Source62 gives 63*((4/3)^2−1)=7² as a counterexample to naive rational Pell-root integrality.

## Formal changes since prior pin

81ba91fa assembles package52 source→ratio→finalizer equivalence in nine naturals under four native-port bounds. 94d84e5c binds the full generic-ring evaluator and literal MvPolynomial Fin9 Z, and a31→16 coordinate elimination.

4edbd536 and263c7fd2 formalize split116 carry foundations, coefficient bounds, exact population calibration, unconditional word positivity, free carrier and compact native tuple arithmetic. 9a58fcec binds the actual old-z31 source, all89 records and exact kernels, removes code-size premises by cofinal power-of-two witnesses, and proves complete nine-natural zero existence iff with the literal22-row source. It also proves signed minus-form auxiliary Pell step-down.

Remaining expressly open: identity of optimized counted DAG with formal polynomial, authentic native compiler/K215 calibration for its actual ports, internal object-language ZFC equivalence. Repository-reported Lake/axiom audits are not rerun here. The new wave9 literal circuits are not automatically covered by package59's formalization. `FORMAL_PINS.json` and `formal/` retain the exact status sources.
