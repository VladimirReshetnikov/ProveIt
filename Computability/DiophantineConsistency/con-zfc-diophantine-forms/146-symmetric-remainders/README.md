# Symmetric remainder bounds for Diophantine consistency

Research contribution prepared with AI assistance for Vladimir Reshetnikov and ProveIt, 25 October 2026.

Start with **report.pdf**. Its editable source is **report.tex** and the two literal appendices in **report_inputs/**. The paper defines the equations, proves the new unbounded arithmetic lemmas, explains the inherited logical calibration, and prints every residual of the principal quartic and the complete fixed-coefficient recipe for the compact equations.

## Results

Every equation below has a solution in its stated domain exactly when there is a finite syntactic ZFC refutation, by the ordinary proofs in this packet composed with the identified ProveIt calibration. Therefore its absence of solutions is provably equivalent in ZFC to Con(ZFC).

| Direct equation | Domain | Variables | Degree | Quadratic residuals | Collected terms | Coefficient height |
|---|---|---:|---:|---:|---:|---:|
| Principal `direct/equations/symmetric_caps` | All integers | **260** | **4** | **185** | **5,099** | **128,446** |
| Alternative `direct/equations/dimension259` | All integers | 259 | 4 | 184 | 21,287 | 240,653 |
| Inspected incoming parent | All integers | 282 | 4 | 192 | 5,491 | 128,446 |

The principal saves **22 integer unknowns, seven residuals, and 392 collected terms**, preserving degree and height. The 259-variable variant spends much more support and height to remove one further coordinate. Both are fully specified ordinary polynomials.

| Compact equation | Domain | Variables | Live binary operations | Exact degree |
|---|---|---:|---:|---:|
| `compact/equation77.json` | Strictly positive integers | 10 | **77** | **626** |
| `compact/equation78.json` | Strictly positive integers | 10 | **78** | **464** |
| `compact/equation79.json` | Strictly positive integers | 10 | **79** | **460** |
| Immediate first parent | Strictly positive integers | 10 | 78 | 630 |
| Immediate second parent | Strictly positive integers | 10 | 79 | 468 |

Every live binary addition, subtraction, and multiplication counts, including squares and fixed scalar multiplication. The compact equations retain the entire four-integer coefficient tuple; its largest port has 592,884 bits. Those coefficients are constants, not additional unknowns. Their complete bytes and finite reconstruction are included.

The direct quartic uses the numerical C222 calculus and does not require K215 simulation or Jones universality. The compact family retains its inherited native/K215 specialization. These two ancestries are intentionally explicit.

## New mathematics

1. **Recover signs from a small canonical residue.** If a true residue modulo L lies in [0,L/8), a congruent signed integer with absolute value below L/2 must be that residue. The self-sized radix supplies this margin, including a proof for the factorial digit before factoriality is known. Eleven independent interval-product predicates become four quadratic rows

   `L^2 - 4*sum(r_i^2) - 1 = u^2 + v^2 + w*(w+1)`.

   Each group needs only three integer witnesses. This replaces 33 old witnesses by twelve fresh ones.

2. **A polynomial comparison center needs only modulus C.** The center `D=A+(1-A)*H^2` gives the required two congruences. Pell growth permits weakening the second modulus from 4C to C, with a separate proof excluding the small exceptional anchor. This avoids both an auxiliary CRT choice and a new parity constraint. The center polynomial itself has an explicit predecessor; the weaker-modulus composition is the new step here.

3. **Orient only the nine pairs that require it.** Use nine linear small-residue errors `1-X_i`; positive indices or an already positive power output orient the other five pairs. The proof treats negative centers and negative proposed exponents before using arithmetic signs.

4. **Use only the necessary divisor in the compact carrier.** The compact argument works for any outer polynomial D with `D>2`, `q^4 | D`, and `D | 4XY^2`. Choosing `D=XY` shares three arithmetic gates; choosing `D=q^4` reduces degree further. A bounded-index argument first extracts the q^4 congruence and only afterward recovers the whole denominator.

## Exact specification

For a direct endpoint, `equation.json` lists every variable and every quadratic residual. A term `[c,[i,j,...]]` means `c*x_i*x_j*...`; repeated indices denote powers and `[]` denotes the constant monomial. The single polynomial is the **sum of all residual squares**. The adjacent `expanded_polynomial.json` lists every collected coefficient. `residuals.txt`, `residuals.tex`, and `variables.tsv` are exact readable exports.

Each compact JSON file is the complete arithmetic circuit, using only fixed integer leaves, ten variable leaves, addition, subtraction, and multiplication. Intermediate registers are polynomial abbreviations, not quantified variables. The coefficient recipe's loops, floors, and decoding operations define fixed integers only. There is no factorial, variable exponentiation, binomial primitive, unnamed universal polynomial, or coefficient oracle in the final equations.

The direct evaluator accepts an explicitly supplied integer tuple; it does not search for roots:

```sh
python3 direct/evaluate.py --help
```

## Reproduce offline

Python 3.10 or later and its standard library are sufficient for the finite mathematical checks. No network, original repository, previous archive, CAS, Lean installation, or Turing-machine simulation is needed.

```sh
python3 -B verify.py --rebuild
python3 -B -O verify.py
```

The first command checks both quartic endpoints and all three compact equations, reconstructs their exact source changes and coefficient data, checks the printed appendices, and compares deterministic reconstructions byte for byte. The second runs the same mathematical checks with Python assertions disabled. Required checks use explicit exceptions.

These commands leave the delivered artifacts unchanged. To save a new receipt, use a path outside the sealed directory:

```sh
python3 -B verify.py --rebuild --receipt ../conzfc-replay.json
```

To check only the release hashes:

```sh
python3 -B verify.py --manifest-only
```

The direct component has two separately authored exact checkers; one replays the principal's 216 monic integer restorations without importing the producer or its polynomial implementation. They check all four group memberships, private witness namespaces, translations, and every quartic coefficient. The compact checks cover all circuit gates, exact leading forms, all four reconstructed coefficient integers, and deliberately corrupted controls. The complete source identities and actual verification receipts are included.

Rebuild the report with a standard pdfLaTeX installation:

```sh
python3 -B build_report.py --output ../rebuilt-report.pdf
```

The builder runs three passes in a temporary directory and checks references and overfull boxes. TeX metadata and font versions may change PDF bytes without changing the mathematics. The supplied PDF was separately rendered and visually inspected.

## Proof and evidence boundary

The new lemmas are unbounded ordinary proofs, not inferences from finite examples. The original numerical C222-to-ZF and ZF-to-ZFC refutation theorems, and the compact native specialization, are inherited and explicitly named. Relevant ordinary proof sources, formal interface source files, exact numerical inputs, licenses, and immutable source identities are retained.

This packet does **not** prove Con(ZFC), provide a contradictory ZFC proof, claim a global minimum, establish worldwide priority, or claim a newly compiled end-to-end Lean/Rocq or encoded object-ZFC derivation. The finite checks certify the literal artifacts and transformations; they do not replace the unbounded proof or rebuild the older formal development's entire transitive closure. Independent review here means separate mathematical and implementation work within this AI-assisted workflow, not outside human refereeing.

## Comparison and integration

The comparison snapshot is ProveIt commit `e0c98c629bf10d30b695884f6b1d2ab361bdf513`. All six incoming ZIPs at that commit were inspected, in addition to the consolidated collection. The main integer parent is from `ConZFC_Cofinal_Anchors_Height_One_Round17_2026-10-25.zip`; the compact parents are from `ConZFC_Certificate_Reductions_2026-10-25.zip`.

Keep this folder intact as a new research contribution; `INTEGRATION.md` gives a concise entry suitable for the collection. No existing repository files, branches, issues, or pull requests were changed.

`ENDPOINTS.json`, `PROVENANCE.json`, component source ledgers, inherited licenses, and `MANIFEST.json` record the boundary. The manifest covers every static delivered file and excludes itself and the two final assembled verification receipts to avoid self-reference. A manifest detects changed bytes; it is not a cryptographic signature or an independent proof of the theorem.
