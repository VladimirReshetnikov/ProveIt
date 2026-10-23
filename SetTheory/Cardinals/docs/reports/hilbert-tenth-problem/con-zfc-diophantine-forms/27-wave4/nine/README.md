# Improved nine-variable consistency equations

Pinned sources: VladimirReshetnikov/ProveIt@ae3007ca4467011e0e051c84acb4a1dd13971b0e, package18-jones9. SOURCE_PINS.json gives an exact commit-pinned URL, Git blob SHA, SHA-256 and byte count for every imported source. All copied Git blob hashes were checked locally.

## Results

All entries use nine unknowns and one equation. The main new equation is generated/nine_natural-majorant_specialized_dag.json over nonnegative integers. Its positive-integer counterpart ends in _positive_dag.json.

- Same paper18 polynomial: 1485 binary operations over N, or 1480 over positive integers; degree 161844*5^33+484 = 18841121345758438110351562984.
- Sharper natural-domain majorants: 1542 operations over N, or 1537 over positive integers; degree 120764*5^33+368 = 14058779925107955932617187868.
- Keeping literal Jones weights: 1478 operations over N, or 1473 over positive integers; original larger degree 291404*5^33+860.

Without folding known coefficient-recipe equalities, the corresponding natural-domain counts are 1616, 1673 and 1609; the positive counts are 1611, 1668 and 1604. The old package18 main circuit used20531operations. No global minimum is claimed.

IMPROVEMENT_PROOF.md supplies the division-free coding identities, bar-majorant induction, two-radical finalizer proof, exact degree argument, domain limitations and imported-theorem boundary. generated/ledger.json is the full twelve-variant count/degree ledger. These arithmetic DAGs contain no hidden existential registers: only their nine variable leaves are unknowns.

## Reproduce

Python3.10+; standard library only. From this directory:

    python3 build_improved.py
    python3 verify_improved.py
    python3 verify_fixed_binding.py

The last command uses the sibling ../coefficients directory containing the complete mixed-radix943tuple. Alternatively:

    python3 verify_fixed_binding.py --coefficient-directory /path/to/coefficients

All commands also work by absolute script path from an unrelated working directory. Use integer-preserving JSON parsing: degrees and exponent fields exceed IEEE754 exact integer range.

The checks include the exact full nu=32 digit polynomial with66045baseline positions and346independent correction symbols; the same exact identity after coefficient folding; all346alias identities; regeneration of the346weighted coefficients from the pinned positive quartic; exact majorant/norm identities;160old/new modular DAG comparisons;180positive-shift comparisons;1000bar-majorant assignments;972constructed finalizer witnesses; and exact symbolic-leading degree ledgers. Actual new-tuple binding is separately checked at three primes with48old/new output comparisons and36specialized/generic comparisons. None is a test of solvability or consistency.

## Full fixed-instance definition

The canonical ordered four-port interface is [beta,K0,MC,MF]. For the sibling mixed-radix compiler:

- beta = expanded/beta.bin.
- K0 = expanded/K.bin.
- MC = expanded/MC.bin.
- MF = expanded/MF_source.bin, already shifted by B-1. Do not shift again.

These are unsigned little-endian files containing four fully materialized integers. Their hashes and bit lengths are recorded in generated/FIXED_BINDING_VALIDATION.json. Use only the complete tuple, never mixed ports. Its universal compiler-correctness proof is a separate imported dependency from the sibling coefficients package; the residue test alone does not establish it.

The larger Jones constants are exact finite recipes, not expanded integers:

1. source/base/quartic32.upstream.json specifies 23 quadratic residuals in32positive variables and the four fixed ports.
2. Shift every positive variable by1 and take the sum of residual squares. source/base/normalized_quartic32.json is the pinned normalized coefficient presentation.
3. source/nine/generated/constants.json specifies all346nonzero factorial-weighted coefficient polynomials c_alpha in those four ports, with their exponent vectors. All omitted c_alpha are0.
4. source/nine/generated/index_bound_s.json specifies the20-term nonnegative integer polynomial s=2+24*sum(rho_j^2).
5. z_index=2^s, and y_index=sum_{|alpha|<=4}(z_index+c_alpha)*(2*z_index)^(5^33-expo(alpha)), including every one of66045digit positions. The unused index component u is also specified in constants.json.
6. A generic DAG uses these346c_alpha leaves plusz,y. A recipe-folded DAG uses64distinct nonliteral coefficient leaves plusz,y, with the exact aliases in generated/COEFFICIENT_ALIASES.json. No named coefficient is an unknown.

Thus materializing the four base ports does not materialize z,y or the full polynomial coefficients. Their bounded recipes completely determine them without running K215 or searching for a refutation.

## Proof status and licensing

The mathematical conclusion is a ZFC-provable equivalence between no solution in the stated domain and Con(ZFC), conditional on the same ordinary compiler/calibration theorems used in package18 and on the authentic complete compiler tuple. It is not a proof of Con(ZFC). The inspected formal source is Jones1982.Nine.wset_iff_nine at nu=32, with a quartic normalized at all-zero witnesses and an admissible index. The public nine_unknowns theorem's automatic nu=58 path is not used.

No new Lean or Rocq compilation was performed. New weight equivalence, natural-domain positivity and end-to-end binding are ordinary mathematical derivations, supported but not replaced by finite checks. Do not extend the nine-variable domain to unrestricted integers: n>=0 is essential in the margin argument.

Imported files retain the package18 license and notice at source/LICENSE and source/NOTICE.md. The earlier mathematical constructions and ProveIt formalization retain their attribution. No discovery-priority claim is made by this bundle.
