# Direct Con(ZFC) quartics in 233 unrestricted integers

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026, with AI assistance.

Each equation below is the ordinary polynomial `P=sum(Q_i^2)` given by its complete literal quadratic residual list. Its complete expanded coefficient list is included. All independent variables range over **unrestricted integers**.

| Equation | Variables | Residuals | Degree | Monomials | Coefficient height |
|---|---:|---:|---:|---:|---:|
| P233_balanced | 233 | 169 | 4 | 18,482 | 5,632 |
| P233_sparse | 233 | 169 | 4 | 10,182 | 8,880 |
| P234_sparse | 234 | 170 | 4 | 5,018 | 8,880 |

`PROOF.md` proves the new arithmetic composition and explains the inherited C222/ZF/ZFC calibration. It gives the ordinary theorem, formalizable in ZFC, that integer solvability is equivalent to a finite syntactic ZFC refutation. Negation gives the requested consistency equivalence.

The new composition changes a self-power source from radius F^2 to F at F=t^t, with even t>=16, and replaces its odd-square radix by a radix congruent to1 modulo4. The elementary bound lcm(1,...,t)<=4^t makes the smaller radius admissible. The signed bootstrap, exact low-tail recovery, self-power multiplicity proof and cofinal completeness are all checked in the correct order. Three common-radical projections, one affine projection, and reversible integer row operations complete the reduction.

## Comparison boundary

The inspected snapshot is commit `fb1bed5eb7196cf35abfaa746c18c6ee7eae6cfb`. Package159's principal has234 variables,171 rows,19,050 terms and height4,480. The new233-variable equations remove one variable and two rows; their coefficient heights are larger. Package165's actual power239 source has239 variables,175 rows,5,137 terms and height3,968. The new sparse234 companion has5 fewer variables and119 fewer terms, at greater height. These are explicitly stated tradeoffs, not a global simplest-equation claim. Other repository branches have far fewer variables with much larger coefficients and degrees.

## Offline verification

Python3.10 or later, standard library only:

    python3 -B verify.py
    python3 -B -O verify.py

An optional output argument saves a detailed receipt:

    python3 -B verify.py /tmp/direct233-receipt.json

The verifier reconstructs every new residual and every expanded coefficient from frozen certificates. It checks both original and edited245-to239 source charts, including76 invertible shears,47 row operations and6 prior monic projections. The new projection checks use an independently authored row-combination/directional-derivative method and test deliberate certificate corruptions. Normal and optimized Python checks both passed.

No search for a root is performed. Finite coefficient checks do not replace the unbounded proof. The supplied source papers and exact literal source are pinned in `PROVENANCE.json`. Some historical dependencies advertised by package165 are absent from the inspected Git tree, so a complete transitive inherited checker replay is expressly not claimed. The inherited calibration remains an ordinary mathematical dependency, not a new end-to-end Lean/Rocq result.

## Data format and evaluation

Each residual's term `[c,[i,j,...]]` is `c*x_i*x_j*...`; an empty index list is a constant. Coordinates are zero-based. `variables` is metadata in the residual file and an integer count in the expanded-polynomial file. The independent verifier checks that the sum of squares agrees with the entire expanded list.

To evaluate a supplied integer tuple stored as a JSON array:

    python3 evaluate.py equations/P233_sparse/equation.json tuple.json

All intermediate equations and certificates are retained under `stages/`, so the final coefficients are recoverable without an optimizer or network access. The packaged independent checker is the deterministic reconstruction algorithm. No variable exponent, factorial primitive or unspecified coefficient remains in a final equation.

To regenerate all three final residual lists, expansions and metric files in a fresh directory, with byte-for-byte comparison against the sealed artifacts:

    python3 -B rebuild.py /tmp/rebuilt-direct233

New composition and artifacts are AI-assisted work. Packages159,164 and165 are credited in the proof and source ledger; their retained checker files are unchanged. The repository's MIT No Attribution license is included.
