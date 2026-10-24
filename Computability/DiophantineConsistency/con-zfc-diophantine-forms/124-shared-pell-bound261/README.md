# One Pell bound and one error congruence

## Explicit Diophantine consistency equations for ProveIt

Prepared for Vladimir Reshetnikov, 24 October 2026. AI-assisted mathematical
research, ordinary proofs, literal polynomial data, and exact finite verification.

**Main result:** a fixed quartic polynomial `P` in **261 nonnegative integer
variables**, explicitly given by the sum of squares of **194 quadratic
residuals**, for which ordinary mathematics formalizable in ZFC proves

> `P` has no solution in `N^261` if and only if `Con(ZFC)`.

Here `N = {0,1,2,...}`. This does not assert either the consistency or the
inconsistency of ZFC. The new construction uses the numerical proof calculus
`C222`, together with inherited arithmetic and logical calibration results.
It does not simulate K215 or instantiate Jones's universal polynomial.

### What to read first

- `report/report.pdf`: the mathematical report, including **every one of the
  194 literal residuals** in its appendix.
- `report/report.tex`, `report/metrics.tex`, `report/residuals.tex`: complete
  editable LaTeX source.
- `portable/equations/primary/equation.txt`: plain-text principal equation.
- `portable/equations/primary/natural/equation.json`: authoritative ordered
  variables and residuals; `expanded_polynomial.json` in the same directory
  contains every collected coefficient of the single quartic.
- `portable/equations/sparse/`: the second, sparser quartic and its certificates.
- `proofs/SELF_RADIX_PROOF.md` and `portable/CAP_THEOREM.md`: additional detailed
  proofs of the two new arithmetic reductions.

## Comparison and meaning of “simpler”

| Equation over nonnegative integers | Variables | Quadratic residuals | Degree | Expanded monomials | Maximum absolute coefficient |
|---|---:|---:|---:|---:|---:|
| Incoming Round14 direct baseline | 349 | 268 | 4 | 12,768 | 86,915,503 |
| New principal equation | **261** | **194** | 4 | 31,679 | 85,566,955 |
| New sparse companion | **292** | **225** | 4 | **6,140** | **83,933,334** |

The principal equation saves **88 variables (25.2%)** and 74 residuals, at the
cost of denser expanded support. The sparse equation saves 57 variables and
51.9% of the expanded monomials, and also has smaller coefficient height.
Coefficient height refers to the fully collected single polynomial, rather
than the smaller coefficients of its quadratic residuals.

The comparison is to the latest inspected **direct natural quartic**, not to
an obsolete opening summary in the repository. The snapshot also has
much lower-variable constructions with other degree/coefficient tradeoffs,
including nine positive variables and a specialized 37-integer quartic.
No global minimum, variables-only record, or worldwide priority is claimed.

## The main new arithmetic theorem

Let `(X_j(A),Y_j(A))` be the natural Pell sequence for
`X^2-(A^2-1)Y^2=1`. The old global frame already forces
`A >= (W+1)^W`, and every requested positive seed index `k_i` is below `W`.

Keep one complete indexed-Pell certificate for `V=Y_W(A)`. Keep only the
principal norm for each other seed pair, and add two shared equations:

```
V = W + 1 + sum_i Y_i + s
sum_i (Y_i-k_i)^2 = (A-1)Q
```

All witnesses are natural. Pell classification writes `Y_i=Y_(j_i)(A)`;
the first equation gives `0 <= j_i < W`. The congruence
`Y_j(A) = j (mod A-1)` makes `A-1` divide `sum_i(j_i-k_i)^2`.
There are at most `W-2` seeds, so that nonnegative sum is smaller than
`W^3 < A-1`. Every squared error is therefore zero. This checks all
seed indices simultaneously. The large Pell ordinates are not assumed
to be small residues; the bound applies to their decoded indices.

The report proves constructive completeness and checks the full remaining
anchor conditions. It also proves that the frame, indices, and powers
can be interpreted in that order, before factorial and CRT semantics,
avoiding a circular argument about proposed power outputs.

The principal version additionally selects the digit radix after choosing
the nine CRT representatives. With their sum `S`, it uses
`q = N (V_0+1+S)^K`, removes their former aggregate upper bound, and
proves that amplification `K=R` suffices at horizon `t>=12`.
The sparse companion retains the old radix and separate bounded residue
tests, with horizon `t>=16`.

## Verification and reconstruction

Python **3.10 or later**, standard library only; no network or repository
checkout is required. From this directory:

```sh
python3 -B verify_release.py
python3 -B -O verify_release.py
python3 -B verify_release.py --rebuild
```

The first two commands verify the release manifest, source hashes, full
anchor and cap bindings, radix bounds, all affine restorations, all
natural-domain contraction certificates, and every expanded coefficient.
They also check deliberately corrupted arithmetic data are rejected.
`--rebuild` additionally reconstructs both equations and requires exact
equality with all four frozen compiler outputs for each endpoint. Temporary
rebuild directories are removed after verification.

For persistent rebuild outputs:

```sh
python3 -B portable/build.py --variant primary --output rebuilt/primary
python3 -B portable/build.py --variant sparse --output rebuilt/sparse
```

To regenerate the report inputs and compile its PDF:

```sh
python3 -B code/generate_report_inputs.py
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The report uses ordinary TeX Live packages: `lmodern`, `amsmath`, `amssymb`,
`amsthm`, `mathtools`, `geometry`, `booktabs`, `longtable`, `array`,
`microtype`, `enumitem`, `xcolor`, `fancyhdr`, `hyperref`, and `listings`.
Recompilation can change PDF bytes and therefore the original release hash;
the manifest deliberately records the shipped bytes.

### What the independent checks establish

1. Exact new semantic row checks bind the cap, pooled congruence, 16 seeds,
   one derived index, and 19 positive-power requests to the exported graph.
2. Independent affine-export replay restores **466** natural coordinates
   from the 406-coordinate raw system to its 872-coordinate semantic graph.
3. Independent contraction checking restores the next **145** coordinates
   from the principal 261-variable equation, including two restorations
   whose nonnegativity is proved by rational square certificates.
4. Independent polynomial arithmetic compares all **31,679** collected
   coefficients for the principal equation and all **6,140** for the sparse
   equation. Both have exact degree four, and every declared variable occurs.
5. Arithmetic controls supplement the unbounded proofs: 780 Pell/index
   checks and 366,601 radix/binomial checks. Nine deliberate semantic
   corruptions are rejected across the three new audit scripts.

Recorded receipts are under `verification/`. The finite checks do not
prove the inherited logic or the unbounded arithmetic theorems by testing
examples; these are supplied by the written arguments and named dependencies.

## An unrestricted-integer companion

`equations/integer/recipe.json` literally substitutes
`z_i = u_i^2 + v_i^2 + w_i(w_i+1)` into the principal equation. It defines
an ordinary polynomial of exact degree eight in **783 unrestricted
integer variables**. The substitution is nonnegative and surjective onto
the natural numbers, by Legendre's three-square theorem. Thus it has the
same consistency equivalence. This companion is provided for completeness
of the domain specification, not as an improvement on specialized integer
constructions. No huge symbolic expansion is necessary to specify it.

`code/evaluate_equation.py EQUATION_JSON POINT_JSON` evaluates either a
natural residual equation or this companion at an explicitly supplied
JSON array of integer coordinates, using exact integer arithmetic. This
is evaluation at a given point, not a procedure for deciding solvability.

## Logical scope and provenance

The two inherited interfaces used are
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. The first is about
the numerical calculus itself and has no machine, boot, or coverage
hypothesis. The retained full indexed-Pell criterion is
`DiophantineConsistency.PellRepresentation.criterion_iff_pell`.

These are dependencies of the mathematical proof. This release does not
provide a newly completed end-to-end Lean/Rocq verification, an exported
object-language ZFC proof, a fresh audit of every imported logical theorem,
or a proof of `Con(ZFC)`. The ordinary argument is formalizable in ZFC and
is intended as a concrete, reviewable mathematical and computational
contribution, with precise interfaces for subsequent formalization.

The inspected ProveIt commit is
`45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6` (24 October 2026).
`provenance/SNAPSHOT.json` records the baseline and its archive hash.
The unchanged Round14 archive is included so the inherited source and
proof history remain available. `portable/SOURCE_MAP.json` records the
minimal local compiler dependency closure and all local routing edits.
Exact retained logical-interface files and their scope are described
in `provenance/logical_interfaces/README.md`.

The main PDF includes the entire new proof and literal principal equation.
`MANIFEST.json` records hashes of all delivery files other than itself.
No files in the original repository have been modified or pushed.

## License and authorship

New material is supplied under ProveIt's MIT No Attribution license,
reproduced in `LICENSE`. Original imported files retain their notices and
provenance. The preserved baseline archive is unchanged. New mathematics,
code, and exposition were developed with AI assistance; no human review
or institutional endorsement is implied.
