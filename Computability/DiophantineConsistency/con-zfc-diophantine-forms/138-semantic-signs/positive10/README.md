# Three shorter ten-positive consistency equations

The complete ordinary proof is `PROOF.md`. The literal arithmetic circuits
are `equation_83_436.json`, `equation_81_560.json`, and
`equation_80_750.json`; filenames give paid binary operations and exact total
degree. Each equation has exactly ten strictly positive integer unknowns.
Every other register is a polynomial abbreviation. All four fixed integer
coefficients are included in `coefficients/` with their full payloads and
hashes; the complete finite printed recipe is
`inherited/indexed_constant_recipe.tex`.

The 83/436 equation removes a redundant auxiliary shift from package 133's
84/436 equation at unchanged degree. The 80/750 and 81/560 equations also
use a normalized q-cube carrier and absorbed padding; the lower arithmetic
cost trades against larger degree. They encode the whole indexed BFS943
native instance, hence retain its K215/refutation calibration. These are
separate from direct C222 quartics and are not global optimum claims.

## Check or reconstruct

```sh
python3 -B verify.py
python3 -B -O verify.py
python3 -B build.py --check
```

Only Python's standard library is needed; no network or optional packages
are used. `verify.py --output /absolute/path/receipt.json` writes a receipt.
`build.py` without `--check` regenerates the equation JSONs and `CUTS.json`
from the retained parent circuits. The checker separately verifies exact
free polynomial identities, whole coefficient hashes, complete literal
formulas, all graph references and liveness, global degree upper bounds,
complete univariate leading-coefficient certificates, planted gate
corruptions, and deterministic rebuilds.

The new arithmetic proof is ordinary mathematics formalizable in ZFC and
composes with the explicitly identified inherited source calibration.
Finite algebra and artifact checks are not a proof of the unbounded Pell
theorems or of consistency. No new end-to-end Lean/Rocq or encoded internal
ZFC proof object is supplied. `SOURCE_LEDGER.json` identifies the selected
inherited proof closure and the current comparison snapshot.

New research, code, and exposition were prepared with AI assistance.
Independent review refers to separately performed mathematical checking in
this workflow, not outside human refereeing. No repository branch, issue,
or pull request was changed.

New material is supplied under the MIT No Attribution terms in `LICENSE`.
Inherited material retains its notices and exact provenance.
