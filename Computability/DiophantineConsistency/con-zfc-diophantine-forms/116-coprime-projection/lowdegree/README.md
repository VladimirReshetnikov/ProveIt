# Low-degree first-root carriers

Four complete fixed polynomials over unrestricted integers:

- `equation.json`: 15 variables, exact degree 56, 110 live operations.
- `fourteen/equation.json`: 14 variables, exact degree 108, 119 live operations.
- `thirteen/equation.json`: 13 variables, exact degree 274, 129 live operations.
- `twelve/equation.json`: 12 variables, exact degree 500, 148 live operations.

The 15-variable equation replaces the first/main Pell rows with one monic rational-root CRT carrier and substitutes out the native transport coordinate. The other three endpoints successively incorporate the strong root, auxiliary root, and a guard square into double-, triple-, and four-root norms. Monicity licenses the congruences before individual roots are extracted. Centering controls exact degree; the runtime uses shorter direct norm formulas.

Each variant's `PROOF.md` gives complete ordinary two-way integer-zero maps. Its `specification.json` provides readable ordered definitions, and its `equation.json` counts every binary arithmetic gate. The six complete fixed coefficients are under `coefficients/`. `source/` retains the immediately used normalized17 and signed projection statements; `DEPENDENCIES.md` identifies the full inherited compiler/refutation chain retained elsewhere in the release. No construction hides quantified registers, inequalities, free coefficient ports, or positive-domain variables.

Run the builders and independent checkers exactly as listed in `REPRODUCE_PLAN.json`, in normal and optimized Python. Builders use the standard library; independent review checks additionally require SymPy (see `requirements.txt`). Python optimization mode is explicitly tested; assertions are not relied upon. `METRICS.json` binds the four final equation hashes and counts. Earlier equivalent centered/Horner schedules are retained as comparison data, not additional claimed endpoints or active builders.

These are new ordinary arithmetic reductions. There is no claim to prove consistency, global minimality, a new encoded internal-ZFC proof, or a new end-to-end proof-assistant certification. The endpoints improve different portions of the size frontier; a lower degree is not always a lower gate count than every other existing endpoint.
