# Literal periodic U15 sandpile loader

This research bundle specifies one fixed stable periodic ordinary nearest-neighbour Z^3 sandpile and a finite nonnegative U15 tape loader. Every primitive, circuit edge and routing coordinate is determined explicitly. The complete dense background is enormous and has not been materialized.

## Main result

For the nearest-head-first binary tape pair `(ell,r)`, U15 halts iff the sandpile's least activation closure is finite, equivalently every fair maximal legal execution has finitely many total topplings. Every lattice site fires at most once; off-support vertices never fire. Global halting is therefore distinct here from the automatically finite number of firings at each individual site.

- Fixed background periods: `(1303671936, 744955392, 1955501604)`
- Primitives per macrocell: `3879975`
- Edges per macrocell: `5819945`
- Finite added chips: at most `len(ell)+len(r)+7`
- All-port gate semantics include backward output activations
- Infinite-support degree at most3 and off-support co-degree at most2, including all seams
- Halting afterT transitions has a proved active prism of fixed thickness and at most `5426111451172075939316367360 * (len(ell)+len(r)+T+1)^2` lattice sites

## Read first

1. `LOADER-PROOF.md`: precise theorem, composition, numerical bounds and limitations
2. `INDEPENDENT-AUDIT.md`: independent mathematical review, scope and exact hashes
3. `VALIDATION.json`: normal and optimized execution receipts

Component proofs are in `gates/GATE-PROOF.md`, `geometry/periodic_router_proof.md`, and `ca/SEMANTICS_AND_BOUNDS.md`.

## Executable interfaces

Run all checks with Python3, standard library only:

    python verify_bundle.py

This is a research replay runner: it regenerates receipt JSON files in place, runs every authored verifier under normal and optimized Python, compares their byte-identical receipts and rejects optimization-disabled assertions. It is not an immutable package-integrity gate. FROZEN-INPUTS.json records expected code, data, proof and receipt hashes; a user-release wrapper must replay an external copy and compare against those frozen expectations without modifying the source package. Individual modules:

- `ca/lazy_u15.py`: literal finite 388146-rule generator and finite U15 initialization
- `geometry/periodic_router.py`: seven-segment routing formula and complete-period toy checks
- `compiler/literal_loader.py`: full gate/edge enumeration, explicit background-height evaluator and tape-pair loader
- `compiler/test_coefficients.py`: whole support/halo coefficient comparison, period shifts, initialization, quadratic bounds and eight tamper tests
- `compiler/make_example.py`: a concrete 43-chip input, checked75-step U15 halt, exact184-row CA extinction and literal seed coordinates

Use `Circuit()` once and pass that fixed circuit object to `background_height(point,circuit)`, `tape_pair_loader(ell,r,circuit)`, or `load_binary_input(word,circuit)`. The binary grammar is `1^len(ell) 0 ell r`; malformed grammar is explicitly rejected. `background_height` is a bounded coefficient algorithm, not an assumed oracle: at most two scans of the explicitly generated fixed edge set plus finite modular segment tests. It is intended for the fixed U15 circuit, not a generic arbitrary-kinds circuit API.

## Verification boundary

The enormous universal dense table and full universal sandpile were not simulated. General coordinate, confinement and composition proofs establish their properties. Executable checks independently cover all primitive port subsets, all CA rules, bounded TM/CA traces, entire smaller periodic router tori, every edge incidence in the full universal cell, exact coefficient lookups on a full small torus and its halo, and a concrete literal initializer.

The arbitrary-program-to-U15-pair encoder remains the published Neary–Woods mathematical dependency, as in Report32. This bundle materializes the finite pair-to-sandpile map. It does not claim a new universality theorem, practical layout, fixed-arity Diophantine equation or new general odometer theorem. Coefficient-level certificate composition is a separate subsequent step retaining the full exterior halo.

All executable code here is newly authored. The bundled `data/u15_table.json` is pure data, pinned by SHA256. No upstream implementation is executed. No repository edits or external publication were performed.
