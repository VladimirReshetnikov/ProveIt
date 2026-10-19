# Complete AX row permutations: proof and portable checks

This packet proves that permuting the eight complete logical AX rows, and
independently permuting their schema parameters in the stated safe ways,
preserves the original abstract proof enumerator's refutation behavior.
It contains no claim of a machine with fewer than 246 states.

Read `axiom_row_permutation.md` for the command contracts, selection lemma,
complete derivation compiler, soundness and completeness proof, and the
single-read twelve-way symmetry of rho8. `ordinary_proof_review.md` explains
the precise internal-ZFC conclusion and the remaining source/binary and
theory-calibration interfaces. `prior_art_audit.md` records source provenance
and proof-status distinctions.

## Run

Python 3.10 or newer and its standard library are sufficient. No compiler,
proof assistant, network access, or separately checked-out repository is
needed. Do not use Python's `-O` flag, because one checker uses assertions.

From this directory:

```sh
python3 -B check_axiom_row_permutation.py
python3 -B check_full_row_emission.py
```

The first command independently checks the symbolic DROP/NIP/MP contracts,
all 40,320 orders of the eight logical rows, all ten selected positions,
the cleanup/generalization/modus-ponens blocks, and the final halt suffix.
The second checks all 40,320 orders with the pinned recovered formula
emitter and its separate symbolic evaluator, and all twelve single-read
rho8 role maps. Each command writes its corresponding JSON result beside
the script. Neither checker uses probabilistic fingerprints.

To use a local ProveIt checkout with byte-identical pinned source files:

```sh
python3 -B check_full_row_emission.py --repo /absolute/path/to/ProveIt
```

For a quick portability and identity check, without repeating the exhaustive
order loop:

```sh
python3 -B check_full_row_emission.py --preflight-only
```

That mode checks the unchanged original order and all twelve role maps,
then writes `portable_preflight.json`. It does not overwrite the archived
exhaustive result. An optional `--output /path/to/result.json` works in both
emitter-checker modes.

## What was checked in this session

The archived exact stack checker passed 403,200 selection contracts and
40,320 sets of compiler-wrapper checks, plus 1,100 general-position cases.
The archived formula-emission checker passed all 40,320 row orders and
twelve safe rho8 role maps. These are independent, finite symbolic checks
of the stated interfaces; they are not exhaustive tests of all numeric
formula codes or a literal Turing machine.

For portability, only the source-loading code and command driver were
adapted. The two source files are unchanged pinned copies. The mathematical
loop bodies and helper functions are unchanged Python abstract syntax;
`portable_adaptation.json` records the exact comparison. After adaptation,
the quick check was run with both the vendored files and the repository
files. The previously completed exhaustive checks were not repeated solely
to validate the different file-loading path.

## Small source dependency boundary

`vendor_loader.py` checks both source hashes against `vendor/manifest.json`,
then compiles only twelve exact pure definitions and two literal constants
selected from the unchanged research source's Python syntax tree. This avoids
importing unrelated compiler experiments. The original `published_spec`
function similarly selects pure formula constructors from the pinned
upstream specification. The specification's numeric runner and its
`bignum` fingerprint facility are not imported or executed.

See `vendor/README.md` for authorship, pins, and the upstream license boundary.
The nominal family of 135,444,234,240 syntactic choices is a theorem-supported
search space, not an exhausted search or a binary state-count result.
