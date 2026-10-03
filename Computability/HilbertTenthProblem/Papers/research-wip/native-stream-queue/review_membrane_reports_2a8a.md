# Independent review of the two membrane research packages

Review date: 2026-10-02. Scope: the Universal Membrane and Membrane Motif packages imported in `2a8a39599`. The independent reviewer worked in private copies; root subsequently published the review artifacts. The incoming archives remain unchanged. No corrective patch is proposed: I found no theorem-level defect or false certificate within the stated well-formed-input and natural-witness contracts.

## Provenance and reproduction

Archive SHA-256 values:

- `Universal_Membrane_Research_Package.zip`: `dc4fe8f07c278614d567029e40bbdf2db2326e5ea4b04f423bcc3b0b2610e3b5`.
- `Membrane_Motif_Research_Package.zip`: `47da14f271cccfb16fceb5cec859889a02d14e6ff5c23ca121f6f17a1ac98e99`.

The complete normalized member inventory is [review_membrane_inventory_2a8a.json](review_membrane_inventory_2a8a.json), with no machine-specific extraction paths. It records every member's archive-relative path, size and SHA-256 value.

The portable independent checker is [review_membrane_reports_2a8a.py](review_membrane_reports_2a8a.py), with the complete saved result in [review_membrane_reports_2a8a.json](review_membrane_reports_2a8a.json). It embeds hashes of the reviewed proof sources, Python sources and numerical inputs that it reads. Its `run(universal_root, motif_root, *, authors=False)` function accepts extracted release directories. Its direct full-reproduction command is:

```sh
python review_membrane_reports_2a8a.py UNIVERSAL_RELEASE_ROOT MOTIF_RELEASE_ROOT --authors --output receipt.json
```

For a clean archive-to-receipt replay, use the sibling [replay_membrane_2a8a39599.py](replay_membrane_2a8a39599.py):

```sh
python replay_membrane_2a8a39599.py --repo /path/to/Proofs
```

When placed in the repository, the wrapper also discovers the repository automatically. `--helper`, `--receipt` and `--inventory` can override the default sibling artifact paths. The wrapper authenticates those three artifacts, authenticates both archive hashes, rejects traversal paths, duplicate members and special files, extracts into separate temporary directories, and compares the complete normalized member inventory. If the incoming ZIPs have been retired from the worktree, it reads their bytes from the pinned arrival commit with read-only `git show`. It then invokes the independent checker with `--authors` and compares the entire fresh JSON receipt with the saved receipt, using a canonical serialization that distinguishes integers from numerically equal floats or Booleans. It does not discard any saved mathematical or test result.

Assertions are required and `-O` is explicitly rejected by both checker and wrapper. Each original author replay runs in a fresh private copy with a 300-second timeout; the archive wrapper allows 900 seconds for the complete independent review and both author replays. The universal author's wrapper verifies both manifests and checks every listed regenerated file byte-for-byte. The motif wrapper regenerates all five suites; the independent checker additionally compares all eight deterministic JSON products byte-for-byte. Its timestamp/platform/timing receipt is not treated as semantic output. There are 18 original author suite commands and two additional loader checks; both complete archives contain 100 authenticated members. The saved wrapper result is [replay_membrane_2a8a39599.json](replay_membrane_2a8a39599.json).

## Exact read and primary-source scope

I read both complete TeX articles, both Universal `PROOF.md` files, their READMEs, the copied Waterfall frontend proof, all Universal Python modules and checkers, and every Motif Python module/checker together with its README and release notes. The full literal tables and exports were checked by the replay and structural/manual arithmetic checks; I did not manually read each line of the 34,605-rule JSONL table or every large generated JSON file. These are research proof reviews and finite executable checks, not proof-assistant formalizations.

The [2006 Alhazov–Freund–Riscos-Núñez institutional primary PDF](https://idus.us.es/bitstreams/dcac15aa-404e-4102-88e2-08ec23b7df8a/download) was independently retrieved: 208,921 bytes, SHA-256 `d667c140b3dc0b1e49b5c286b1ff6a97b348e875f08a681c8b4ff343b51c57a5`, matching the report. Its Theorem 4.1 is a two-register generator with zero initial register values, not the new arbitrary-input acceptor. Its displayed output alternative and missing punctuation are indeed present, and the report openly specifies its repairs and skin/delay role split. The new input and three-register simulation proofs are therefore necessary and are supplied.

[Gazdag–Hajagos–Iván, §2](https://link.springer.com/article/10.1007/s41965-021-00082-2) explicitly gives allocation to old object occurrences, one structural rule per membrane, inclusion maximality, and bottom-up application that copies an already updated subtree. These match the motif article's semantics. [Murphy–Woods, Definition 3 and Theorem 3](https://www.niallmurphy.me/papers/MW2007p.pdf) use parent-local elementary equivalence classes and prove the existence of a suitably compressed path for their restricted confluent symmetric-division model. The report correctly avoids transferring that theorem to arbitrary asymmetric weak-division schedules. The fixed U15 table and two-half-tape convention agree with the previously audited [Neary–Woods Table 16](https://dna.hamilton.ie/assets/dw/NearyWoods-FI09.pdf); this review rechecked the report's exact serialization and simulation, rather than claiming a new independent proof of the original universality theorem.

## Universal frontend: mathematical assessment

The direct 528-instruction program implements each binary-tape transition by pair removal, quotient restoration, doubling the other half tape, and optionally writing one. Its loop ranks decrease on arbitrary natural values. A TM cut requires scratch zero in addition to the control label. The three-register proof is complete, including the initial scratch-clear instruction and the unique J1 halt.

The membrane proof treats all maximal runs, rather than choosing a convenient nondeterministic branch and assuming soundness. Every accepting run must avoid the persistent `#` trap. The spare counter membrane and occupied delay force the SUB zero/positive choice; simultaneous actions use different child boundaries and old objects. A positive SUB leaves a harmless pending `t`, so a generic final positive SUB would need cleanup. Both generated frontends reach HALT through a clean exit. Global quiescence, not merely seeing a HALT object, is the acceptance predicate.

The prime frontend's factorization is a mathematical invariant, not a machine primitive. For every positive raw input, a coprime-to-30 cofactor is preserved and the 5-adic scratch is cleared. Literal constant-prime multiplication/divisibility macros implement the virtual machine and terminate. The external map from two half tapes to `2^L 3^R` and the input-dependent expanded membrane population are explicitly charged; a compact tree descriptor does not make population or loading free.

The quadratic argument is sound over the entire nonnegative orthant. Every inactive penalty is `(sum of other selectors)*(own selector + sum of retained bases)`, whose factors are independently nonnegative before any equation is used. Combined with selector sum one, these penalties force one-hot selectors even over nonnegative reals, and force all inactive bases to zero. Active ADD and positive SUB bases are the old counter or old counter minus one; zero SUB omits its tested base. Natural initial data therefore force every active base to be natural. Determinism gives an empty or singleton full witness fiber, and the absence of outgoing HALT branches makes the represented time the first halt. This is an outcome projection justified by the separate simulation; it does not certify an arbitrary submitted membrane history.

Exact ledgers at external literal-counter horizon `T`:

| Interface | Program and membrane resources | Natural witnesses | Affine squares | Nonnegative products |
|---|---|---:|---:|---:|
| Direct half tapes | 528 instructions; 2,544 rules; 1,296 symbols; 5 labels | 2,811 T | 5 T + 1 | 761 T |
| Prime raw input | 8,408 instructions; 34,605 rules; 19,162 symbols; 4 labels | 29,904 T | 4 T + 1 | 10,748 T |

Both polynomials have degree at most two. The direct input `L=6,R=0` genuinely has 328 counter instructions and 1,013 membrane steps, with all 922,008 formal coordinates retained despite sparse storage of 922 nonzero values. The full 1,641 squares and 249,608 products are evaluated. The corresponding prime example's 738,579,314,485,258,247 instructions are derived from proved macro counts, not enumerated. Both descriptions are accurate.

The density argument also survives review: disjoint valuation cylinders have computable geometric tails; their positive weights let an oracle for the limiting density decide membership in the complete c.e. set, while a halting oracle computes the density. This gives degree 0′ and transcendence. The effective counting remainder concerns a noncomputable counting function. It is correctly distinguished from the computable bounded-time counting sequence, whose noncomputable limit admits no computable sublinear error envelope. The short-prefix description uses noncomputably chosen finite advice and does not yield an effective convergence modulus.

## Motif certificate: mathematical assessment

The source projection is per parent and per supported child type. Together with positive supported multiplicities, it permits source-identical children to choose different decorated schedules without exchanging objects between unrelated parents. Natural resource residuals allocate only old payload. Upward output and promoted forest are computed bottom-up; a dividing parent then copies the updated descendants. The separate elementary restriction uses old child support, so simultaneous child dissolution cannot make an originally non-elementary parent eligible for an elementary rule.

Maximality is encoded by zeroing the union of residual object types that could enable an additional rule: any evolution, a local structural rule when the current boundary is idle, or a send-in to an idle child. A nonempty supported child class always contains an actual child because its multiplicity is `1+m`. Naturality makes a sum-zero row equivalent to every required residual being zero. This proves inclusion maximality of the old allocation; it does not confuse maximum cardinality with maximality.

Soundness holds for every well-formed indexed schema. Completeness is existential in the schema and needs consistent target indexing; duplicate preassigned catalogue indices can block an otherwise legal step. Only derived `U,Y,O,F` coordinates are unique after fixing the numerical source and decorated schedule. The report states these distinctions explicitly and includes counterexamples to stronger claims.

The dense compiler ledger is exactly

`V = dK + A + E + B + 3dJ + KJ`,

`R = (3d + 2K)J + (d + K)L + Z`.

All scalar residuals have degree at most two, so the sum of squares has degree at most four. The contextual exported quartic has 282 monomials and height 19. The 18-variable, 30-residual clone-doubling schema handles every positive multiplicity, including the supplied 10,001-bit population. The nested-chain formula and exact surviving-root population identity correctly count copies from every dividing ancestor. The four-rule base-4 example proves failure of identical-subtree sharing alone; it is not a lower bound for all possible encodings.

## API and domain boundaries

The generic motif compiler expressly requires a well-formed finite acyclic schema. Its low-level sparse polynomial evaluator is arithmetic over supplied assignments; it is not advertised as a natural-domain or hostile-JSON validation boundary. The replay wrappers check natural witnesses. The universal compiler similarly takes a valid literal program/table, while its public evaluators explicitly reject negative, Boolean and fractional supplied natural coordinates and invalid horizon values. There is no claim that arbitrary mutated packet dictionaries are authenticated canonical objects. I did not interpret these documented scope limits as theorem defects or introduce unrelated constructor hardening.

Any maintained public extension should preserve those preconditions or add complete validation before advertising a stronger API contract. The present review found no supported-input false certificate requiring a patch.

## Independent evidence and limits

The adjacent JSON receipt gives exact executed counts. Independent checks exhaust small one-counter first-halt fibers, include rational mixed selectors, evaluate both actual complete universal source formulas at signed and natural off-zero assignments, reconstruct all seven saved motif residual systems numerically from the displayed mathematics, verify complete ledgers and coefficient bounds, and mutate every derived coordinate in those examples. A separate flat-tree oracle enumerates old resources, idle/busy slots, maximality and structural outputs for two children, with optional evolution at parent and children. It does not call the author's legality or update routine to derive its expected result.

All author suites also pass in private copies. Their larger finite suites are corroboration and do not substitute for the unbounded proofs read above. The independent off-zero arithmetic checks are finite complete evaluations, not a claim of symbolic polynomial identity established by sampling.

## Transfer toward a low-operation universal equation

The strongest reusable technique is parametrizing the legal domain of each branch directly, then using globally nonnegative inactive-branch penalties. This avoids separate Boolean and counter-guard variables while retaining degree two and even nonnegative-real discreteness. It is compatible with exact shared affine arithmetic, but the paper supplies no complete fixed-arity unbounded-time interface or paid straight-line operation ledger. The current witness counts grow with external `T`, and the motif catalogue and decorated schedule remain external finite data. Neither package establishes a 75/87-operation improvement.

A precise bounded-time simplification is available without a new theorem: the direct frontend's first instruction always zero-tests its initially zero scratch. Substitute its forced selector, zero inactive bases, and active bases `L,R`; all first-step squares and products vanish identically. The remaining system starts at A0 with the same half tapes. This removes 2,811 coordinates, five squares and 761 products at every horizon `T>=1`, giving `2,811(T−1)` coordinates, `5(T−1)+1` squares and `761(T−1)` products. The terminal row remains, so `T=1` still has no accepting zero. This is an affine graph projection of a bounded family, not a claimed universal arithmetic-record reduction, and no production implementation was added during this review.

For the broader goal, the meaningful remaining obligation is a paid fixed-size representation of unbounded time and of the variable catalogue/schedule. Spatial repetition alone does not supply it. Converting natural witnesses to the positive-witness convention of existing compilers also requires explicit shifted expressions and their arithmetic cost.

### Executed independent counts

```json
{
  "quadratic": {
    "domain_rejections": 16,
    "empty_or_singleton_fibers": 24,
    "exhaustive_natural_tuples": 122640,
    "full_actual_source_ledgers": 6,
    "full_actual_source_offzero_identities": 12,
    "nonnegative_rational_tuples": 750
  },
  "motif": {
    "complete_residual_identities": 91,
    "derived_coordinate_mutations_rejected": 502,
    "independent_concrete_updates": 1060,
    "independent_old_resource_and_maximality_cases": 10125,
    "scalar_residuals_compared": 19123,
    "schema_ledgers_and_heights": 7
  }
}
```
