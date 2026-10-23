# Rocq audit at cbf94cb552a3b49509e0eee80e7455d4eb5974c6

## Recommendation

The highest-confidence remaining structural improvement is to give Rocq the same
table-parametric K-family runtime boundary that Lean already has. This is a
concrete cross-assistant consolidation, not a claim of a newly discovered
simulation principle. The five largest plainly shared runtime modules are still
physically copied into every Rocq variant. A common runtime theorem plus small
machine-data obligations would remove that maintenance duplication and remove
string-level proof rewriting from the generators. A single K215 endpoint would
still depend on the common runtime proof, so the physical multi-variant saving
must not be reported as an equal reduction of its transitive proof closure.

The actual `coq/215/` directory has 44 `.v` files, 8,026 physical lines. Its
largest files are `NormalizedCert215.v` (1,447), `ProgLibPerm.v` (780),
`DagPerm.v` (495), `Runtime230Core.v` (450), `L1_CompPerm.v` (331),
`Complete222.v` (314), `Sound222.v` (278), `DominatedCore.v` (269), and
`L2RootPerm.v` (246). `Source215.v` and `Correct215.v` are already short
composition facades; shortening their text is not a useful target.

## Work already done; do not re-propose it as new

* `Source215.certificate_normalized` checks 1,426 correspondence entries,
  replacing the earlier 2,240-entry offset relation. `NCheck.check_one_sided_iff`
  gets the reverse direction from `check_mirror`.
* `NormalizedBisim.ibeq` compares finite paths modulo the infinite false suffix.
  `PathCodec` already packs paths into `positive` with a sentinel.
* `DomRho8.rho8_all` is already a short adapter of a generic implication core.
* `L2RootPerm.root_step_det` already obtains backward classification from
  deterministic big-step execution and the forward `root_step_gen` theorem.
* `Sim230Main.tm230_rm` already uses `progress_halts` and a positive macro-step
  witness. A new generic progress theorem is not by itself a novel simplification.
* Recent commits removed the unused initial-state enumerator layer and shared
  the paired dispatch tactic scripts. The current source no longer contains
  the removed theorems; do not calculate savings against a stale baseline.

The fifteen simplification phases in `verification/k215/simplification/README.md`
are historical measurements with exact scopes. They are not fresh measurements
of this audit. The `normalized-91/README.md` describes a decode-based enumerator
checkpoint, while the current `EnumPerm`/`L1_*Perm` source is branch-expanded.
Use the pinned current files for architectural claims.

## Measured duplication

The read-only `prototypes/rocq/audit_runtime.py` removes nested comments,
replaces only namespace tokens `K<digits>F` by `KVF`, and strips blank lines and
line-edge whitespace. Under exactly that normalization, each of these modules
has one body across all eight variants 215, 217, 218, 221, 225, 226, 227, 229:

| Module | Bytes across eight variants | K215 representative | Other seven copies |
|---|---:|---:|---:|
| Zip | 30,923 | 3,959 | 26,964 |
| Runtime230Core | 156,227 | 19,622 | 136,605 |
| Tape230Blocks | 69,539 | 8,786 | 60,753 |
| Tape230Carry | 43,883 | 5,579 | 38,304 |
| Interpreter230Sites | 64,219 | 8,121 | 56,098 |
| Total | 364,791 | 46,067 | 318,724 |

These are source-body equivalence and physical-byte metrics. They do not mean
that one can delete the seven copies without an adapter: the imported machine
constants currently differ. The common parameterized proofs must be built
first. No net saving or compilation speedup has been measured for that refactor.

The calculus files shared by K215/K217 also normalize identically:
`Codes222`, `Thm222`, `DominatedCore`, `CD222`, `Prop222`, `G222`, `L224Def`,
`L224Prop`, `L224Meta`, `L224E`, `Interp222`, `Sound222`, `Complete222`, `DomRho8`.
This is a second straightforward namespace-sharing opportunity, separate from
the runtime. `regenerate215.py` lines 60-63 explicitly copy them from K217.

## Exact finite support already available

Lean's `KTape.lean`, lines 21-35, defines the engine states

```
[0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198]
```

The support contains both read-symbol rows at the first 21 states and the
read-1 rows of 113 and 198: 44 rows. The separate `IncTail` contract accepts
either the original three-row return or the bypass `(198,0) -> (1,L,40)`.
`KTape.boxLemmas` at lines 391-397 proves all four universally quantified
register-oracle lemmas from those hypotheses. This is existing Lean work to
port, not a proof supplied by the new prototype.

Parsing the complete pinned sparse tables gives:

| Pair with K215 | Differing state/symbol rows overall | Differences on the 44 engine rows |
|---|---:|---:|
| K217 | 55 | 0 |
| K218 | 118 | 0 |
| K221 | 129 | 0 |
| K225 | 157 | 0 |
| K226 | 177 | 0 |
| K227 | 181 | 0 |
| K229 | 193 | 0 |

K215, K217 and K218 use the bypass; the larger listed variants use the original
tail. The data includes missing rows as `None`; equality is not restricted to
present transition values. In K215, row `(183,false)` is absent, whereas K217
has a transition there. The delivered Coq negative control rejects that row.

## Concrete port plan

1. Separate the bounded-state context from the table. The busycoq context uses
   the same bound 230 in these sparse-label variants, so generic tape and zipper
   lemmas need not depend on a concrete table. `tmn` and `tm` become parameters
   or record fields, with the lifting lemma `tm_st` and terminal-row property.
2. Move tape representations and arithmetic facts out of `Boot230`. Presently
   generic modules import it even though the actual blank-tape boot certificate
   is candidate-specific. Keep definitions of `ones`, `zeros`, `sepsR`, and the
   fixed layout in a common module; supply the boot fact separately.
3. Port `AgreeRows` plus `IncTail -> BoxLemmas`. The four contracts have exactly
   the quantification already present as Section hypotheses in
   `Runtime230Core.v` lines 267-276: all gaps, all relevant registers, arbitrary
   left tape frame, and valid register-file lengths. They are not finite tests.
4. Make `Runtime230Core.sstep` and `exec` explicit in the table. Its current
   generic `oracle_sound`, `sstep_sound`, and `exec_sound` proofs then occur
   once. Preserve the exact return value, including the progress Boolean.
5. Make `Interpreter230Sites` and `Interpreter230Check` explicit in the source
   program, table, and maximum decoder depth. Replace generator edits of
   literals 40 to 48 by typed record fields and proof premises.
6. Make `Sim230.Inv` and `tm230_rm` generic in the program and boot register file.
   Put source well-formedness, site coverage, boot reachability and boot shape
   in the candidate record. Instantiate it for K215 and retain the public
   theorem names as short wrappers.
7. Regenerate only data and certificates. Delete proof-string substitutions
   only after the new adapter checks the identical dense table and the final
   statements have the same closed assumption profile.

`regenerate215.py` lines 148-198 show the present proof rewriting clearly:
namespace substitutions, disabled-row guards, changes to the boot constants,
replacement of `p230` by `p215`, `R0` by `R0p`, and repeated depth-bound edits.
The historical repair of forgotten `Nat.leb ... 40` splits in the repository's
Rocq README is a concrete reason to put those values behind an interface.

## Delivered kernel-checked prototype

Files under `prototypes/rocq/`:

* `OracleFootprint.v`: 111 lines, only Coq standard library imports. It models
  terminating adaptive table queries as an inductive query tree. Agreement on
  the queries made against one table implies equality of both the complete
  result and the entire query sequence against the other table. The proof is
  structural induction. `Answer` may include `None`, and the result
  `option (C * bool)` preserves executor failure and the progress bit exactly.
* `Support215217.v`: 574 lines, mostly the two complete literal sparse tables.
  It checks the 44 engine rows plus the common bypass (45 keys), proves the
  tables differ globally, rejects the missing 183/0 row, and instantiates exact
  query-result transport for a computation whose support is proved contained
  in those keys.
* `audit_runtime.py`, `runtime_audit.json`: deterministic producer, source hashes,
  full row comparisons and duplication census at the pinned commit.
* `check.py`, `verification.json`, `check-1.txt` through `check-3.txt`: fresh
  validation of the exact prototype sources.

Fresh compiler: Coq 8.16.1, OCaml 4.13.1. Both files compiled, six explicitly
requested assumption reports were `Closed under the global context`.
`coqchk -silent -o OracleFootprint Support215217` recursively rechecked them and
their standard-library dependencies in 24.20 seconds and reported no axioms,
no type-in-type, no unsafe fixpoints and no assumed positivity.

This is **not** a fresh Rocq 9.1 build of K215, an integration of the proposed
runtime abstraction, or a new proof of its endpoint. The query-tree adapter to
the maintained symbolic executor remains to be written; so does the Rocq port
of the universally quantified 44-row register contract. That distinction must
be stated in the report. The prototype is useful because it fixes the exact
transport obligation and its trust boundary rather than leaving the central
reuse idea as pseudocode.

## Immutable source references for the report

All paths below are relative to
`https://github.com/VladimirReshetnikov/ProveIt/blob/cbf94cb552a3b49509e0eee80e7455d4eb5974c6/`.

* `Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/regenerate215.py`
* `Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/source_data.py`
* `Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/Runtime230Core.v`
* `Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/Source215.v`
* `Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/Sim230Main.v`
* `Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/L2RootPerm.v`
* `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/README.md`
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KTape.lean`
