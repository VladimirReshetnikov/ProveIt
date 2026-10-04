# Scoped arithmetic/compiler intake at 0d7f51c44

This review found no new paid circuit below the current 84-operation unbounded ordinary-input construction. The strongest concrete alternative in these archives is Report55's completely materialized degree-12 matrix certificate, at 184,016 operations and 41,309 positive witnesses. The other arity reductions apply to a separately compiled finite horizon; the cellular-automaton improvements measure recognition radius and do not furnish corresponding arithmetic evaluators.

This is a bounded intake review, not approval of every manuscript, inherited theorem, source program, or saved verification claim. All conclusions below concern immutable arrival bytes at commit `0d7f51c442f5736f35d9de14d4c1b1f7cc1c2bbf`. No archived/frozen program was executed or imported, including extracted copies. Newly written metadata/data checks alone ran. No repository files were changed.

## Provenance and exact scope

Companion `review_new_arithmetic_0d7f51c44.manifest.json`, SHA256 `d19ed0ab027e866bf5ac5a5db129d0edbdd3e95616538fcb848860a6ae1c877a`, records every archive's full commit, Git blob, byte count and SHA256, and every immediate member's index, exact path, size, compressed size, CRC32, SHA256 and coverage. All archive/member bytes were reloaded from immutable Git and rechecked when sealing the manifest. This inventories 2,622 entries: 2,612 files and 10 directory entries, with 1,437 distinct member SHA256 values. Nested archives, if present, are inventoried as opaque members; this is not a recursive archive claim.

| Archive under `docs/incoming/` | Entries | Whole ZIP SHA256 |
|---|---:|---|
| `A196460_asymptotics_and_inversion_sources.zip` | 176 | `821a1cfc1c00fd6d109ee2f6ff8007b4e8985f03d45f6f9a04d07aa8623fde27` |
| `A196460_sharp_uniform_truncations_sources.zip` | 584 | `9e223bb02aed17d87552925bd5019d8955da1ea8731883b94de8e7630c97b47e` |
| `Bounded_certificates_and_encoded_gap_counts_source.zip` | 106 | `e7fbba10802123b84e3f41344191add059901282f16541eaaf66a8ea2e0fbacb` |
| `Chronological_Diophantine_Matrix_Certificates_Package.zip` | 78 | `ac5f61c6ed8d98792800f956097d27d88b73a5780afb9b1925d9592e2d89fc78` |
| `Low_arity_Diophantine_compilers_sources.zip` | 638 | `b55164fe4c5f70284f9c5040f82b144ab3f66220cf16deaf9b5369cb401132f2` |
| `Positive_POWER_reductions_and_exact_compiler_costs_source.zip` | 532 | `27ccef88ab20c0497c0df54b252e6fd2f29d16309246782f514a69102d4ecffe` |
| `Shorter_exactness_windows_sources.zip` | 329 | `b39b1731647f70ba8a86adfab456ab3733782c9cd317444f3907ff2fafa9eaca` |
| `Two_scale_recognition_radius_sources.zip` | 179 | `f03c89a1d48f3edc1ec0c18e5fe3b9f119bb7b747d2f2809f21c78adb2116aa9` |

The eight primary READMEs were read completely. Two additional Report55 interface notes were read completely. There are 17 selected text-span records, for 27 text records total; the following table specifies every read. Line numbers are one-based physical source lines; exact span hashes including original line endings are in the manifest. A heading-only search of the eight main TeX members selected these spans and is not an additional manuscript read. Nested README copies and unread body sections remain inventory-only.

| Archive shorthand | Member | Exact text read |
|---|---|---|
| Asymptotics | `ArityAsymptotics/README.md` | 1–113 (complete) |
| Uniform sectors | `UniformSectors/README.md` | 1–172 (complete) |
| Report66 | `Report66/README.md` | 1–111 (complete) |
| Report55 | `README.md` | 1–87 (complete) |
| Report69 | `Report69/README.md` | 1–122 (complete) |
| Report67 | `Report67/README.md` | 1–77 (complete) |
| Report71 | `Report71/README.md` | 1–85 (complete) |
| Report70 | `Report70/README.md` | 1–101 (complete) |
| Report69 | `Report69/Report69.tex` | 42–425; 532–632 |
| Report67 | `Report67/Report67.tex` | 319–455; 675–797 |
| Report55 | `science/ARCHITECTURE.md` | 1–164 (complete) |
| Report55 | `science/SOURCE_NOTES.md` | 1–105 (complete) |
| Report66 | `Report66/Report66.tex` | 94–288; 288–303; 359–408 |
| Asymptotics | `ArityAsymptotics/article.tex` | 44–133; 887–939 |
| Uniform sectors | `UniformSectors/article.tex` | 36–153; 641–680 |
| Report71 | `Report71/Report71.tex` | 40–71; 310–359; 435–437 |
| Report70 | `Report70/Report70.tex` | 44–77; 448–509; 621–641 |

Separately, the entire Report55 `science/evidence/polynomial-dag.json` was parsed as inert data and checked as described below. Its SHA256 is `95e2563fcfcaecfdc5918ffd6dd7421896350df8969a38f08cbb5f5060d80034`. This is the only complete archived arithmetic DAG audited in this intake.

## Arithmetic and compiler findings

**Report55: an actual degree/cost tradeoff.** The architecture describes chronological packing of the fixed matrix context with initial state `(35426321,-19628667,1,0,x)`, LOAD acting by the displayed inverse matrix while decrementing the counter, 96 TILE choices enabled at counter zero, and equal terminal rows. It asserts the language for that fixed context; it is not a new implementation of arbitrary program-dependent initialization. Its paid modules are 1,475 POWER calls and 491 subset calls. Their inherited Pell/group semantics and the full chronological proof were not independently recertified here.

Fresh independent analysis of the actual JSON verifies all 184,016 gate operands and topological ordering, all declared leaves, and complete backward liveness of all gates, all 41,309 witnesses, and ordinary input `x`. Counts are 72,093 multiplications, 64,111 additions and 47,812 subtractions, hence 111,923 A operations in a combined +/- ledger. The finalizer literally squares and sums all 23,618 declared residual differences: 47,236 difference/square gates followed by 23,617 additions. The body has 113,163 gates and the finalizer 70,853. The witness ledger is `1475*26 + 491*5 + 504 = 41309`; residual count is `1475*15 + 491*3 + 20 = 23618`.

A fresh graph degree propagation gives degree at most 12. Restricting the actual first POWER call's 13th equality (`bounds.offset.eq13`, left `gate:15`, right `gate:57`) to its `w,g` leaves with all other dynamic leaves zero gives `-w^4*g^2-2*w^3*g^2`. Thus a literal degree-six residual occurs, and its square cannot have its leading homogeneous form canceled in the complete real sum of squares. This proves exact degree 12 for these bytes. It does not prove each module's semantics or provide a full native numerical zero. This packet is a useful paid low-degree reference, with much larger cost and witness count than the current work.

**Reports66 and69: genuine finite-table arity reductions.** The selected clipping proof is sound: through transition `T`, a counter initially at least `T` and its clipped representative make the same zero tests, since tests occur before the final decrement. Final counter values need not agree. Report66's finite interpolation gives exactly three positive witnesses and six residual slots; Report69 replaces it by a tensor construction with exactly two positive witnesses and five residual slots. The selected range/slack arguments force the unique clipped cell, with no encoded-input promise. These are polynomials compiled separately for a fixed program and fixed `T`; acceptance-table construction, coefficients, degree and support change with `T`. Neither an external existential quantifier over `T` nor unique bounded witnesses internalizes that family into one fixed unbounded polynomial.

Report69's alternative uses one positive witness and a product of nonnegative cell polynomials. The selected cell formulas, positive-tail condition and disjointness prove unique positive witness in each accepted cell. This product is not one residual square: replacing it by its square doubles degree. The zero-versus-one classification is for fixed finite clipping tables with unrestricted degree, not arbitrary c.e. languages. The article gives paid arithmetic upper bounds for evaluating those finite-table formulas; these do not make the growing coefficient table free. Its gap compositions have 28 positive witnesses/17 residual squares for the two-witness native formula, or 27 positive witnesses/12 squares plus the nonnegative native product. These are finite-horizon predicates.

**Report67: twelve leaves, not twelve gates.** The selected reduction makes the quotient `q_alpha` strictly positive, reconstructs the eliminated Pell data rationally and then integrally, and uses that strict sign to recover the positive branch. Its stated converse restores the strict-quotient subset of the older presentation; it does not claim every old quotient-zero completion transfers. The new 12-leaf POWER module includes its output and has five residual slots; the displayed fixed-base polynomial has degree 20, and variable-base degree 24. No optimized arithmetic DAG for it is supplied in the selected interface. The finite gap composition with the older three-witness native table has 29 positive witnesses, 32 variables including its three inputs, and 18 residual slots. Reports66 and69 use different native/module presentations, explaining their 57- and 27/28-witness ledgers. Full gap fibers remain infinite despite uniquely decoded input and native projection. No inherited Pell theorem was newly certified here.

**The two A196460 archives concern the number of finite tables.** The first connects zero-auxiliary tables to `C_n=1+a_n`, supplies fixed-order asymptotic/inverse expansions, and explicitly separates approximate inversion from exact integer threshold comparison. The successor's reported sharp uniform tail constants concern finite exact sectors, not an unrestricted growing-order inverse or simultaneous replacement by leading monomials. Their statement/scope sections were read; the analytic estimates and claimed sharpness were not independently proved. They do not contain a lower paid source for the unbounded compiler interface in question.

**Reports70 and71 improve a different resource.** Their reported sufficient radii are respectively `108D+149+3J` and `76D+104+3J` (the latter includes a same-rule support refinement). The corresponding inherited numerical substitutions are 55,027,013 and 38,722,712. These are sufficient radii, not arithmetic gates or minimum-radius theorems. Both packets expressly retain an absent universal-source table as an inherited premise. They preserve admissible simulated trajectories while changing the full-shift rule on malformed inputs. Consequently prior arbitrary-input transition certificates, circuit counts, ordered-factor budgets and evaluators do not transfer automatically. Report71's support-bound argument was read, but its complete recognition/geometry proof and Report70's full-shift theorem were not re-audited. Neither packet supplies the missing new-rule arithmetic evaluator.

## Routing and limits

No correction to a selected cost interface was found. The most useful next uses are Report69's finite-table formulas for deliberately bounded predicates, Report67's strict positive quotient when designing a separately paid POWER implementation, and Report55's literal degree-12 DAG as a high-cost baseline. None warrants changing the current universal paid-operation frontier from this review. The radius results would first need a new arbitrary-input arithmetic implementation and cost audit. The analytic counts require no compiler integration.

This review authenticates arrival bytes, exact declared reading, and the narrowly specified fresh Report55 DAG checks. It does not validate archived test suites, reproduce historical receipts, approve unread proof sections, establish novelty, or certify the inherited universality/Pell/physical simulation dependencies.
