# Ten-variable direct-BFS decimal display

`equation.tex` and `equation.pdf` display the retained 80-row direct-BFS graph `ten-positive-unshift-t-finite/data/equation_qcube_V2.json`. Its ten strictly positive unknowns have distinct names `a` through `j`; `r01` through `r80` are abbreviations, not additional unknowns. Arithmetic is over the integers, so intermediate subtraction may be negative. All printed numerals are base 10. The display specifies the four fixed integers using finite formulas and a printed list of 943 decimal selectors.

All 80 displayed graph operations are live: 48 multiplications, 18 additions, and 14 subtractions. The count excludes construction of fixed constants and the ten shifts that express positive unknowns using unrestricted natural variables. `verify_degree.py` checks an upper bound of 750 and a nonzero diagonal coefficient modulo 1,000,000,007, certifying exact degree 750 for the actual retained coefficients. These operation and degree checks are external computations, not Lean theorems.

The [fixed symbolic direct-BFS Lean client](../direct-bfs-80-ipra-fixed-prototype/README.md) contains four assumption-free iPRA derivability statements for the once-shifted Lean graph and the direct-BFS symbolic ports. Its [65-stage selected-provider replay](../direct-bfs-80-coherent-rebuild/README.md) passed its recorded checks and a separate post-run receipt audit. That replay inherits the earlier 127-stage provider, 101 supplements and package/dynamic inputs; the outer process exit was not separately captured. The Python checks here connect the displayed rows, selectors and complete coefficient bytes to the retained graph and BFS table, but Lean does not parse or authenticate this PDF, TeX, JSON or the coefficient files. The direct-BFS K is different from the [original-kernel display](../ten-positive-80-original-kernel-display/README.md); their equal-looking formulas use different selector lists. This PDF is not the maintained original 14-variable `Computability/DiophantineConsistency/equation.pdf`.

Two separate builds in `build01/` and `build02/` produced byte-identical TeX and PDF. `check_display.py` independently checks all 80 rows extracted from the PDF against the pinned JSON, the 41 slot indices, the 943 printed selectors against the separate BFS table, all four complete coefficient payloads, the fixed formulas against the separately reviewed original display, and bounding boxes on all four PDF pages. `check_liveness.py` checks the operation breakdown and all fourteen inputs. `observations/check01/`, `observations/liveness01/`, and `observations/degree01/` retain their outputs and successful subprocess exits. All four PDF pages were visually inspected; the graph and fixed formulas are legible, selector blocks are aligned, and no clipping was visible. The root `equation.tex` and `equation.pdf` have no Git changes from this work.

To rebuild, invoke `python3 -I -S -B generate.py --output build03` with a fresh direct child output directory. The currently published bytes are:

- TeX SHA-256 `be7181e835a2b530da007b7b856ea9a799db2f2ad05aef8036a3a95ed21cd849`.
- PDF SHA-256 `412ebf276d1e3d9b2802d333e020a4b7579f2368660bdede31be665564e40fe7`.
- Complete BFS K raw SHA-256 `0a86821a704294199c2e1a50379d242c96840a3366e9d965689ba3d74605203f`.

The [independent display review](../../reviews/ten-positive-80-bfs-decimal-independent/README.md) separately checks all 80 rows, the direct-BFS Lean and JSON table, the 943 selectors, 41 slots, full payloads and a full diagonal-polynomial degree certificate. It does not provide Lean file semantics.

A later [full-recipe iPRA client](../ten-positive-80-bfs-displayed-full-ipra/README.md)
states all four derivability forms using Lean expressions for the displayed
beta, kernel lists, low support and high interval sums; its inferred types have
an [independent source/receipt review](../../reviews/bfs-displayed-full-ipra-independent/README.md).
The connection from the PDF text and coefficient files to those expressions
remains external, and the client's complete selected-provider ancestry has
not yet been authenticated.

The [selected-header capture](../ten-positive-80-bfs-full-closure/README.md)
matches all 1,795 previously replayed project records and 80 outside records,
and records 12 new selected modules. An [independent audit](../../reviews/bfs-full-closure-independent/README.md)
rechecks that capture; historical producer, package-transitive and dynamic
ancestry remain separate.
