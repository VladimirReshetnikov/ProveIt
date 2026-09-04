# Special-function inversion at infinity

Twenty-four independently written articles that invert a rapidly growing
special function at infinity to all orders, filed here on 2026-09-03 as
quick-gate intakes in four batches: three from commit `5a453e1dc`, six more
that arrived while that first batch was being published, three (the Fibonacci
subject) later the same day, and twelve more (the last four subjects) in a
fourth batch that evening.  All twenty-four came as ZIP archives; the archives
were deleted after unpacking and git history is the archive.

They share a method rather than a function.  In each, the map to be inverted
has a dominant *power–logarithmic* phase, so ordinary series reversion does not
apply; the first step is to invert that phase exactly with the Lambert
`W`-function, and the remaining Stirling- or Bell-type corrections then
generate a finer grid of transseries blocks above that core.  Each article also
extracts a general reversion calculus from its worked case.

This is why they are filed apart from
[`../lambert-inverse-transseries/`](../lambert-inverse-transseries/), whose
three articles all invert the single map `x + W(x)`: the subgroups share the
Lambert-core technique, but that one treats one map in depth while this one
applies the technique across different special functions.

## The eight subjects

The twenty-four fall into eight subjects, three articles each, written
independently of one another.  That was noted at intake as provenance; **no comparison,
deduplication, or canonical selection has been made**, and the titles below are
transcribed rather than assessed.

### Gamma and Barnes `G`

| Directory | Document | Source | PDF |
| --- | --- | --- | --- |
| `Asymptotic_Inversion_Gamma_Barnes_G/` | *Asymptotic Inversion of the Gamma and Barnes `G`-Functions: Lambert-Core Transseries and a General Reversion Calculus* | 2,376 lines; 83,252 bytes | 29 A4 pages; 646,225 bytes |
| `inverse_gamma_barnesG_transseries/` | *Asymptotic Transseries for the Inverses of the Gamma and Barnes `G`-Functions: Lambert–`W` Normal Forms, All-Orders Reversion, and Residual Certification* | 1,655 lines; 72,966 bytes | 28 A4 pages; 663,480 bytes |
| `inverse_gamma_barnes_transseries/` | *Asymptotic Inversion of the Gamma and Barnes `G` Functions: Lambert-Normalized Transseries, Explicit Coefficients, and a General Power–Logarithmic Reversion Calculus* | 1,827 lines; 60,596 bytes | 25 A4 pages; 324,795 bytes |

### The hyperfactorial `K`-function

| Directory | Document | Source | PDF |
| --- | --- | --- | --- |
| `inverse_k_function_transseries/` | *Inverting the K-Function at Infinity: Lambert–`W` Normalization, All-Orders Transseries, and a General Theory of Power–Logarithmic Reversion* | 2,259 lines; 66,867 bytes | 29 A4 pages; 349,822 bytes |
| `K_Function_Inverse_Transseries/` | *Asymptotic Inversion of the Generalized Hyperfactorial `K`-Function: Lambert and `r`-Lambert Anchors, Centered Bernoulli Structure, and a General Calculus for Power–Logarithmic Transseries* | 2,644 lines; 90,380 bytes | 33 A4 pages; 724,630 bytes |
| `K_function_inverse_transseries_article/` | *Asymptotic Inversion of the Kinkelin–Bendersky `K`-Function: Lambert-Anchored Transseries for the Generalized Hyperfactorial and a General Theory of `x^p log x` Reversion* | 2,581 lines; 84,722 bytes | 30 A4 pages; 743,783 bytes |

### The subfactorial

| Directory | Document | Source | PDF |
| --- | --- | --- | --- |
| `inverse_subfactorial_transseries/` | *Inverting the Subfactorial at Infinity: Bell-Sector Transseries, Inverse-Gamma Geometry, and a General Reversion Calculus for Rapid Cores with Tiny Oscillatory Tails* | 2,631 lines; 95,404 bytes | 38 A4 pages; 688,626 bytes |
| `inverse_subfactorial_transseries-2/` | *Asymptotic Inversion of the Subfactorial: Bell-Number Tails, Inverse-Gamma Anchoring, and a Calculus for Exponentially Separated Transseries* | 2,188 lines; 73,742 bytes | 27 A4 pages; 725,870 bytes |
| `inverse_subfactorial_transseries-3/` | *Inverse Subfactorials at Infinity: Lambert–`W` Carriers, Bell-Number Sectors, and a General Calculus of Gamma-Dominant Transseries* | 1,878 lines; 81,203 bytes | 35 Letter pages; 530,302 bytes |

### A real-argument Fibonacci function

The fourth subject differs from the first three in its core: the map inverted
is a real continuation of the Fibonacci numbers, so the dominant phase is a pure
exponential in the golden ratio and the inverse transseries is *log-periodic*
(oscillatory in `log` of the argument) rather than Lambert-cored.  Filed here
because the purpose is the same, inverting a rapidly growing special function
at infinity to all orders with an extracted general reversion calculus; the
titles are transcribed, not assessed.

| Directory | Document | Source | PDF |
| --- | --- | --- | --- |
| `Fibonacci_Inverse_LogPeriodic_Transseries/` | *Inverting a Real-Argument Fibonacci Function: Log-Periodic Transseries, Exact Coefficients, and a General Product-Reversion Calculus* | 2,554 lines; 89,365 bytes | 33 A4 pages; 787,646 bytes |
| `fibonacci_inverse_transseries_article/` | *Log-Periodic Transseries for the Inverse of a Real Fibonacci Continuation* | 2,857 lines; 98,788 bytes | 36 A4 pages; 797,090 bytes |
| `fibonacci_inverse_transseries_article-2/` | *Inverse Asymptotics for a Real-Argument Fibonacci Function* | 1,884 lines; 64,334 bytes | 24 A4 pages; 759,845 bytes |

### The Butcher--Pólya rooted-tree numbers (A000081)

The fourth batch's first subject leaves the Stirling-type world: the sequence
is defined by the functional equation `T(z) = z exp(sum_k T(z^k)/k)`, so the
inversion runs through a Pólya-tree singularity analysis and a Lambert--`W`
reversion of the exponential-power model rather than through a gamma-ratio
normal form.

| Directory | Document | Source | PDF |
| --- | --- | --- | --- |
| `Butcher_Tree_Transseries/` | *All-Orders Asymptotic Transseries for the Butcher--Pólya Tree Numbers and Their Inverses* | 1,674 lines; 55,275 bytes | 21 A4 pages; 593,560 bytes |
| `Butcher_Tree_Transseries-2/` | *The Butcher-Tree Counting Transseries: All-Order Pólya-Tree Asymptotics, Lambert--`W` Reversion, and the Asymptotic Inverse of A000081* — the only `book`-class member of the subgroup | 2,853 lines; 100,576 bytes | 62 A4 pages; 763,748 bytes |
| `Butcher_Tree_Transseries-3/` | *Asymptotic Transseries of the Butcher--Pólya Rooted-Tree Numbers: Bell-Polynomial Coefficients, Lambert--`W` Reversion, and Exponentially Small Singularity Sectors* | 2,382 lines; 91,654 bytes | 35 A4 pages; 697,611 bytes |

### The double factorial

Here the object is an *interleaving* of two gamma-type branches, so all three
articles make the same structural point at intake: there is no canonical real
inverse of the sequence until an interpolation is fixed, and the even and odd
branches must be inverted separately before any discrete inverse is defined.

| Directory | Document | Source | PDF |
| --- | --- | --- | --- |
| `Double_Factorial_Transseries/` | *Complete Asymptotic Transseries for the Double Factorial and Its Inverses: Bernoulli--Bell coefficient formulae, Lambert-`W` reversion, parity branches, and the periodic OEIS interpolation* | 1,552 lines; 52,202 bytes | 18 A4 pages; 632,400 bytes |
| `Double_Factorial_Transseries-3/` | *The Double Factorial and Its Inverse: Complete Asymptotic Transseries, Borel Summation, and General Coefficient Formulae* | 2,287 lines; 79,355 bytes | 28 A4 pages; 662,997 bytes |
| `double_factorial_transseries-2/` | *Double-Factorial Transseries and Their Inversion: Bernoulli--Bell Coefficients, Lambert-`W` Cores, Parity Sectors, Borel Structure, and Discrete Inverses* — `book` class; inner files are lowercase `double_factorial_transseries.*`, kept as submitted | 2,138 lines; 63,319 bytes | 44 A4 pages; 622,907 bytes |

### The partition numbers (A000041)

The only arithmetic subject in the subgroup: the transseries is Rademacher's
convergent series reorganized into root-of-unity sectors with periodic
Dedekind-sum amplitudes, and the inversion is of the Hardy--Ramanujan phase
`pi sqrt(2N/3)`.  These three are also the only members that carry no
Libertinus faces.

| Directory | Document | Source | PDF |
| --- | --- | --- | --- |
| `Partition_Number_Transseries_and_Asymptotic_Inverse/` | *Arithmetic Rademacher Transseries for the Partition Numbers: Exact Exponential Sectors, All-Order Coefficients, and Asymptotic Inversion* | 1,901 lines; 83,252 bytes | 32 A4 pages; 369,259 bytes |
| `Partition_Number_Transseries_and_Inverse/` | *Rademacher Transseries for the Partition Numbers and Their Inverse: All-order arithmetic sectors, coefficient formulae, Lambert--Lagrange reversion, and phase-locked inversion* | 2,020 lines; 72,533 bytes | 27 A4 pages; 354,685 bytes |
| `Partition_Numbers_Transseries_and_Inverse/` | *Rademacher Towers and the Asymptotic Inverse of the Partition Numbers: Exact root-of-unity sectors, all-order coefficient formulae, Lambert--`W` reversion, and the discrete staircase* | 1,905 lines; 78,298 bytes | 33 **Letter** pages; 553,908 bytes |

### The swing factorial (A056040)

The central binomial-type quotient `n!/floor(n/2)!^2`, whose even and odd
subsequences carry different power prefactors (`2^n n^(-1/2)` and
`2^n n^(1/2)`), so — as with the double factorial — the parity split precedes
the inversion and each branch gets its own Lambert-normalized reversion.

| Directory | Document | Source | PDF |
| --- | --- | --- | --- |
| `Swing_Factorial_Transseries/` | *All-Orders Asymptotic Transseries for the Swing Factorial and Its Two Inverse Branches: Bernoulli--Bell coefficient calculus, Lambert--`W` normal forms, logarithmic reversion, and beyond-all-orders control* | 1,885 lines; 75,057 bytes | 28 A4 pages; 688,586 bytes |
| `Swing_Factorial_Transseries_Article/` | *The Full Asymptotic Transseries of the Swing Factorial and Its Inverse: Gamma-Ratio Normal Forms, Bernoulli--Bell Coefficient Calculus, Borel Geometry, and Lambert-Normalized Reversion* — inner files are lowercase `swing_factorial_transseries.*`, kept as submitted | 1,824 lines; 62,179 bytes | 25 A4 pages; 666,609 bytes |
| `Swing_Factorial_Transseries_and_Inverse/` | *Parity-Resolved Transseries for the Swing Factorial and Its Inverse: Exact Borel normal form, Bell-polynomial coefficient formulae, Lambert-`W` cores, and all-orders reversion* | 1,389 lines; 56,138 bytes | 22 A4 pages; 326,626 bytes |

## Intake receipts

Every archive passed a CRC check and carried no absolute path, no
parent-directory traversal, and no symlink entry.  Each contained exactly one
`.tex` and one `.pdf` at top level with no wrapping directory, so each
destination directory was created at filing.  No checksum ledger was submitted
and none was added.

All nine sources are LF with a final newline, so no line-ending normalization
was applied and the filed bytes are exactly the submitted bytes.  Where an
archive's inner filenames differ from its directory name — as in
`inverse_subfactorial_transseries-2/` and `-3/`, whose inner files are both
plain `inverse_subfactorial_transseries.*` — the submitted names were kept
verbatim, following the precedent of
[`../lambert-inverse-transseries/lambert_inverse_transseries_bundle/`](../lambert-inverse-transseries/lambert_inverse_transseries_bundle/).

All nine PDFs are readable and unencrypted, produced by pdfTeX-1.40.26, with
every font row embedded and no Type 3 font.  Eight are A4, which is canonical;
`inverse_subfactorial_transseries-3/` is Letter.  Five carry Libertinus faces
and four do not (`inverse_k_function_transseries/`,
`inverse_gamma_barnes_transseries/`, `inverse_subfactorial_transseries-3/`,
and, on the page-size axis as well, the same Letter package).  Those are the
batch's only styling debts.

None of the nine loads the shared notation file `docs/fabius-notation.tex`;
each uses document-local notation, so all nine are outside the corpus notation
migration and free of its defect classes.

**One directory was renamed at filing.**  The archive
`K_Function_Inverse_Transseries_LaTeX_and_PDF.zip` would have produced a full
path of 263 characters for its PDF, past the Windows `MAX_PATH` limit of 260,
and tools then fail with a misleading *"No such file or directory"* for a file
that plainly exists — `pdfinfo` did exactly that here.  The directory is
therefore named `K_Function_Inverse_Transseries/`, after the document, which is
also the convention the rest of the corpus follows.  Its contents are
unchanged.  The remaining paths run 249–259 characters; the longest,
`Asymptotic_Inversion_Gamma_Barnes_G/`, sits one character inside the limit, so
this subgroup has no headroom for deeper nesting or longer names.

### The fourth batch (twelve archives)

All twelve passed a CRC check and carried no absolute path, parent-directory
traversal, or symlink entry; each held exactly one `.tex` and one `.pdf` at top
level with no wrapping directory, and the twelve archive stems are distinct, so
they name the directories.  Two collision hazards were checked rather than
assumed: the three Butcher archives ship **identical** inner file names
(`Butcher_Tree_Transseries.tex`/`.pdf`), and `Double_Factorial_Transseries.zip`
and `double_factorial_transseries-2.zip` ship inner names differing only in
case, which on a case-insensitive filesystem is the hazard that silently nests
one arrival inside another; distinct destination directories were created
explicitly and the thirteen pre-existing members were verified intact after
filing.

All twelve sources are LF with a final newline and were filed byte-for-byte;
git reported no line-ending normalization at staging.  All twelve PDFs are
readable and unencrypted, produced by pdfTeX-1.40.26, with every font row
subset-embedded and no Type 3 row.  Eleven are A4;
`Partition_Numbers_Transseries_and_Inverse/` is Letter.  Eight carry Libertinus
faces; the four that do not are exactly the three partition articles and
`Swing_Factorial_Transseries_and_Inverse/`.  Two members are `book` class
(`Butcher_Tree_Transseries-2/`, `double_factorial_transseries-2/`) where the
rest are `article`.  None of the twelve loads `docs/fabius-notation.tex`, so
all twelve are outside the notation migration.  No checksum ledger was
submitted and none was added.

**Path lengths.**  Measured from the repository root the longest filed path in
this batch is 228 characters
(`Partition_Number_Transseries_and_Asymptotic_Inverse/…​.pdf`), and 239 from the
root of a checkout at `C:\ProveIt`.  In a *git worktree* nested under
`.claude/worktrees/<name>/`, however, four of the twelve exceed the Windows
`MAX_PATH` limit of 260 — the longest reaching 291 — so tools that are not
long-path aware report a misleading *"No such file or directory"* for files
that plainly exist.  Git itself is configured with `core.longpaths`, and the
metadata above was read with Python, which is long-path safe.  Nothing was
renamed on that account, because the repository-root path is what the corpus
convention measures and it is well inside the limit; the constraint is recorded
here so the next batch does not nest deeper without checking.

## Deferred

Nothing beyond title, abstract, and package metadata was read at intake.  Claim
comparison against the corpus, comparison *among* the three articles in each
subject, deduplication against
[`../lambert-inverse-transseries/`](../lambert-inverse-transseries/) and
[`../../lambert-w/`](../../lambert-w/), proof checking, numerical reproduction,
canonical selection, editorial consolidation, styling repair, and Lean
crosswalking are all deferred.  Nothing here has been merged, rewritten, or
verified.

One connection worth recording for that later phase, and *not* acted on: the
corpus already carries a Lambert-`W` layer of its own — analyticity of both
real branches, the lower-branch bracket with its explicit remainder rate, and
the Fabius saddle expansions — so the "Lambert core" these articles build on is
formalized here to a degree they do not assume.  Whether any of their reversion
machinery is already available in that layer is unexamined.

See [`../../MANIFEST.md`](../../MANIFEST.md) for the group record.
