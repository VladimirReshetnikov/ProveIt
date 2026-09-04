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

## The consolidated volume

All eight subjects were merged, together with the shared apparatus of all
twenty-four articles, into

> [`Sequence_Inversion_Transseries/`](Sequence_Inversion_Transseries/) ---
> *Asymptotic Transseries and Inversion of Eight Sequences and Special
> Functions*,
> 205 A4 pages, 3 September 2026.

Chapter~0 of that volume states once, with complete proofs, the apparatus that
all twenty-four articles carry a copy of: the exponential--power model and an
axiomatized dominant core, the Bell-polynomial coefficient calculus,
Lagrange--Bürmann, the Lagrange fixed-point formula and perturbed inversion
around an exactly invertible core, the exact Lambert
carrier with its branch rule, the all-orders reversion, the flattening into a
polynomial--logarithmic transseries, the three inverse objects of a discrete
sequence, backward error, remainder transport and optimal truncation.  Its
Chapters~1--8 supply only the parameter dictionary and the subject-specific
mathematics, citing Chapter~0 266 times.  Chapters~5--6 add a second exactly
invertible core, `a x^p (log x - beta)`; Chapter~7 borrows its carrier from
Chapter~5 rather than rederiving it, as all three of its sources do; and
Chapter~8 falls outside the frame entirely, with no Lambert core and a
convergent expansion.

Facts the merge made visible: the partition numbers are the `alpha = 1/2`
case of the same model and reduce to the others by `xi = sqrt(N)` (with the
arithmetic shift taken first); the double factorial is *not* an
exponential--power model at all --- its phase is `(s/2) log s` --- so the
right common object is the core, not the model; the slope-denominator bound
of the power--logarithmic family is attained, with deepest pole
`binom(1/2,n) 12^-n` for Gamma; four apparently unrelated square roots are
one quadratic lemma seen through two different extractions; and the
K-function's "accelerated coordinate" is the resummation of its own resonant
subsector, a device that applies to Barnes `G` as well but which no Barnes
source attempted.

The twenty-four source packages were residue-audited and deleted on
4 September 2026; git history is the archive.

## The eight subjects, and what became of them

The twenty-four articles fell into eight subjects, three articles each,
written independently of one another.  All twenty-four have been **merged into
the volume above and deleted**; they remain in git history.  The volume's
Appendix~A lists every one of them with its line and page count and the
chapter that absorbed it, and Appendix~B lists every correction made to them.

| Subject | Volume chapter | Sources (deleted 2026-09-04) |
| --- | --- | --- |
| Butcher--Pólya rooted trees, A000081 | 1 | `Butcher_Tree_Transseries{,-2,-3}` |
| the double factorial | 2 | `Double_Factorial_Transseries{,-3}`, `double_factorial_transseries-2` |
| the partition numbers, A000041 | 3 | `Partition_Number_Transseries_and_{Asymptotic_,}Inverse`, `Partition_Numbers_Transseries_and_Inverse` |
| the swing factorial, A056040 | 4 | `Swing_Factorial_Transseries{,_Article,_and_Inverse}` |
| Gamma and Barnes `G` | 5 | `Asymptotic_Inversion_Gamma_Barnes_G`, `inverse_gamma_barnesG_transseries`, `inverse_gamma_barnes_transseries` |
| the hyperfactorial `K`-function | 6 | `inverse_k_function_transseries`, `K_Function_Inverse_Transseries`, `K_function_inverse_transseries_article` |
| the subfactorial | 7 | `inverse_subfactorial_transseries{,-2,-3}` |
| a real-argument Fibonacci function | 8 | `Fibonacci_Inverse_LogPeriodic_Transseries`, `fibonacci_inverse_transseries_article{,-2}` |

### The residue audit that preceded deletion

Two probes were run over all twenty-four sources against the assembled volume.

*Named results.* Every `\begin{theorem}[Title]` and its kin in every source
was matched against the volume's 409 titled results by content-word overlap.
Seven had no overlap at all; six of those turned out to be covered under
different names (lateral determinations, the Dobiński moment identity, the two
representations of the Bell tail, and so on).  The seventh was a genuine
omission — a **formal Newton valuation-doubling theorem**, stated in three
sources and nowhere in the volume — and it was added before deletion, as
Theorem `p6:thm:newton`.

*Numbers.* Every integer of at least four digits and every decimal constant
was looked for in the volume, decimals matched on their leading eight
significant digits so that a source printing forty digits and the volume
printing twelve count as agreeing.  Of 963 integers, 198 were unseen; of 1,288
decimals, 772.  Inspection showed these fall into three classes, none of them
substantive: standard number-theoretic tables (Bell numbers, derangement
numbers, swing-factorial values), the sources' own numerical error tables at
arguments the volume does not tabulate — the volume recomputed its own — and
coefficients printed one or two orders beyond the volume's truncation.  The
last class is regenerable in seconds from the recurrences the volume proves;
the two cases where the volume had stopped exactly one term short of a source
(`c_6` and `d_6` of the `K`-function) were filled in before deletion.

## Intake receipts

> **Superseded.** The packages these receipts describe were merged
> into the volume above and deleted on 4 September 2026, after a
> residue audit. The receipts are kept as the record of what arrived.

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
