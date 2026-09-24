# Foundations for surreal and surcomplex mathematics

Sets, classes, universes, type theories, and a pinned Lean audit.
One article, merged from **three independently written foundational audits**.

The article separates three verification records: the September 21 source
audits (source reading only), the original merge's checks of three illustrative
Lean files, and subsequent work in this repository. The latter is tracked in
[the formalization ledger](../../FORMALIZATION.md), with exact theorem mappings
and remaining obligations. At checkpoint `ebda0e0`, canonical normal-form
evaluation is an order isomorphism with inverse extraction; preservation of
arithmetic and strong sums, and real closedness of the concrete surreal carrier,
remain separate obligations. The proposed architecture is not a completion
report, and no complete verification of this article is claimed.

## September 22 exposition corrections

- **Workspace localization:** states the arithmetic preservation required of
  normal-form evaluation and gives a universe-relative version. An input family
  and the resulting exponent group must be small in the specified universe;
  being an arbitrary external set of elements of `No_U[i]` does not suffice.
  The proof now checks support unions, coefficient-function sets and compatible
  workspace inclusions.
- **Support recursion:** explicitly requires the controlling set `E` to be
  positive and well ordered, and explains why each nonlinear coefficient uses
  only finitely many decompositions into smaller positive exponents.
- **Topologies and convergence:** proves that intrinsic modulus and valuation
  balls define the same topology on a nontrivial Hahn workspace, although they
  are different balls and differ from the ambient fine subspace topology.
  Geometric partial sums converge exactly when their exponent multiples are
  cofinal. The new rank-one example `Σ t^(n/(n+1))` shows that arbitrary strong
  summation still need not be topological summation, even over `Q`.
- **Verification scope:** labels the historical checks as historical, links
  the later implementation ledger, and clarifies that `#print axioms` follows
  transitive dependencies of the named declaration without auditing all other
  declarations in imported modules.

These corrections change only the maintained article and this README.
The historical originals in `code/` and `data/` are unchanged. Source manuscripts
and their READMEs are retained in [Git history before their retirement from the
working tree](https://github.com/VladimirReshetnikov/Surreal/tree/251bd32/docs/foundations-and-computation/foundations/sources).

---

## What this is

`article.tex` / `article.pdf` — 95 pages, 26 numbered sections (21 main plus 5
appendices), 31 numbered theorem-environment results, 15 tables (11 longtables
plus 4 inline), 9 Lean listings, 88 numbered non-claims, 58 bibliography
entries. Standalone LaTeX: full preamble, internal `thebibliography`, no
external `.bib`, no graphics, no bibliography processor. It compiles in its own
directory.

The report does five things.

1. **Proves the elementary size obstructions** any surreal/surcomplex
   foundation must respect: `No` is a proper class; the unrestricted cut axiom
   is inconsistent (carrier against empty set — the one-line regression test for
   any axiom interface); `No` is not Dedekind complete; every *set* of positive
   surreals has a positive lower bound below it.
2. **Compares candidate foundations** — ZF/ZFC with definable classes, GB/GBC/
   specified NBG, Kelley–Morse, Grothendieck universes and Tarski–Grothendieck,
   Feferman reflection, birthday fragments, set-sized Hahn workspaces,
   constructive set theory, classical dependent type theory, HoTT and higher
   induction, internal `ZFSet` in Lean — in one reconciled table that records
   which audits rated each.
3. **Restates size-correctly, with proofs**, the workspace, summability,
   topology and phase principles of five supplied surcomplex research
   manuscripts.
4. **Reports one dated, pinned, read-only inspection** of the Lean 4 repository
   `vihdzp/combinatorial-games` at revision
   `02b4a908ea2ecfefffecb438f691951a814a5264`, separating what the inspected
   source establishes from what is an unverified bridge.
5. **Proposes a layered Lean architecture**, with module contracts, completion
   tests, a regression suite, and three complementary dependency ledgers.

---

## Which archives it came from

Three audit archives, all dated 21 September 2026:

| In this report | Archive | Size | Its own shape |
|---|---|---|---|
| **M1** | `01-size-ledger-and-universe-audit.tex` | 110,177 bytes, 1073 lines | 30 refs; ships 3 uncompiled Lean files |
| **M2** | `03-set-and-type-theory-comparison.tex` | 100,299 bytes, 923 lines | 32 pages, 28 refs; ships 2 uncompiled Lean files |
| **M3** | `06-classes-universes-and-lean-audit.tex` | 125,084 bytes, 1109 lines | 40 pages, 36 refs; ships **no** Lean files |

M3 supplies the prose spine and the section order. M1's tabular apparatus and
its finite-algebra descent theorem, and M2's topology counterexamples,
forbidden-shortcut discipline and trigonometry material, are grafted onto it.

The `build_report.json` / `build_report.txt` and `source_audit.json` records
ship verbatim in `data/`. The five Lean files from M1 and M2 ship verbatim in
`code/` — including M2's `LogicalGuards`, which does not compile as delivered
(see below). **Nothing in `code/` or `data/` was modified.** The three audit
manuscripts themselves, and their READMEs, are available in Git history at
checkpoint `251bd32`, under this report's former `sources/` directory. What each
contributed, and how each of their results was disposed of, is recorded in the
provenance material below and in the article.

### What each contributed uniquely

**M1** — the size ledger (safe vs. dangerous reading, 7 rows); the evidence
table whose third column is *"What is not claimed"*, used here as the
organizing device of the whole ecosystem section; the nine-row proposed-module
contract table; the finite-algebra descent theorem (Cayley–Hamilton plus
Artinian decomposition) and its companion non-claim about finite base change;
the *positive* half of the rescaling example (enlarge to `Q + Q·ω`); the
four-ring distinction `H_Γ(U) / A_{n,Γ} / F_{n,Γ} / K_Γ[[z]]` with two worked
separators; Feferman reflection (the only audit to treat it); the class-relation
sheaf encoding; the Hessenberg recursion measure with the argument that `max` is
not a substitute; the `MvPowerSeries.heval` TODO (the only concrete extension
target named anywhere in the group); the NFU warning; the notation glossary; the
five-milestone hierarchy of completion claims; the minimal dependency diagram;
the three-strategy comparison.

**M2** — the larger-index net counterexample (`D = F_{>0}` under reverse order),
the exact complement to the discreteness theorem; the no-countable-ball-basis
proof, and with it the engineering conclusion that Mathlib's *metric*
typeclasses are the wrong target while `TopologicalSpace` and filters are right;
closure under a fixed finitary signature, with the Hahn-sum caveat; sign-tree
categoricity; the entire trigonometry and global-phase strand (`Oz = Π ⊕ Z`,
kernels, and the Ehrlich–Kaplan initial-integer-part reconciliation); the Layer B
recentering warning; external countability versus internal properness;
`IsRealClosed` is an *interface*; `Classical.allZFSetDefinable`; the twelve-item
forbidden-shortcuts appendix; the eleven-row theorem-by-theorem dependency audit;
the Layers A–E architecture; the fine derivative over the *actual* scalar field;
the insistence that `FineHasDerivAt`, a formal-series germ, a Hahn-coherent datum
and a scalar-field derivation be distinct types.

**M3** — the nonpolynomial internally all-scale-coherent function on `C((t^Q))`
with its full support proof; the all-scale rigidity argument reconstructed in
support-theoretic form; support-local nonlinear recursion with its fixed-domain
corollary; the Hartogs coherence analysis (class replacement, Baire, and the
surcomplex-slices warning); the disjoint-disks sheaf necessity example; the
positive universe inventory proposition; local recursion and coherent assembly —
the group's only numbered theorem on recursion strength; the van den
Dries–Ehrlich identification of the *field* birthday cutoffs as the epsilon
numbers (so `ε₀` already qualifies and no large cardinal is needed);
real-closed-field quantifier elimination as a restricted tool, with the inventory
of absent predicates; "no nonconstant fine-continuous paths"; the
`Surreal/Cut.lean` finding; the valuation-vs-modulus separator `2t^ρ`; the three
distinct closure requirements; the character-and-actual-fibers pattern; the
residue pairing determinant; "sign-prefix simplicity is not birthday
precedence"; the Hessenberg agreement on embedded ordinals; the `Set RawGame`
positivity warning; the two failed simplifications; the Archimedean-argument
warning; the March 2026 announcement **at slide level**; the ten-row regression
table and the eleven-row dependency ledger.

---

## Two things this report is engineered to prevent

### 1. Three readings of one page are not three pieces of evidence

All three audits inspected the *same* repository at the *same* revision on the
*same* day by reading source through a web interface. They agree. That agreement
is evidence about what the source **says**, and about nothing else.

Those findings are therefore printed **once**, in one section, framed as a
single inspection with three concurring readers. The merged report's greater
length does not stand in for execution: zero of the three compiled a Lean file,
zero rebuilt the repository, zero recorded any `#print axioms` output, zero
performed a transitive axiom audit, zero ran Mizar, zero machine-verified any
manuscript. The only step common to all three was the LaTeX build.

### 2. Two near-mirror series that a reader must not confuse

Over the same field `K = C((t^Q))`, with opposite exponent signs and opposite
conclusions:

| | `A(X) = Σ t^(−n²) Xⁿ` | `f(z) = Σ t^(+n²) zⁿ` |
|---|---|---|
| valuations | `−n² + nq`, unbounded **below** | `n² + nσ`, unbounded **above** |
| strongly summable in `K`? | at **no** nonzero argument | at **every** argument |
| repair | enlarge to `Δ = Q + Q·ω` | none needed |
| says | a fixed workspace may be too poor to **evaluate** | a fixed workspace may be too poor to **rule out** a nonpolynomial all-scale function |
| from | M1 and M2 | M3 |

They are two *different* series proving two *different* non-transfer results.
Section 11 prints them adjacent, in one place, with an explicit paragraph — not
a footnote — stating that the sign is the whole difference and that the two
results are complementary rather than contradictory.

**The plus-sign example is a sharpness result, not a refutation.** The all-scale
polynomial rigidity theorem of the companion report at
`docs/surcomplex/analysis/` is stated for **class** functions on the whole of
`No[i]`, whose proper class of scales supplies the dominating exponent the proof
needs. Over the fixed value group `Q` no such exponent exists, and the
conclusion genuinely fails. Both are true. Section 11.5 says exactly that, and
cites the companion report by title and repository path — never by its internal
labels.

---

## What is NOT claimed

The full union of the three audits' limitation lists is **Appendix E**, 88
numbered items in eight groups. The headline items:

- **Historical verification.** No Lean or Lake executable was available in any of the three
  preparation environments, so none of the three audits compiled anything. Both
  were available where this merge was prepared. Three of the five shipped files
  were compiled and axiom-audited, under Lean 4.32.0 with Mathlib — **not** the
  `v4.35.0-rc2` the sources pin, which is not installed here. `FoundationsSketch`
  and `ComplexifySketch` compile as shipped; `LogicalGuards` does **not**, because
  a `/-!` module docstring precedes its `import`, and a docstring is a command.
  Moving the import to the first line fixes it. No `sorryAx` or
  `Classical.choice` occurs in those illustrative files' reported dependencies,
  and the two size-obstruction theorems depend on no axioms at all. The two files importing the external
  combinatorial-games library were not attempted, that repository being absent.
  In that original merge, the external repository was not rebuilt, its complete
  declaration set was not axiom-audited, no Mizar was run, and none of the five
  manuscripts was machine-verified. Later checks are recorded in the repository
  ledger and are separate from these historical results. Source inspection and
  compilation are different verification levels, and compiling three small illustrative files is neither an audit of the
  pinned revision nor a verification of any manuscript.
- **The pinned inspection.** Source reading only — no clone, no build, no
  comprehensive placeholder search, no axiom audit. Module names do not prove
  their strongest imaginable theorems. `#synth Field Surreal` is not proof of
  real closedness. A constructor for a Hahn type, or a comment describing an
  intended future isomorphism, is not that isomorphism. No normal-form
  equivalence, no real-closedness instance for the concrete carrier, no
  surcomplex algebraic-closure specialization and no Gonshor exponential was
  verified in the inspected modules — **a scope-limited observation, not a claim
  of absence from any other file, branch, repository or later revision.**
  Mathlib and Lean "latest" documentation pages are *rolling* sources consulted
  on the inspection date, not asserted to match the pinned dependency commit.
- **Consistency.** All assurances are relative to the chosen foundation and its
  metatheory. "Paradox-free" means only the exclusion of the specific invalid
  constructions analysed. GBC's conservativity over ZFC must not be strengthened
  to a claim about model expansions. A minimal consistency strength cannot be
  read off universe levels in source code.
- **The manuscripts.** All five are user-supplied research expositions, not
  certified libraries or refereed publications. **The Analysis manuscript is the
  only one read by all three audits**; every claim about the analytic-geometry,
  trigonometry, polynomial-algebra or Hartogs manuscripts rests on a *single*
  audit, and is tagged as such in the text. A fourth, global-divisors manuscript
  referenced inside one source was never supplied.
- **The mathematics here.** Elementary deductions included to make the
  architecture precise. No novelty claim, no priority claim, no resolution of
  any open conjecture. The plus-sign example specifically carries no priority
  claim and no machine-verification claim.
- **Design proposals.** All module names, layers and sequences are suggestions,
  not claims that files with those paths exist. A dependency gate not yet proved
  stays a stated hypothesis — never a new axiom called a theorem.
- **This merged document.** The three audits' agreement on the pinned revision
  reflects three readings of one source, not independent execution. Where they
  differ in scope, sources or emphasis, the differences are printed rather than
  averaged. The September 22 corrections and expanded arguments listed above
  are additions to the historical synthesis.

Two further record-keeping notes carried forward. M2's README refers to a
`SHA256SUMS` file: its archive did ship one, and this repository does not carry
it, because the collection ships no checksum manifests. And M2's reproduction
recipe warns explicitly against running `lake update` and then describing the
result as a check of the pinned revision.

## Later reports building on this one

- [birthday-cutoffs-and-hereditary-sets](../birthday-cutoffs-and-hereditary-sets/)
  proves cutoff-local versions of the bi-interpretation announced by
  Chen–Hamkins–Yang (recorded here, `found:sub:announcement`) and prints a
  written proof of the global statement as a proof of the announced theorem,
  credited to them; the announced axiomatization is not addressed there.
- [surreal-fields-across-universes](../surreal-fields-across-universes/)
  proves an external form of `found:thm:discrete`: for transitive `M ⊆ N`
  with the same ordinals, every `N`-set of elements of `No^M` is closed and
  uniformly discrete, and set-indexed Cauchy nets of old numbers are
  eventually constant, although filling of small cuts can fail in `N`.
- [omnific-preserving-automorphisms](../../surreal/omnific-preserving-automorphisms/)
  (batch 32) proves the general form of `found:sub:tsum`: a full Hahn field
  `k((t^Γ))` over a set-sized `Γ` has a Hausdorff ring topology realizing every
  Hahn sum as the limit of its finite partial sums iff `Γ = 0` or `Γ ≅ Z`
  (`opa:tc:thm:cyclicboundary`), and on `No` and `No[i]` only the indiscrete
  topology does so (`opa:tc:cor:fieldcollapse`). An unnumbered "Related (batch
  32)" note after `found:ex:boundedrankone` records this, citing that report by
  title and path; the page count (95) and all label numbers are unchanged.

---

## Build

```sh
cd docs/foundations-and-computation/foundations
latexmk -pdf -interaction=nonstopmode article.tex
latexmk -c
```

Standard TeX Live or MiKTeX. Packages: `lmodern`, `geometry`, AMS, `mathrsfs`,
`microtype`, `booktabs`, `longtable`, `array`, `enumitem`, `xcolor`, `fancyhdr`,
`listings`, `xurl`, `needspace`, `hyperref`, `cleveref`. No external figures, no
`.bib`, no bibliography processor, no shell escape.

Final build status: **95 pages; 0 errors, 0 undefined references, 0 undefined
citations, 0 multiply-defined labels, 0 duplicate-destination warnings, 0
overfull or underfull boxes, 0 warnings of any kind.**

Every `\label` carries the prefix `found:`, and every cross-reference resolves
inside `article.tex`. Companion reports are cited by title and repository path,
never by their labels.

---

## Directory

```
article.tex   the maintained merged report
article.pdf   95 pages
code/         the five Lean files from M1 and M2, three since compiled  (verbatim)
data/         the three build/audit records from M2 and M3                 (verbatim)
```

Related reports in this repository, cited by path from the article:

- `docs/surcomplex/analysis/` — surcomplex analysis; source of the all-scale
  polynomial rigidity theorem whose scope section 11.5 delimits.
- `docs/surcomplex/trigonometry/` — surcomplex trigonometry; companion to
  section 14.
