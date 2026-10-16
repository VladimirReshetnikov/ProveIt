# Batch145 manuscript01 mathematical intake dossier

Reviewed16 October2026. Arrival commit9c98495586, untouched extraction
`/tmp/zfc-intake-145-zfno7ajz/01-zfc_small_machine_research/zfc_small_machine`.
All Python checks and PDF builds used separate copy `/tmp/zfc-review145-01`.
No release SHA256 manifest or line-ending work was performed. No Lean/Coq
build was performed by this reviewer; fibers owns the separate Lean review,
and mira_backend_route owns the complete machine/search suite.

## Pin, reading and placement

The declared project baseline is17d0f2eaa650901cda59764dfcc4661c199e49c8.
Four distinct requested earlier commits are b07d1a27bbe2814f2fd84cc55feef71c4de5b2db,
83ef1da6b717338f710277c2744fb4ec644cedbc,67086c8d8802ea7b3625a2fc0765d39e2181e335,
and6594795e9db81637c30959e42b3bcfc9eb77722f; later relevant pins fa6fcaf096446ff5774f6d03570f030314bc7ad8
and29efd22ed802c81f0ece48be0838ca48310983e6 are explicit. Upstream254 is297ab8df7e5de329605c3875b4934643b371a5e3.
The separately attributed253 source is mira-emmy PR20 head0d544f2a2e3c18f12278441a74b7879f31cbe856;
tested merge26bd0b2beeed5c3dd88511e39acd604c235e2f1c and CI metadata are distinguished
from a local build or exported ZFC proof object. Lean source pin is4.32.0,
commit8c9756b28d64dab099da31a4c09229a9e6a2ef35.

Read all1122 lines of report.tex, both included sections (73+150 lines),
root README.txt, machine README_AUDIT/STATUS/provenance, standalone Lean
source and its recorded axiom log, both mathematical Python scripts, and
the translated-equality comparator. No mathematical flaw found within the
stated scopes. Recommend existing closure-kernels addition, local10,
continuing the raw C/G calibration, exact codec and compiler questions.

## Mathematical findings and boundaries

1. Two-sided atomic indiscernibility Δ is an equivalence and full membership
congruence in pure equality-free logic. Replacing equality by Δ, with fresh
binders/deBruijn shifting, fixes CP/IR and maps each full-GIC instance to an
allowed equality-free full-GIC instance. Formula induction supplies equality
substitution. The line-by-line proof erasure is an ordinary conservative
interpretation for equality-free conclusions; the reverse inclusion is literal.
Nonempty quotient semantics is a valid cross-check. No Extensionality is
asserted for that quotient, so the interpretation composes with the existing
raw equality-bearing CP/GIC calibration instead of claiming to rebuild it.
The PA formalizability statement is a normal mathematical primitive-recursive
proof-transformer argument, expressly not a serialized PA proof or implemented
proof-code translator. No hidden choice principle or one-sided-profile error
was found.

2. The canonical base3 grammar exactly excludes Imp(Truth,Truth). Strong
induction gives encode(decode(n))=n for alln and the reverse on canonical
formulas. Positive child codes decrease; Truth0 has no labels. All atom and
binder labels are<n, so n itself is fresh, including vacuous code0. The
well-founded decoder can be implemented by primitive-recursive course-of-values
coding. This does not imply logical-calculus adequacy or runtime matrix coverage.
The single normalization preserves ordinary implication semantics, independently
of IR; F=Rel00 still needs its separate bridge.

3. The pure-logic counterinterpretation is correct: quantifiers identity,
Rel00=false and independent Rel01=true/Rel21=false validate every retained
logical row, MP, GEN and fresh atomic vacuity, but falsify ordinary UI
(All0 Rel01)→Rel21. Same-name UI also holds, so adding only it does not repair
cross-name substitution. The report correctly does NOT extend this
counterinterpretation to the full C/G theory, prove unconditional nonhalting,
or reject a single designated-refutation equivalence. The newer root research
notes add stronger protected-QI and constant-true-quantifier controls; none
supplies the missing full C/G refutation theorem.

4. Relative conjunction satisfies And_F(A,B)=F∨(A∧B), so commutation and
association hold for either truth value of F. They remain valid within the
same quantified contexts because no binder is moved. The proposed250 rewrite
therefore has a sound ordinary semantic justification independent of the
dual-rho6/falsity capture gap. A stronger exact-code rewrite proof would use
implicational tautologies (rho8 supplies classical implicational logic) and
GEN/QI to lift through quantifier contexts; that proof is not delivered as a
Lean/coded derivation certificate. The report honestly says semantic rewrite,
not an established full endpoint.

5. The translated-equality348 control replaces every explicit Eq atom by Δ
and computes its fresh local label k=3P(i,j)+1 with the existing Rel constructor.
This computed AST is a natural label in binder positions, not a nested atom
assertion there. k>i,j suffices for its internal quantifiers. The control
retains all original logical row types and both vacuity types; it does not
silently claim a complete numeric-calculus/alias/enumerator/compiler proof.
Its cost is implementation-specific, not a lower bound.

6. AtomicEquality.lean is a self-contained constructive semantic component:
no assumptions that Δ is actual raw identity, no quotient theorem, no
syntactic proof transformer, no set-theory calibration or machine theorem.
The source's seven principal theorem statements match its recorded no-axiom
reports. Independent compilation is assigned to fibers.

## New/overlap reconciliation against the current tree

* Host README.md:251–259 already records local09's same two-sided observational
profile equality bridge for CP/GIC and the associated nonclaims. This new
report rederives/clarifies it, adds explicit PA-proof-transport discussion and
the standalone Lean semantic component; do not present equality erasure as
new relative to the current collection.
* `Base3Syntax.lean:129,232,235,240,276,280` already proves all-natural decode
coverage, canonical inverse/injection, smart implication compatibility and
freshness. It entered in56a3fdcce. The new report's statements that the project
only covers finite positive syntax, and its proposed Lean codec task, are
historical to its baseline17d0. The paper's codec proof and100000-code audit
are useful independent confirmations, not a still-open current formal gap.
* `logical_engine_completeness.md:24–40` now records exact original-equality
instantiation dependencies; `:42–107` gives independent related countermodels
and the ax467/ax5o distinction. This report agrees that exact reduced-engine
completeness is open. Its simpler identity model cleanly pinpoints cross-name
transport and is scoped correctly.
* `full-logic-psc-control.json` now provides a different complete-front-end
control retaining the original Eq engine, measured279 with PSC and fixed
seed2 (283 with an explicit IR row). It does not supersede or contradict the
report's348 translated-equality control because the languages/theories and
programs differ. Neither is a verified changed machine.
* The 250 conjunction search is new literal compiler evidence relative to
the frozen252 family. It inherits the unresolved dual-rho6 and exact numeric
logic/search/backend obligations. It does not beat the attributed verified
253 endpoint as a proved consistency machine.

## Verification run by this reviewer

On the copy:

`uv run --no-project python code/logical_kernel_diagnostic.py --output /tmp/zfc-review145-01-logical.json`
PASS:16 Lukasiewicz assignments,4 QI cases,2 each commutation/old+dual B6c/vacuity/same-label UI,
GEN validity and48 relative-conjunction identities. The stated ordinary-valid
UI formula is false in the intended counterinterpretation.

`uv run --no-project python code/base3_codec.py`
PASS:100000 integer roundtrips/freshness checks,12288 constructor identities,
32896 independent triangular unpair cases,4 Truth-normalization Boolean cases.
Evidence was written only to the copy. This code uses assertions; executed
normally, not with-O. No release-manifest verification was attempted.

`pdflatex -interaction=nonstopmode -halt-on-error report.tex` twice on copy:
PASS,22 pages,20 embedded fonts,0overfull boxes/undefined references/citations/errors;
2underfull boxes in the artifact table (lines117–120 of the included machine
section). Physicalpage6 rendered/viewed at1600px, with readable unclipped
formulas and text. No delivered source was edited.

The joined machine review below and independent Lean review in
`intake-145-source-10-lean.md` complete the advertised intake checks. This
mathematical review finds no reason to reject placement and no completed
new machine endpoint.

## Joined independent machine review

Machine review completed after the mathematical dossier above:
`/tmp/zfc-report145-machine-wzvhf1xp/machine-review.txt` and `.json`.
Full offline `reproduce.py --offline --search-orders --search-conjunctions`
PASS in180.755s, including the full9216 new choices (172.152s), exact histogram
and both250 minimizers, all8 old variants and prior288 search. Frozen outputs,
recipe and deterministic evidence match; only elapsed timing changes.
Independent named/normalized1M-step lockstep compares every transition and the
entire tape; the prefix never enters edited AX. All62 framework states and123
partial framework rows match the frozen252 predecessor.250=188+62 with500total
rows and normalized hashd7af3920268db1c95bf71dc06b77e53c8266086a13043b2fc91f9319c520aff1.
7 normalizer and11 auditor regressions pass; all250 states remain graph-reachable,
exact-bisimulation singleton and no radius4/64-step merge. The348 control also
reproduces exactly:286+62,695partialrows,602macros,16384binder cases.
No manifest checks, repository edits or proof-assistant builds were performed
by the machine reviewer. The separately joined Lean review compiled the
standalone delivered source successfully: all seven principal theorem roots
have no axiom dependencies. That semantic component remains separate from
proof transport, source calibration and compiler correctness.
