# Audit supplement: commit e7c4cad, 16 October 2026

Inspected commit `e7c4cadf9b180e4b1801755b09777a7572412360`, timestamp
`2026-10-16T19:44:39Z`, parent `bda2b4860e6b3664d8ae84978bd7683572f55f49`.
The GitHub commit API and pinned file retrievals are the primary sources.
The baseline remains `83dec60c249ca0f9e1b2e5ee3cf18fd1ce58c373`.

## What changed

The commit modifies the ZFC research README and adds exactly four files:
`psc_backend_experiment.py`, `psc_backend_experiment.md`,
`psc_adapter_checks.py`, and `psc-backend-results.json`. All are in
`Computability/BusyBeaver/Research/ZFC/`.

It leaves the old raw C/G generator and frozen table intact. Pinned retrieval
confirmed unchanged Git blob IDs for `theory_backend_experiment.py`
(`7c469a12c6d7d2b1d1c3b458d14016791d5fb5a2`), the candidate note
(`763e35b518042a734ed96bf116723766c280b7b8`), and the frozen table
(`31e2e1b61b2a6eb1a02bc78823253ab32a7e4b01`). The latter still has SHA-256
`58f8aab7fcc21a7e3a88e6250bf05b7a97eaafd340f75ea8117b6d8f989f3142`.

The new experiment compiles a fixed-input-zero/output-one subset-PSC row
with fresh binder `k=c+2`, where `c` is its matrix code. Original rho6 is
retained. A primitive-Bottom control uses `Imp=4P`, `Rel=4P+2`,
`All=4P+3`; every residue-one code means Bottom. Code zero is closed Truth.
The adapter checks distinguish correct decode/encode normalization from
the false claim that every numeric Bottom alias round-trips to itself.

Exact macro-word grammar sharing at seed 93 gives a **different** named
252-state table, with 190 decision states, 62 framework states, and 503
rows. Its sole undefined row remains `1.inc/read1`. This named partial
table is `offset_bottom4_repair93.tm`, SHA-256
`76af4b702bc455bb4560530476b1c82313aa12d44cd4757c5aed2bf11710a08c`.
No replacement of the frozen raw table, no complete new literal table,
and no compiler endpoint theorem are supplied.

## What was independently reproduced

The new files were materialized byte-for-byte and checked against their
Git blob IDs. The generator SHA-256 is
`33337fc228b1347b7bb942bfdd98511e9d88da24458a9f0b759a5ed90f039902`;
the adapter SHA-256 is
`aeae5f034491b90ef27c35850e63da675819cd57d7bae43be6a1aee2f0ce7b5e`.

All seven fixed recipes and every core check were rerun using the existing
pinned offline backend. The complete resulting JSON equals the upstream
JSON after removing only its optional `searches` field. In particular:

| Recipe | Working states |
| --- | ---: |
| gated base three | 261 |
| offset base three | 256 |
| offset primitive Bottom | 257 |
| offset base three, best order | 255 |
| offset Bottom, best order | 256 |
| offset Bottom plus IR | 263 |
| offset Bottom, grammar seed 93 | 252 |

Every named-table hash also matches. The rerun includes 4,894 alpha
adapter cases, 100,000 decoder-normalization/label cases, 225 constructor
contracts, 19 closed macro roots, and the 32-case negative control against
the actual frozen C/G bundle. The 144 row/grouping variants and 200 grammar
seeds remain **source-reported searches**, not locally rerun searches.

## Relationship to this report's countermodel

The new commit correctly identifies its reduced logical kernel as
inadequate. Its counterinterpretation makes every universal operator
constant true, Bottom false, and all membership atoms false. Its PSC row
has a universally quantified conclusion, so it is true. Ordinary
same-variable specialization `All(a,Bottom) -> Bottom` is false.

The commit correctly shows that this particular algebra does **not** model
the frozen C/G bundle: the actual C and G start with existential
quantifiers and are false under constant-true universal operators.
That negative control does not exclude our different countermodel. In
this report every label quantifies genuinely over its own nonempty finite
domain; actual C and G are true, and the target is false.

Our model also validates the newly inspected PSC row. Let `D_i` and the
typed membership relations be as in `sections/countermodel.tex`. For any matrix
code `c`, set `k=c+2` and take its finite global output range

`S = { y in D_1 : exists x in D_0, phi(x,y) }`.

Because `k>=2`, `D_k` contains an object representing exactly `S` as
incoming membership from `D_1`. Since `k` exceeds every matrix label,
setting the hull coordinate does not change the matrix. Every matrix
output is in the hull, independently of the guard and root, and each
hull member has an input witness. Thus closure and support hold for every
root, making the PSC conclusion true without using its subset-boundedness
premise. This proof works for the primitive-Bottom and relative-falsity
codings and also validates the optional IR row.

Furthermore, our genuine finite quantifiers validate every same-variable
specialization `All(i,p) -> p`, while the ordinary cross-variable theorem
`All(0,Rel(0,1)) -> Rel(2,1)` remains false at coordinate1=5. Thus adding
only same-variable specialization repairs the commit's simpler algebra
but still leaves a precise stronger obstruction. The LaTeX section now
contains this proposition and proof as a dated mathematical supplement.

The concurrent PSC work has a narrower countermodel scope; the report's
main result about the unchanged actual C/G calculus remains valid. Both
analyses distinguish ordinary theory strength from the implemented
calculus. Neither supplies a new proof-assistant or literal-machine
simulation certificate.

## Supplemental files

All compact supplementary material is in `supplement/psc-e7c4cadf/`: the four
exact pinned sources/evidence files, `reproduced-results.json`,
`comparison.json`, and the newly reproduced named partial table.
The source evidence file is locally named `upstream-psc-backend-results.json`
to distinguish it from the independent rerun. The packaging agent can
copy this directory and this note without altering the baseline snapshot.

Primary document:
https://github.com/VladimirReshetnikov/ProveIt/blob/e7c4cadf9b180e4b1801755b09777a7572412360/Computability/BusyBeaver/Research/ZFC/psc_backend_experiment.md
