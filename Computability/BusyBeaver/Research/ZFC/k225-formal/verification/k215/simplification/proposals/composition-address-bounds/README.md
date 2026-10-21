# K215: proof composition and source-address bounds

Research contribution for Vladimir Reshetnikov's ProveIt, 21 October 2026.

**No correct machine with 214 or fewer working states was constructed.**
The positive results are three checked proof components and a new source
layout with an exact optimal zero-run bound in a restricted transformation class.

## Results

| Component | Result | Remaining boundary |
|---|---|---|
| `normalized_balanced/` | Existing 1,426-row normalization combined with balanced lookup; exact all-register source theorem; same public facade; recursive kernel audit | Production Rocq 9.1 complete machine/ZFC endpoint not rebuilt |
| `decoder_source_paths/` | Literal upstream source walk generates all shared decoder windows; exact primitive-entry result and whole-tape restoration | Native-label/zipper bridge and primitive/return integration |
| `cm215_stream/` | Existing CM215 table equivalent to accepted dense K215 on every initial binary tape, directly in repository stream semantics; closed Coq theorem and recursive audit | Short final ZFC endpoint client supplied as integration-only |
| `address_runs/` | Closed-reassociation capacity criterion; exact minimum zero run five; new 206-subtree/depth-43 source with original word and both CFGs | Two restricted physical allocation models fail; no new binary candidate |

The source correspondence checker now performs 32,961 indexing-node visits,
versus 54,514 for the previous balanced version and 5,018,706 for the original
list representation. The normalized counts are proved in Coq. They do not
measure total compilation time or complete proof size.

The supplied source layout removes all six-zero runs, preserving the full
4,751-primitive word and both complete 6,175-edge guarded CFGs. It is a source
program, not a 214-state Turing machine. The original machine has 202 distinct
source subtrees; the new source has 206, so sharing/allocation remains central.

## Read and reproduce

`report.pdf` is the comprehensive article. `report.tex` and `sections/*.tex`
are its editable source. It includes proofs, exact status boundaries,
candidate comparison, integration guidance, and further research questions.

Lightweight package and source checks, Python 3 standard library:

```
python3 verify.py
```

This checks all released identities and replays the lookup census, compact
source-rotation certificate, guarded CFG comparisons, and independent finite
capacity controls. It does not recompile proof-assistant sources or rerun the
integer allocation solver. Replays run in a temporary copy, preserving the release files. Component READMEs describe those explicit actions.
The frozen model-solver failures are research evidence, not a proof of a global
state-count lower bound.

Build the report with a standard TeX Live installation:

```
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

Build in a separate copy if you want the original release manifest to remain
unchanged. Intermediate TeX files and compiled proof objects are not included.

## Pins and verification status

The original snapshot is `aa66d0a33f1f8237a348899eb8095b045a502832`.
Commits through `56e487ce8fa4cf63ad169ffe0cd2944e9fc62dd3` were reviewed; the
maintained Lean and K225 Rocq source trees are identical between those pins.
The incoming proposals already contain normalization, balanced lookup,
framed local blocks, automatic source inference, marker variants, and concrete
scheduler theorems. This packet credits and reuses those results.

Coq checks use 8.18.0 / OCaml 4.14.1; Lean checks use 4.32.0. The production
Rocq lane is 9.1.0 and must be rebuilt before adoption. The report identifies
which checks are fresh compilations, recursive audits, same-session bound
objects, ordinary proofs, finite replays, and restricted synthesis attempts.
No source or endpoint theorem in this packet proves unconditional nonhalting.
The packet does not provide an encoded derivation in PA or ZFC's own syntax.

## Incorporation

The packet is additive research material. Keep primary K215 as the accepted
baseline. The normalized source facade preserves its public theorem type.
CM215 is the best immediate alternative for a short relative endpoint because
its new proof uses the exact native endpoint semantics. The decoder theorem
is a concrete next building block for replacing occurrence-specific site
proofs; its remaining adapters are explicitly listed. Update generators and
build manifests with any maintained proof replacement.

`MANIFEST.json` binds the released files. `provenance.json` records the reviewed
archive identities. Component notices retain the source and license ancestry.
