# Reproduction and incorporation

Run commands from the root of the extracted packet unless a command explicitly
changes directory. Use an ordinary Python 3.10+ interpreter, without `-O`: the
finite audit scripts intentionally use assertions. No network is required once
the pinned repository sources and proof toolchains are available.

## 1. Verify the packet and repository revision

```sh
sha256sum --check MANIFEST.sha256

export PROVEIT_ROOT=/absolute/path/to/ProveIt
export LEAN_BIN=/absolute/path/to/lean-4.32.0/bin/lean
export COQ_BIN=/absolute/path/to/coq-8.18.0/bin
export K215_PACKET="$(pwd)"
export K215_BUILD=/absolute/path/to/empty/k215-reproduction
mkdir -p "$K215_BUILD"

git -C "$PROVEIT_ROOT" rev-parse HEAD
git -C "$PROVEIT_ROOT" status --short --untracked-files=no
```

The first Git command must print
`2ca3a5c16f0876d2cab842056353c03a1ed2f5f0`; the second should print nothing.
Use a separate checkout if your working branch has advanced or has local edits.
The scripts refuse a different baseline or, where stated, a changed source hash.
They do not change the supplied checkout.

Required source directories are `Computability/BusyBeaver/Lean` and
`Computability/BusyBeaver/Research/ZFC/k225-formal`. The dense-table hash refers to
`Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm`.

## 2. Rebuild the exact decoder/runtime closure and new Lean proofs

```sh
python3 code/check_uniform_decoder.py \
  --repo "$PROVEIT_ROOT" --lean "$LEAN_BIN" \
  --out "$K215_BUILD/lean-uniform"
```

This discovers the 23 original modules reachable from `KDecoderPrefix215`, compiles
all of them from source in dependency order, and then compiles `UniformDecoder`
and `UniformZipper`. It sets `LEAN_PATH` to the fresh output directory. The local
closure needs only Lean's bundled library; it does not need mathlib or a prebuilt
ZFC endpoint. Lean 4.32.0 is the validated version, with compiler commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`.

Expected result: 25 successful compiler exits and final JSON status `PASS`.
The script writes source hashes, commands, elapsed times, object hashes, and raw
compiler output to the output directory. `evidence/lean-uniform/` contains the
delivered run's records; compiled objects and the toolchain are intentionally omitted.

The concrete uniform decoder and zipper theorems report only `propext`,
`Classical.choice`, and `Quot.sound`. The generic source-path and prefix/tail rules
have the smaller reports printed in the logs. No new theorem uses `sorryAx`.

## 3. Check the standalone enumerator lemmas

```sh
"$LEAN_BIN" --root="$K215_PACKET/proofs" \
  -o "$K215_BUILD/OptionContracts.olean" proofs/OptionContracts.lean
"$LEAN_BIN" --root="$K215_PACKET/proofs" \
  -o "$K215_BUILD/FairSearch.olean" proofs/FairSearch.lean
```

All eight printed option-contract results and both finite-search results should
report no axioms. These are general lemmas, not already integrated enumerator proofs.
`none` in the intended finite execution represents actual halting; it must not be
interpreted as divergence. The separate halt-to-refutation invariant remains necessary.

## 4. Reproduce the decoder census

```sh
python3 code/decoder_prefix_census.py "$PROVEIT_ROOT" \
  "$K215_BUILD/decoder_prefix_metrics.json"
```

Expected status: `FINITE_SOURCE_AND_LITERAL_TRACE_CHECKS_PASS`. The audit checks
the exact pinned Lean decoder and table sources, all local windows, primitive
transition agreement, all source/role occurrences, and literal prefix runs. It
imports no repository generator. Key values are 4,751 leaves, 6,176 branch outcomes,
prefix clocks from 2 to 55, and a branch-weighted sum of 213,945 physical steps.
This is finite audit evidence, not a replacement for the kernel proofs or a runtime
benchmark of site checking.

## 5. Reproduce and inspect the import proposal

```sh
python3 code/import_boundary_proposal.py "$PROVEIT_ROOT" \
  "$K215_BUILD/import-proposal"
cmp patches/import_boundaries.patch \
  "$K215_BUILD/import-proposal/import_boundaries.patch"
git -C "$PROVEIT_ROOT" apply --check \
  "$K215_PACKET/patches/import_boundaries.patch"
```

The generator writes the patch, review copies, and source graph to the requested
output directory. It does not apply the patch. The projected local module counts
are 180 and 167; net source changes are -3,965 lines and -233,503 UTF-8 bytes.
Seven external library boundary names are unchanged. The moved declaration regions
are checked for verbatim extraction and hashed.

To incorporate it, use an isolated checkout and apply the reviewed patch there.
Before merging, compile the new cores and affected descendants, run both original
K215 endpoint clients and their assumption reports, and check historical clients
of the `ZFNative` and `WFModel` compatibility wrappers. Regenerate the L2 source
and inspect unexpected differences. **Those integrated kernel checks were not run
for this packet.** Textually preserving declarations does not by itself prove that
narrowed imports retain all instances, names, attributes and simplification lemmas.

## 6. Audit and compile the abstract implication proof

The structural audit is independent of Coq:

```sh
python3 rocq/check_and_render.py \
  --output "$K215_BUILD/DominatedImplication.rendered.v"
cmp rocq/DominatedImplication.v "$K215_BUILD/DominatedImplication.rendered.v"
```

To run the malformed-certificate controls and compilers without overwriting the
delivered receipts, copy the small Rocq folder into the reproduction directory:

```sh
cp -R rocq "$K215_BUILD/rocq"
python3 "$K215_BUILD/rocq/validate.py"
cd "$K215_BUILD/rocq"
"$COQ_BIN/coqc" DominatedImplication.v
"$COQ_BIN/coqchk" -silent DominatedImplication
cd "$K215_PACKET"
```

The three public results should print `Closed under the global context`.
The checker verifies 58 explicit substitution instances and rejects five malformed
certificates. The kernel, not the Python audit, is the authority for the theorem.

The numerical adapter pilot uses two hash-pinned arithmetic dependency sources
archived under the supplied baseline:

```sh
python3 "$K215_BUILD/rocq/verify_adapter.py" \
  --repo "$PROVEIT_ROOT" --coq-bin "$COQ_BIN" \
  --build "$K215_BUILD/adapter"
```

It compiles four modules and recursively checks `K215F.DomRho8` with `coqchk`.
The only compatibility edit for Coq 8.18 is `From Stdlib Require Import Arith Lia.`
to `From Coq Require Import Arith Lia.` in the adapter. The delivered modern source
is unchanged; the exact one-line patch is included. Source hashes and all compiler
outputs are recorded in the copied folder's `adapter_check.json`.

Production adoption requires the repository's Rocq 9.1/stdlib configuration and its
maintained dependencies, generator, module manifest, dependent proofs and endpoint
checks. Passing this focused Coq 8.18 pilot does not establish that adoption.

## 7. Build the report

TeX Live with `pdflatex`, Latin Modern, and the packages listed in the preamble is
sufficient. `make` runs enough passes to settle contents and references:

```sh
make pdf
```

The output is `report.pdf`; auxiliary files are under `.build-pdf/`. To render the
PDF for review, use `pdftoppm -png -r 110 report.pdf /path/to/pages/report` after
creating the destination directory. The delivered PDF was rendered and visually
reviewed. Regeneration changes PDF metadata and therefore its hash; refresh the
manifest if you deliberately publish a rebuilt packet.

## 8. Semantic-coverage integration not yet implemented

The report specifies `EdgeRealizes` and `SemanticCovered`, an adapter from the old
Boolean `Covered`, and a second prefix-plus-tail producer. The implementation must
retain the exact targets, both decrement outcomes, `consume` zero padding, arbitrary
natural gaps, validity and spare-tail conditions, overflow behavior, and positive
physical progress. `UniformZipper.prefix_tail_sound` supplies the proved composition
rule. The generic producer and production site migration remain the next change;
there is no claim that the supplied patch implements them.
