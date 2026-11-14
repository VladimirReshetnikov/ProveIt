THEORY AND ATOMIC-ORIENTATION RESEARCH ARTIFACTS

Repository snapshot:
  https://github.com/VladimirReshetnikov/ProveIt/tree/5784600f8709872fa258af66a94df8deb7075c2f

RESULT AND SCOPE

This directory contains a new admissible-source-entry lemma, a partial
proof-store certificate generator, and reproducible records of a bounded
atomic-orientation search. It does not contain a verified blank-start
machine with fewer than 194 states. A nominal reader score is not a
complete machine certificate or a proof of a new calculus calibration.

The startup lemma accepts source sites 25 through 44, with logical
registers (N,T,W,A,D,H,S,R,L) = (N,0,0,A,D,0,S,R,L), where all six
non-proof values are arbitrary natural numbers. A caller must additionally
verify a complete physical runtime frame. For HAZ the logical-to-physical
map is [6,2,0,3,4,7,8,5,1]; therefore only physical slots 0,2,7 must be
zero under the simplest criterion. The primary PA194 allocation swaps
A and D but has the same three required zero slots.

The paper first proves cofinality from arbitrary clean counter and
continuation values. Every accepted dirty prefix then reaches the same
full source configuration as a suitably chosen ordinary clean fetch.
Determinism transfers halting. This is an ordinary mathematical proof
formalizable in PA, not a newly compiled end-to-end Lean theorem.

FILES

  startup_seed_lemma.tex     Standalone article with the complete proof.
  startup_seed_receipt.json  Checked source slice, site paths, register map.
  theory_audit.tex           Includeable logical-calibration audit section.
  seed_truth.py             Partial syntactic PA-proof-template recognizer.
  transpose_inputs.py      Portable exact 190-token search-seed generator.
  audit_orientation_search.py
                            Checks each saved word against the permitted
                            explicit formula-emitter family, reconstructs
                            run summaries from logs, and compares the
                            result with search_summary.json.
  baseline.grammar.json     Expanded baseline association fixture.
  fixed_readers.txt         The 134 inherited fixed runtime rows.
  leaf_attrs.txt            Inherited leaf attributes for the scorer.
  mode0.txt ... mode3.txt   32 seed grammars per orientation, with fixed rows.
  transpose_inputs.json    Metadata for all 128 exact seed words.
  search_plateau.cpp        Inherited association/parameter search driver.
  screen.cpp                Inherited compatible-reader scoring code.
  orientation_anneal_retained.cpp
                            Driver variation retaining nearby good seeds
                            above the old absolute score-62 pool threshold.
  transpose_mode*.log       Original bounded-search records.
  retained_mode*.log        Records for the seed-retaining variation.
  *.best.grammar.json       The six saved best witnesses, independently
                            checked by audit_orientation_search.py.
  search_summary.json      Completed and interrupted runs distinguished.
  portable_validation.json Validation performed after removing repository
                            and absolute-path dependencies.
  provenance.json          Imported source locations and SHA-256 digests.
  SHA256SUMS               Digests of the included files except this list.
  LICENSE.*                Notices for inherited code.

REPRODUCE THE FINITE AUDIT

Run from this directory using Python 3; only the standard library is used:

  python3 audit_orientation_search.py --output audit_result.json
  python3 transpose_inputs.py --output regenerated
  cmp mode0.txt regenerated/mode0.txt
  cmp mode1.txt regenerated/mode1.txt
  cmp mode2.txt regenerated/mode2.txt
  cmp mode3.txt regenerated/mode3.txt
  cmp transpose_inputs.json regenerated/transpose_inputs.json

The generator's portable form inlines the small grammar helpers formerly
imported from the repository; all five generated files were compared
byte-for-byte with the original experiment inputs. The witness audit
checks exact emitter syntax and the recorded scores, not a new execution
of the C++ scoring algorithm or a literal TM simulation certificate.

The partial startup-store recognizer takes one JSON object on stdin:

  python3 seed_truth.py <<'JSON'
  {"pc": 44, "logical_registers": [100, 2, 6, 91, 17, 3, 23, 29, 71]}
  JSON

Alternatively use physical_registers instead of logical_registers; the
HAZ allocation is then applied. The script emits finite proof-template
trees. It rejects unknown formulas rather than deciding all PA theorems.
Its optional broader certificates use PA derivations directly and do not
claim source-calculus derivability unless those annotations are supplied
separately. It does not inspect tape markers, source paths, padding, the
complete register-file encoding, or spare-register tails.

OPTIONAL SEARCH REBUILD AND REPLAY

  g++ -O3 -std=c++17 search_plateau.cpp -o search_plateau
  g++ -O3 -std=c++17 orientation_anneal_retained.cpp -o orientation_anneal_retained

The driver arguments are input-file, leaf-attributes, output-prefix,
wall-time budget in seconds, and random seed. Store new output under new
prefixes so the delivered evidence is preserved. For example:

  ./search_plateau mode1.txt leaf_attrs.txt new_mode1 180 781337 > new_mode1.log
  ./orientation_anneal_retained mode1.txt leaf_attrs.txt new_retained1 420 782331 > new_retained1.log

Original runs:
  transpose_mode1: mode 1, seed 781337, budget 180 seconds, completed.
  transpose_mode2: mode 2, seed 781332, budget 180 seconds, interrupted.
  transpose_mode3: mode 3, seed 781333, budget 180 seconds, interrupted.
  retained_mode1:  mode 1, seed 782331, budget 420 seconds, completed.
  retained_mode2:  mode 2, seed 782332, budget 420 seconds, completed.
  retained_mode3:  mode 3, seed 782333, budget 420 seconds, completed.

Modes independently transpose equality (bit 0) and membership (bit 1).
Every mode has eight curried-premise exchanges and four separation-matrix
spellings. The original mode-2 and mode-3 processes were killed with exit
status 137 and have no DONE record; their last recorded iterations are
partial evidence. The three retained 420-second searches completed.

The inherited search holds a large hash-consed expression arena. Its
periodic compaction condition can be skipped by an earlier continue, and
it can consume substantial memory. No repaired compaction variant was
used for the recorded results. Wall-time stopping makes iteration counts
hardware-dependent even with the supplied random seeds. These bounded
searches establish neither optimality nor a lower bound.

Best nominal totals were 198/197/199 for the original modes 1/2/3 and
197/199/199 for the retained modes 1/2/3. The unchanged baseline scores
194 = 134 fixed rows + 60 effective reader rows. None of these searches
found a smaller candidate, and the changed coding's freshness guards
would still need a separate PA-calibration proof for any future success.

To typeset the standalone note:

  pdflatex startup_seed_lemma.tex
  pdflatex startup_seed_lemma.tex

The main research report also includes its text. See the note and
provenance manifest for the source files supporting its inherited lemmas.
