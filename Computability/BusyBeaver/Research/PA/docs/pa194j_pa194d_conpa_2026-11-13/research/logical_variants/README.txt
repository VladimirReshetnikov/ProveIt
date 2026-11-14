Logical emitter research inputs
================================

The five new proposals are h1D, h2D, h6outerD, separateD, and separateH.
h1A, h2A, and h6innerD are prior-art controls retained for comparison.

new_transfer_words.py independently executes every complete macro word in
a free term algebra and checks the whole emitted stack, gate, parameter
reads, and guard. It uses the frozen old grammar in construction/inputs/.
Run with Python 3.10+ and assertions enabled:

  python3 -B research/logical_variants/new_transfer_words.py
  python3 -B research/logical_variants/source_words.py

These direct commands regenerate files in this directory. Run in a copy
if preserving the supplied SHA256SUMS matters. source_words.py resolves
balanced source associations using the bundled source-language routines.
Its counts refer to the original uncached controller, so separateD has
3,673 sites here; the accepted cached PA194D has 3,649 sites.

The .word.json files give exact formulas and macro tokens. The .balanced
files are primitive source graphs, not certified physical allocations.
The .adapted194 files and adapted194_seed_receipt.json record an early
unsuccessful direct substitution into the old 194-state association.
Its matching score was only a heuristic bound, not a simultaneous-fold
certificate. The later accepted winning association is in:

  logical_emitter/inputs/winner.grammar.json

Only separateD is delivered as a fully independently checked 194-state
physical machine. The other four new logical proposals remain research
inputs. Their equiconsistency arguments do not imply a smaller machine.

The full PA194D selector, strong all-store proof compiler, zero-invariant
transfer, and consistency theorem appear in report/supplemental_gammad.tex.
The text proof notes here retain additional derivations for the remaining
logical proposals and explicitly distinguish prior art.
