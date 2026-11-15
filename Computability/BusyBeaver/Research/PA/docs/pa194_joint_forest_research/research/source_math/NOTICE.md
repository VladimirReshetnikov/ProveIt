# Source-search provenance

The starting C++ scorer is the exact file `Computability/BusyBeaver/Research/PA/docs/pa194q_conpa_2026-11-13/search/screen.cpp` at ProveIt commit 7c0bb454cf73c29ca1c385f9fec856ddd236a7cb (SHA-256 45fd39723955a367bbcd1c3e4f33673320596636ce60d0bf7b4ed5dcaa5bffc5).

The starting annealer derives from `Computability/BusyBeaver/Research/PA/docs/pa194_ax11h_research_2026-11-14_2/research/joint_grammar/joint_ax11/search.cpp` at the same commit; its only initial changes disable both parameter-renaming branches, because the transformed words have different head boundaries. All subsequently added source-tree generators, global macro adapters, ingress filtering, broader fixed-control matching, and neutral-frontier exploration are retained here.

The source and literal fixed rows for the global experiments are root's A0M0L3 family. Its two useful internal patterns are `(node55,node65)` and right-associated three increments. The all-control extension establishes the predecessor-bit context from the *written* bit of every right-moving ingress. It also includes the blank initial predecessor bit 0 for start control 74. Every candidate fold is tested simultaneously on all of its two-cell contexts. Search scores remain finite diagnostics; no whole-machine or iPRA calibration is inferred from a low score alone.

`make_many_padding.py` re-reads the pinned repository's grammar JSON files. Its 97,361 initial templates and 1,085 source shapes are reproducible from that corpus; the large generated template file need not be redistributed if these dependencies are retained. All negative results concern only the displayed bounded searches.

For the portable research package, the small generator inputs were copied into `inputs/`, while corpus-wide regeneration uses the explicit `PROVEIT_ROOT` environment variable. The two parameterized-generalizer grammars come from `docs/incoming/pa194_ax11hc4_c32_research_2026-11-15.zip` at the same pinned commit. Exact input hashes and the paths changed during packaging are recorded in `provenance/portable_inputs.json`. No captured search templates or C++ algorithms were changed during this relocation.

The original code's copyright and license remain those of the pinned ProveIt research packet and its retained upstream attribution.
