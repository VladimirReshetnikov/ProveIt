# Historical beam replay

These local modules preserve the pre-fix allocator and helper cost used in the completed depth6 beam recorded by ../helper_beam.log. They are for reproducing that historical finite search, not for certifying or constructing a delivered machine. Use research_sub221/calculus/compile221.py for current corrected allocation.

Run from /workspace/scratch/416780682817:

    python research_sub221/grammar/replay_legacy/beam_helpers.py --depth 6 --beam 200 --cost 222 --output research_sub221/grammar/replay_beam_output

Expected completed census: depth6,171357 generated source roots seen,885428 interned tree nodes,9875 final eligible successors,200 retained; no220 hit. Wall-clock timestamps may differ. The completed run did not save an in-memory frontier checkpoint; this deterministic replay bundle preserves its inputs and implementation rather than claiming an unavailable checkpoint exists.

The historical compiler deliberately lacks the later dynamic alias dependency correction. The failed first12 projected221 allocations must not be presented as valid machines.
