FULL REPLAY PROVENANCE

The unedited replay.json and logs record the complete offline run of
reproduce.py --full on 2026-10-19. Both fresh symbolic runtime derivations
passed, with byte-identical case arrays. The fresh runtime receipts and
case arrays are delivered one level above this directory.

input_manifest.json is the pre-publication input inventory that this run
checked. Its hash agrees with replay.json. It is retained as a historical
execution record; it is not the release inventory. Report typesetting,
README completion, and collection of fresh receipts happened during or
after that run. The root manifest.json inventories the final release.

unchanged_proof_input_pins.json checks that the executable code, source and
machine inputs, construction data, and runtime case arrays used by the
full run retain their pre-publication bytes. In particular, neither proof
engine nor the final machine or source changed after the full derivation.
The final ZIP is also extracted and replayed in quick mode before delivery.
Run --full yourself to regenerate all runtime proofs against the release
inventory; no network or Rocq installation is needed for that Python run.

Absolute paths and elapsed times inside original execution logs describe
the producing environment only; they are not replay dependencies.
