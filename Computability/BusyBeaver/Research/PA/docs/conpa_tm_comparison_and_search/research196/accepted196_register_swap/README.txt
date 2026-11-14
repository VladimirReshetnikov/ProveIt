This is a 196-state alternative, not a solution to the requested state bound.

The physical locations of abstract registers A and D are exchanged. Exactly three transition targets change. The literal numbering, start 0, and halt 196 are inherited from pinned PA196.

All4,959  symbolic source-step contracts pass with the new register interpretation. A literal blank-tape execution reaches the exact clean frame with candidate 2 at physical slot 6 after 58,122 steps. These are Python checks, not a newly kernel-checked Lean development.

Reproduce with research196/verify_register_remapping.py, supplying --core and --source if the archive is relocated. See manifest.json for exact changed rows and hash.
