# Parametric four-byte assembly

`FourByteGeneric.assemble` is a Lean theorem for arbitrary four natural-number lists and an arbitrary `Fin 4 → ℤ` port tuple: if each list's reversed natural base-256 decoding, cast to integers, equals the corresponding port, then the function decoding all four lists equals the port tuple. It contains no closed beta, K or mask byte recipe and proves no file-content claim.

Attempt01 passed: actual outer session 38757 exit 0, Lean exit 0, `[propext, Classical.choice, Quot.sound]`, 685 stable recorded guard slots and no stop. The object `/tmp/current2011-four-port-byte-generic-check01/FourByteGeneric.olean` has SHA-256 `a56873fdf83e80abd3c5233b6fff93919af0e28d116fe86acd092143d61411eb`. Child receipt and actual outer observation are retained separately. The guard uses Lean `-M2800`, one worker, nice 19, idle I/O, 120 seconds, sampled group-RSS stop at 3.5 GiB and host available-memory stop at 10 GiB. Direct/provider guards inherit the transitive base and are not a complete dynamic load trace or independent rebuild.

| Artifact | SHA-256 |
| --- | --- |
| `FourByteGeneric.lean` | `07ad651c97ebc529cc83c4bcd119341e2e5ef4db7661995cee547e4a5cea7123` |
| `check01.py` | `85a569cf8a353e5d74cc2e83442dfb2d7941701314321aa34db277a358ff8745` |
| `attempt01/result.json` | `c81f781229683a3cd117379938b82d9c69bed1bdc1b0b325b8458d5359f76552` |
| `attempt01/outer-observation.json` | `a82f864626fed466454c054a83fbfdb6fa9243d566e4af29465dfcc23aa4fca2` |
