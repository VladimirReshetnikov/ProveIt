# Identical-polynomial transport contraction

`zero98.json` has ten positive inputs, 98 live operations and exact degree
368. `direct103.json` has ten positive inputs, 103 live operations and
exact degree 340. These improve the accepted 99/368 and 105/340 graphs
without changing either polynomial or any witness. This is an ordinary
research packet; no frozen endpoint or canonical page has been changed.

Expanding `W=1+gL` lets the integral `L*B` term enter the center beside
`n+V`. It deletes three gates and inserts two. The direct graph also
reuses its existing `q*(q-1)` product in `P=q^3*[q*(q-1)]`, deleting
the private `q4` gate. See `PROOF.md` for the unbounded argument, and
the complete `*_CUTS.json` maps for every literal parent definition.

The producer's `--check` mode rebuilds all graphs, row maps, copied inputs
and BUILD.json in memory and compares every byte without writing. The
independent checker binds its proof, builder and all complete source inputs;
when MANIFEST.json is present it also checks its closed file inventory and
every member hash. All four release commands pass:

```sh
python -B Computability/DiophantineConsistency/research/ten-positive-expanded-transport/build.py --check
python -B Computability/DiophantineConsistency/research/ten-positive-expanded-transport/check.py
python -B -O Computability/DiophantineConsistency/research/ten-positive-expanded-transport/build.py --check
python -B -O Computability/DiophantineConsistency/research/ten-positive-expanded-transport/check.py
```

No imports from emitters or authentication dependencies are used. The
complete original coefficient tuple is copied byte for byte; copied
parent proofs and the live accepted parents are SHA-256 pinned. Exact
polynomial identity inherits all ordinary soundness/completeness steps,
coherent tuple handling, and exact degree certificates from the parents.
The normal and optimized rebuild/check logs are in `verification/`.

