# Area selection and exclusions

The fixed list contains 96 distinct areas. A single `secrets.randbelow(96)`
call selected zero-based index 9, one-based entry 10, “Permutation patterns”.
The recorded UTC timestamp is 2026-09-20T21:58:38.955311+00:00. The full ordered
list and the draw are in area_selection.json. No area redraw was performed.
This is an ordinary executed audit record, not a tamper-proof external lottery.

The supplied manifest's SHA-256 is:

    729fb6e3aef3f30c7c5284c4296681fba72b6d6af68211f178ad0bc3c5d15b41

The 71 manifest entries were read in full. The selected PAP reverse-reply
conjecture is not one of them. In particular:

- A000139 / two-stack-sortable permutations concerns parity and valuations of
  an enumerative formula, not the PAP game.
- Adjacency-bounded 132-avoiders concerns growth constants and their strict
  increase, not the PAP game.
- Stabilized permutation-weight series concerns rationality and asymptotics,
  not the PAP game.
- Ordinal Chomp, point-separating games, and open-query games use different
  positions and rules and do not address PAP.

No manifest result is used as a theorem in the present proof. The exclusion
check does not endorse or independently verify the manifest's claimed proofs.

The initially considered stack-sorting target was rejected after a later
solution was found; see SOURCES.md. Investigation then stayed within the
randomly selected area and selected Ulfarsson's Conjecture 2.9.
