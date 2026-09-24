# Random selection and exclusion record

An ordered list of 80 areas was created before selecting a problem.
The original computation called `secrets.randbelow(len(areas))` once.
It returned 17, the zero-based index of **Functional equations**, item 18.
There was no redraw. `data/selection.json` contains the complete list,
the method, the index, and the selected area.

The generator draws from operating-system entropy. There is no claimed
replay seed; a fresh draw need not return the recorded result.

The user-supplied `manifest(1).tex` was read in full: 1,095 source lines
cataloguing 71 research packages. Its SHA-256 is:

    729fb6e3aef3f30c7c5284c4296681fba72b6d6af68211f178ad0bc3c5d15b41

The selected target is Draga–Morawiec Problem 6.1 on deleting nonreal
maximal-modulus roots from polynomial iterative equations. No entry of
the supplied manifest targets that problem. The report does not reuse
one of the manifest's problems about compositional generating series,
tetration, transfinite operations, or other listed objects.

Reviewing the manifest as an exclusion list is not an independent check
of the correctness or priority of its mathematical claims. The original
input is not modified or included in this archive. `manifest_entry.tex`
is a suggested new entry, not an automatic update to the user's manifest.
