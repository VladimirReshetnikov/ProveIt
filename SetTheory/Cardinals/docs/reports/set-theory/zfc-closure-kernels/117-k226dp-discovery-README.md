# Discovery records

These files explain how accepted transformations were found. They are not
dependencies of the ordinary mathematical calibration of K226: the main
replay checks the literal resulting source, machine, and unbounded runtime
contracts independently of the layout search.

## Accepted 49-atom layout

Run from the archive root, using Python 3.10 or later:

```sh
python3 -B discovery/discover_layout227.py --output /tmp/k226-layout.json
```

The ordered interval dynamic program reads `layout_problem227.json` and
retains two predecessor bits and the trailing zero-run constraint. It
reconstructs the accepted layout with weighted entry-depth cost 26,568,
compared with 27,716 for the earlier parenthesization. Its cache contains
9,284 subproblems. `layout_replay.json` records the separate replay from
the completed portable package; `boundary49_layout.json` retains the
original discovery receipt. The optimization claim is restricted to
this fixed ordered set of atoms, stated feasibility predicates, and
weighted-depth objective. It is not a minimum-state theorem.

## Unsuccessful additional searches

`search_below226_receipt.json` records a restricted search from K226 through
one, two, and three compatible closed rotations. The C++ files and their
logs preserve earlier neutral-block and correlated-window helper searches
on the direct K228 companion. These finite searches found no additional
accepted state saving in their respective families. They impose no lower
bound on arbitrary constructions or encodings of consistency.

The discovery logs may contain original working paths and elapsed times;
the portable accepted construction is in `../verification/reconstruct227.py`
and `../verification/reconstruct226.py`.
