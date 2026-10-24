# Raw100-guard low-height integer quartics

Keeping all original1259 body coordinates and adding the frozen100-guard
set gives a complete1559-integer quartic of coefficient height427.
Fresh signed projections give912/767/703/689 integer unknowns, with
heights4750/737653/737653/938261. Every exact degree is4.

All592 original affine recipes and all100 guard triples give a literal
integer zero-set bijection with the frozen967 equation. No fresh
witness or sign premise is used before constructing that target zero.
See [PROOF.md](PROOF.md) for the full argument and counts.

From the repository root:

```sh
python3 -B Computability/DiophantineConsistency/candidates/retained-radius-mixed-orbits/build.py --check
python3 -B Computability/DiophantineConsistency/candidates/retained-radius-mixed-orbits/check.py
python3 -B -O Computability/DiophantineConsistency/candidates/retained-radius-mixed-orbits/build.py --check
python3 -B -O Computability/DiophantineConsistency/candidates/retained-radius-mixed-orbits/check.py
```

Every full coefficient list and integer inverse certificate is stored.
Frozen candidates, common documents, equation pages and Lean files are unchanged.
