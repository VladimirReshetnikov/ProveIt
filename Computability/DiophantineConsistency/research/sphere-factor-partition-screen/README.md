# Five-factor sphere partition screen

This is a bounded arithmetic screen of one family of literal constructions on the 62-row prefix of the checked 71/80 sphere. The available factors are `P=N0`, `Q=N1`, `U`, `W=Nt`, and `Z`, with exact witness degrees 22, 18, 30, 2, and 34 from the pinned existing degree certificate. For each of the 52 set partitions into nonempty blocks, it constructs the prescribed *shape*: multiply each block's factors, square each product, subtract one before squaring the block containing `W`, sum the squares, then subtract the number of other blocks (omitting that final subtraction when it is zero). Products within blocks are formed independently; no other algebraic rewriting or gate sharing is searched.

Counting every binary operation in that explicit scheme gives the following optima conditional on the pinned factor-degree certificate:

| Blocks | Partitions | Operations | Minimum degree |
| --- | ---: | ---: | ---: |
| 1 | 1 | 68 | 212 |
| 2 | 15 | 70 | 108 |
| 3 | 25 | 71 | 80 |
| 4 | 10 | 72 | 68 |
| 5 | 1 | 73 | 68 |

For example, the existing 71/80 equation uses blocks `{P,Q}`, `{U,W}`, and `{Z}`. The 70/108 optimum is dominated by the separately checked 67/106 integer graph; the 68/212 shape is dominated by 65/150. The other minima reproduce or are dominated by the 71/80 and 72/68 profiles.

The degree formula is exact for this family: each block product has the sum of its nonzero factor degrees, and the highest homogeneous part of the whole expression is a nonempty sum of squares of nonzero real polynomials, so it cannot vanish identically. This uses the specialized factor-degree certificate; it is not a new Lean degree theorem. The operation count is for the stated unshared construction, with its 62-row common prefix, rather than the minimum possible circuit for the resulting polynomial.

No equation in this screen is asserted to have the required zero set: extracting individual norm signs from a grouped product can require additional proof. In particular this does not settle the separate `W=-1` issue of the proposed 70/80 expression. It is not a global lower bound and does not rule out other witness maps, operations, identities, degree cancellations, prefixes, or gate sharing.

Run from the repository root:

```
python3 -I -S -B Computability/DiophantineConsistency/research/sphere-factor-partition-screen/check.py
```

| Artifact | SHA-256 |
| --- | --- |
| `check.py` | `4d2c0d070bccc0e95f731395f1a12268cfdf55a0b32761935a16b8e9877da97f` |
| `result.json` | `6fcefc6496055f132b01c31e45fdf75f0231d59f1006a5899bded4370de54904` |
| pinned `CERTIFICATE.json` | `99a901c08cd45b549a638ddd051ce80a0bf7a833231b52bc2b29d5390feb37ec` |
| pinned `polynomial71.json` | `937752350556a94539584db8f646ff9e02d25a7113e6d4af70ac22c1b1e01ad2` |
