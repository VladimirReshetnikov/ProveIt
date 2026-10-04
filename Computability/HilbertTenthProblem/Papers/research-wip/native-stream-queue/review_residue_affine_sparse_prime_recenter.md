# Independent review of U21 prime-selector recentering

**PASS; no correction requested.** I read the full author helper and proof,
the full immediate-parent joint-recoding proof, and the authenticated full
parent/child arrays and actual U21 table. A fresh independent checker
reconstructs both complete sources and proves their whole polynomial
identities. No author or predecessor helper was executed or imported.

## Frozen author reviewed

| File | SHA-256 |
|---|---|
| `residue_affine_sparse_prime_recenter.py` | `c5d8b2690f1e2a9b50aa063a95f81297ff388b276ab83ce487aa4cbaacc46798` |
| `residue_affine_sparse_prime_recenter.json` | `e35399b892850ace2bf860fd37f0e3e9f8af34dd8e516f66718547e0689fe26c` |
| `residue_affine_sparse_prime_recenter.md` | `78e81a12145ecf2b5b57fecdbef614cafa2a96ff0b86e488c4479546914c108c` |

The immediate-parent trio is `residue_affine_sparse_joint_recoding.*`,
pinned at PY `386f00228dd250a1c582a3bf93724e9732db71cdd8d4fea6828d0b78d06fe443`,
JSON `a3b00883d84e7c8e9a6aea04ec3e54776fe927f7193f60a04050246f32039284`,
MD `16d4a9e60343eb4f8f4ee78e8d60e7aeb2ee73b8d045241dd4951e124cf7b404`.
The separately authenticated `residue_affine_sparse_factored.json` is
`39e52871ae5137f8edd111055e6338db4bf17b232d145a24390b1675d8c99fda`.

## Independent findings and validation

The proposed identity is valid in the actual supplied hats, including
constant terms:

    G17 = E5+E8+E9+E14+E15,
    A3  = E5+E8+E9,
    D9  = E14+E15,
    D14 = E24+E25,
    17G17+D9+D14 = 18G17+D14-A3.

G17, A3 and D14 are already paid in the retained noncontrol base. The
literal old private-consumer map permits deleting exactly `joint_1` and
`joint_2`. The fresh subtraction restores the old `joint_21` value;
`joint_22` and all downstream values agree. Exactly the five recorded
retained affine prefixes differ: `joint_8,18,19,20` each increases by G17,
and `joint_21` increases by A3 before the new subtraction. Their signs
impose no new witness restriction because they are computed registers.

The fresh checker independently reconstructs all **931 rows**, checks
acyclic scheduling and complete row/port liveness, and obtains:

| Interface | M | A | Full operations | Positive witnesses | Degree upper bound |
|---|---:|---:|---:|---:|---:|
| One program |171|295|466|67|5091|
| Two program |171|294|465|67|5160|

It independently reconstructs the actual 36-edge table from the saved
21-instruction program and verifies the unchanged 23 injective codes,
maximum40, loader0 and halt14. All old/new current/target vectors are
expanded through all36 supplied hats. The four vectors per interface
include their exact constant terms. The paid current/target union is
59=20M+39A, including the sole shared `29*D11` product once.

Exact 37-entry affine normalization, bound to the actual hat definitions,
is embedded in an independent expression-DAG interpretation of every
source row. This proves full output equality and equality of all
460/459 retained computed values outside the five stated exceptions.
A supplementary expansion of each full output at the actual hats and
proved-equal nonlinear boundaries matches all2039 terms. The complete
finalizer also expands to U*(1+sum of six residual squares)-1. No unbound
cut or hash collision assumption substitutes for an identity proof.

All389/388 retained base rows, all72 native rows and all20 comparison/
finalizer rows are literal. The height/radix recipes, supplied parameters,
67 witnesses, control interfaces and all other packet metadata are
unchanged. The fresh degree check expands the seven-term main-norm
cancellation, obtains bounds816/827 at the actual computed cuts, and
propagates5091/5160 through the complete sources. These are upper bounds,
not exact-degree claims; naive propagation gives5157/5227.

Since the complete polynomials are equal, the supplied positive zero sets
agree by the identity map within each interface. No new native bootstrap,
chronology argument or witness reselection is needed. The inherited
one-program recipe E=3^e, B=64(E+x+eta), and the two-program recipe
E=3^e, dyadic C>=64 with C>E, B=C(x+eta), remain distinct. This review
claims neither a positive-coordinate map between them nor a theorem on
invalid fixed slices. It does not establish a new global minimum or
improve the separate complete84 result.

## Repeatable review evidence

The independent [checker](review_residue_affine_sparse_prime_recenter.py)
and [receipt](review_residue_affine_sparse_prime_recenter.json) use strict
JSON, source bindings, explicit optimization-safe guards and exclusive
receipt creation. Writer and fresh normal/optimized exact replays from `/`
passed. Only the new review helper executed; no numeric history fixture or
new native tuple was generated, and no repository file was edited.

Reviewer PY SHA-256:
`d5fed30a745c1d321c8e311dbf7482681423e037354743c5c48f9a79d92c4e60`.
Reviewer JSON SHA-256:
`1f786de6154f342005547687123e34472a8f4eb8877dce4d95b3952e30809465`.

```sh
python3 /tmp/review_residue_affine_sparse_prime_recenter.py \
  --root ABS_WIP --author-root /tmp \
  --expect /tmp/review_residue_affine_sparse_prime_recenter.json
python3 -O /tmp/review_residue_affine_sparse_prime_recenter.py \
  --root ABS_WIP --author-root /tmp \
  --expect /tmp/review_residue_affine_sparse_prime_recenter.json
```
