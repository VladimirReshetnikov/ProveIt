# Independent ordinary review of the current cap helper reflection

Reviewed by intake_e13 on 24 October 2026. The full 130-line proof, complete
binding and source pins were independently read. **Ordinary mathematical
approval: no finding.** The current result retains F, the direct positive
cap graph and the complete cap-in-pool term. It does not silently compose
the separate F deletion or unoriented-cap proposal.

The exact reviewed files have SHA256:

| File | SHA256 |
| --- | --- |
| PROOF.md | 7a63b5da6a86cf6ef769665c7d9e5b0c945b44035f2ea5c4bbfed92c1e639f6c |
| BINDING.json | 20b5490c2ae1351308ee68d5ec8bcbcd9baf489eb2a7c19c5cf59eb661220780 |
| SOURCE_PINS.json | 8815fb0b646e98c5b18040060cc828016987387a751944b37b04fd39c93fcbc9 |

All ten external whole-file pins and both own-core pins authenticate. The
source is the exact sealed current cap body, with402 coordinates and335
rows, rather than the former522-coordinate Round15 body. Its old product
coordinate is absent, so copying the earlier five-coordinate reflection
would be incorrect. The proposal uses exactly these four coordinates:

    V251 -> -V251, d252 -> -d252-2,
    H254 -> -H254, e375 -> -e375-2.

An independent inert sparse substitution verifies all402 coordinate
involution identities, every one of the335 row identities and the complete
body sum-of-squares coefficient identity. Only rows205 and323 change sign.
The complete actual occurrence lists are exactly those in the proof and
binding. In particular the replacement of V's old product by Ccap^2 is
handled by reflecting e375, while keeping Ccap and its square gate fixed.

The complete domain list agrees with the binding. All37 guard triples are
pairwise disjoint and each auxiliary occurs only in its own graph in the
whole guarded equation. The only two predicate expressions touching a
changed coordinate are original27 and30, actual rows361 and362 with
private triples480..482 and483..485. Every other expression is fixed.
Both cap graphs, all cap rows210..219, the pooled row and frame are fixed.
All37 recorded frame atoms and all18 actual base/exponent/output interfaces
agree with their original complete binding and are coefficientwise fixed
by the four-coordinate reflection.

The normalization is acyclic and needs no Pell semantics. The new graph
gives v255>=4. The unchanged exact row207 then gives V(d+1)>0, excluding
V=0. If V>0, integrality gives V>=1,d>=0 immediately. If V<0, reflection
makes both V and d+1 positive, so the same integer inequalities hold. The
norm gate H must change sign, and row323 must change sign through e's
affine reflection; the proof includes both changes. Every other body row
and retained graph remains satisfied with its original witnesses.

Fresh old Legendre triples now restore d>=0 and V-1>=0. Only after this
restoration is the accepted entire cap theorem invoked. No earlier cap,
F, positive-index or orientation conclusion is used to normalize its own
helper premises. In the converse, an original zero has V>=1,d>=0, so
row207 gives v255>=4 and a fresh new triple exists. The entire body is
kept in that direction, and the six old private helper witnesses are
forgotten. The inverse may reflect four private body coordinates; no
whole-body pointwise identity or guarded-witness bijection is claimed.

The possible future composition orders are correctly stated as separate
obligations: normalize and restore the helper signs first, then invoke
the matching approved F or different cap theorem. The four-coordinate
reflection fixes their relevant semantic interfaces, but that alone does
not emit or bind a combined source policy.

Only read-only standard-library hashing and inert collection of identities
on the accepted JSON were used. No author module, incoming program,
source generator, optimizer, compiler, projected equation or Lean command
was imported or executed. The author folders, all frozen packets and
canonical PDF/TeX were left unchanged. A future implementation still
requires its own complete guard/coordinate maps and finite replays.
