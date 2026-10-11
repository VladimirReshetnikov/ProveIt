# Source audit and provenance

## Observed repository revision

`74206207617254448a1992dc76cd6dd84987ff59`

This was read from the GitHub `commits/main` endpoint during the research session. Its recorded commit time is 2026-10-11 00:15:21 UTC, which is still 10 October in the user's Pacific time zone. Initial manuscript and directory reads used the default branch before this revision was recorded. The repository was evolving during the session; this is a targeted read with a recorded reference revision, not an assertion of an exhaustive immutable checkout.

## Actual manuscript reading

- `Analysis/Polylogarithms/docs/manuscript/polylogarithms.tex`: complete driver and preface.
- `Analysis/Polylogarithms/docs/manuscript/chapters/10-discovery.tex`: full returned chapter, including surviving questions and the frozen S8 rejection.
- `Analysis/Polylogarithms/docs/manuscript/chapters/07-integration.tex`: requested lines 1–230, including Hurwitz/Gamma primitive conventions and correction scope.
- The manuscript and `docs/incoming` directory metadata were inspected. Not all listed files or archives were read.
- Relevant Library search results were used to locate the newest periodic collision and contact reports and their exact coordinate-transport research questions. Earlier Gauss/Dougall/nested-harmonic reports were reviewed at summary/search-snippet scope for topic overlap only, not treated as fully audited manuscripts.

## Byte-matched incoming archives

The GitHub connector returned their incoming-directory Git blob hashes but did not supply binary downloads. Identically named Library archives were materialized and their **Git blob hashes were recomputed from the actual bytes**, including the `blob <size>\0` header. Both match the repository listing:

| Archive | Bytes | Verified Git blob SHA-1 |
|---|---:|---|
| `ProveIt_Periodic_Collision_Contacts_2026-10-10.zip` | 467928 | `57b31b66e07ebb684258ca8636eab756b6e40f51` |
| `ProveIt_Periodic_Stieltjes_Contact_2026-10-10.zip` | 434079 | `f48a0fb812c810fb8a77e1f827a5e0d2282e7fdb` |

Machine-readable SHA-256 values and comparison records are in `data/source_provenance.json`. The original archives are not redistributed in this continuation.

The first archive's `Periodic_Stieltjes_Collisions.tex` was inspected in the local definition/theorem context, especially lines 136–271, the Fourier/extension interface, the contact-scope safeguards and lines around the nonlinear-coordinate research question. This confirms the sign convention, full `P_p(t)` correction, density/distribution distinction, and original scope. The second archive was located, byte-matched and extracted; its selected results and research questions were read via Library text retrieval, but its entire proof corpus was not independently re-audited or re-executed.

## External primary references

- NIST DLMF 25.11: Hurwitz shift, Fourier expansion, parameter derivatives and `zeta'(0,x)`.
- NIST DLMF 25.12: polylogarithm conventions and analytic continuation.
- NIST DLMF 5.5 and 5.7: Gamma reflection and Taylor coefficients.
- Giovanni Felder and David Kazhdan, *Regularization of divergent integrals*, arXiv:1611.05057v1. The full HTML was retrieved and the regularization-change theorem and boundary discussion inspected. General finite-part change-of-regularization theory is credited as prior work.
- Ricardo Estrada and R. P. Kanwal, *Regularization, pseudofunction, and Hadamard finite part*, JMAA 141 (1989), 195–207. Publication metadata was verified through the Louisiana State University repository. This was a metadata-level attribution, not a claim to have read the full paper.

No exhaustive priority investigation was performed. The article's formulas are established with proofs, but the delivery does not certify their first appearance in the global literature.
