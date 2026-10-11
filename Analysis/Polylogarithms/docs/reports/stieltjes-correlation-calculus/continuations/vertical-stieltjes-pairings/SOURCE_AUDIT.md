# Source audit and provenance

## Repository observation

Repository: `VladimirReshetnikov/ProveIt`.
Requested areas:

- `Analysis/Polylogarithms/docs/manuscript`
- `docs/incoming`

The GitHub connector was used for directory, source, search, and commit reads.
One observed main-branch HEAD was
`0c740647c48baec7f0b4192723e977d69917dd52`, whose recorded commit timestamp is
`2026-10-11T00:57:27Z` (10 October in Pacific time). The source reads below
are separately identified by their actual blob hashes; they were not all
requested using that later HEAD as a pinned ref.

| Source inspected | Blob SHA | Scope |
|---|---|---|
| `Analysis/Polylogarithms/docs/manuscript/README.md` | `341ff8cddc0eae89230a057c2c02c0fb2325b419` | Canonical organization, proof/audit distinction, existing Stieltjes convolution program, S6/S8 status. |
| `Analysis/Polylogarithms/docs/manuscript/chapters/07-stieltjes-convolution-foundation.tex` | `ba1825f3b9c282c3e12ffff136e24bcf6aff9c5e` | First 95 source lines: Fourier conventions, periodic family, semigroup, derivative ladder. |
| `Analysis/Polylogarithms/docs/manuscript/chapters/07-shifted-stieltjes-correlations.tex` | `9220b6c417d5ec5a02a3de4ba7f4ee61a17621df` | Terminal source range beginning at line 760: rational reductions and audit/zero-shift distinctions. |
| `docs/incoming/README.md` | `9956ad83c5ddfa3c75e5f2946481a83082bc81e8` | First 100 lines: provenance and canonical-integration policy. |

Directory metadata and limited repository search results were also inspected.
This is **not a read-through of all canonical chapters**.

## Incoming archives: exact limitation

Metadata exposed several recent packages, including bilinear Mellin–Hurwitz,
coincident Stieltjes, periodic contacts, mixed spectral, ordered resonance,
nonlinear transport, and unequal-twist reports. Their names/metadata were
used only to identify possible overlap, not as evidence of uninspected
mathematical contents. Binary retrieval was not completed for these archives.
Therefore the article does not claim an exhaustive incoming-archive audit
or absence of every possible duplicate. Integration should include a final
comparison with their full texts.

## Primary public background

- NIST DLMF §25.11, Hurwitz zeta: `https://dlmf.nist.gov/25.11`
- NIST DLMF §5.9, Gamma/digamma integral representations: `https://dlmf.nist.gov/5.9`
- NIST DLMF §25.14, Lerch transcendent: `https://dlmf.nist.gov/25.14`
- Shpot–Chaudhary–Paris, arXiv:1603.00722; the abstract establishes that its auxiliary-zeta product integrals are over `[0,1]`.
- Shpot–Paris, arXiv:1609.05658; the abstract establishes the same distinction in integration geometry.
- mpmath version-tagged implementation:
  `https://github.com/mpmath/mpmath/blob/1.3.0/mpmath/functions/zeta.py`
  The source of `stieltjes` contains a real-part projection in its integral.

The new formulas are proved in this paper. Their proofs do not depend on
unavailable external report contents. Background transforms and special
values are classical; the package makes no exhaustive literature-priority
claim.

## Correction findings

No new false statement was established in the canonical portions actually
read. A concrete **version-specific numerical limitation** was found in the
installed mpmath 1.3.0 Stieltjes function at nonreal arguments. The original
failed comparison, the direct `gamma_0=-digamma` calibration, and the corrected
Hermite/Cauchy routes are preserved in `results/` and the article.

No claim is made that a particular existing ProveIt theorem or replay was
affected. Recommended audit action: locate any calls to that routine with
nonreal second arguments and replay them using a holomorphic implementation.

No repository files were modified, no issue was filed upstream, and no
claim about a later mpmath version is inferred from this version-specific
observation.
