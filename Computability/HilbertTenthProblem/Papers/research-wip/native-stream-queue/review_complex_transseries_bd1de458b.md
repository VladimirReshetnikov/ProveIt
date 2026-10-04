# Guide-only intake: three complex-transseries archives

Bounded intake complete, with no guide-level correction identified. This is **not a manuscript-proof review**. The immutable arrival is `bd1de458b7145f535cfcef0bef47d851c2e82463`, parent `5e4d8eed80f58f9299fa9deff7d03c095a373dbc`; its changes are exactly the three new archives below. The companion JSON, SHA-256 `7b61551d9cf9a3349ee960a328db6ad41246acf686d2e0d1bfb0b099430fccd1`, records each archive's Git blob, bytes and SHA-256, all member hashes and coverage, and exact human-read spans.

| Archive under `docs/incoming/` | Bytes | Members | SHA-256 |
|---|---:|---:|---|
| `Complex_Transseries_Reversion.zip` | 593,154 | 14 | `93a0e32342496a98f80739d26979fcda93dc2ea9c71f76a4779c9df58bc29a6c` |
| `Complex_Transseries_q_Cusps.zip` | 539,476 | 12 | `01ec1f405070963011dbfe4beaa1d18eb1923b8efd2f2899535e809eed022e94` |
| `Phase_Accurate_Complex_Reversion.zip` | 538,958 | 11 | `c1c61bb5a7188a34122bb97469b92af4e577eac7fe4979ff14dc5f0077f1f561` |

All 37 members were authenticated as inert bytes. Fresh metadata code parsed the three delivered checksum ledgers and confirmed exact coverage of all other members, respectively 13, 11 and 10. Internal checksum consistency is not independent evidence of mathematical correctness, authorship or historical execution.

I read these files completely, totaling 626 lines and 35,755 bytes:

- **Reversion:** `README.md` lines 1–102, `CLAIM_LEDGER.md` 1–28, `SOURCES.md` 1–80, `QA_REPORT.md` 1–55.
- **q-Cusps:** `README.md` 1–102, `SOURCES.md` 1–80, `PROVENANCE.json` 1–13, `BUILD_REPORT.json` 1–33.
- **Phase-Accurate:** `README.md` 1–46, `SOURCES.md` 1–38, `QA_REPORT.md` 1–49.

Each span is pinned to its archive/member with raw and normalized UTF-8 hashes. Manuscript sources, PDFs, figures, programs and scientific result files were hashed only. Their mathematical claims and recorded outcomes were not independently checked.

The **Reversion** guide advertises an exact Taylor radius for the inverse selected at zero of `Q(s)=-s exp(s+V(s))`, under an explicit holomorphic-disk smallness condition, with a unique dominant square-root singularity. Its claimed application to the existing logarithmic-inversion radius gap is restricted to sufficiently large core parameters satisfying inherited complex-uniform hypotheses. It distinguishes the selected sheet from unrelated critical values: the very small foreign-sheet example does not assert that the nearest critical value always controls the chosen inverse. Its ledger also preserves the hypotheses for filtered reversion, parameter uniformity, nonlinear actions, Stokes compatibility and singularity transfer. The stated `>10^1081` scale certificate and other analytic conclusions remain claims to inspect in a later proof review.

The **q-Cusps** guide advertises local prepared-transseries inversion, a branch-indexed logarithmic–Puiseux atlas, rational-cusp Euler-quotient preparation, four inverse regimes, correction-ramification claims and recovery of exponent data. It expressly does not supply unrestricted inversion for arbitrary transseries supports or unspecified summation operators. Its complex numerical test selects the logarithmic deck from a known reference solution; the guide correctly distinguishes that diagnostic from automatic sheet selection for an unknown inverse. The stated 619 exact assertions, 15 modular tests and 115-digit diagnostics are historical source claims, not new replay results.

The **Phase-Accurate** guide concerns the precision of an approximate inverse inside an exponential phase. It advertises a minimal phase jet and the fixed-step threshold `(2^(k+1)-1)(1-beta)>sigma` in its stated power-core setting, distinct moving Newton-count laws, and a higher-height obstruction with a sufficient moving cutoff. The precise manuscript parameter domains and necessity proofs were not read here. The status note usefully separates fixed-depth from uniform-in-depth estimates, real necessity from possible complex `2*pi*i` aliases, formal identities from convergence and summability, and geometric decay boundaries from Borel Stokes classification. Its 710 exact assertions and 160-digit diagnostics remain unverified execution records.

All three packages explicitly disclaim independent priority certification and Lean formalization. Their numerical work is described as ordinary high-precision diagnostics, not outward-rounded interval evidence. Their repository comparisons are targeted and sometimes mix pinned excerpts with default-branch material; these are author-declared comparison boundaries, not my independent audit of the named earlier reports or external literature. No claimed existing gap is treated as proved closed by this intake.

The natural subject route is `Analysis/Transseries/docs/series-and-transseries`, beside the named nonlinear Stokes, support-controlled reversion and q-transition reports. This is a routing suggestion, not a placement or publication action. Nothing in the read guides supplies a paid fixed-arity ordinary-input universal polynomial or an arithmetic operation bound for such a compiler. The standing preservation rule remains applicable to later review: keep claims with their credited hypotheses and missing proof obligations; do not erase unverified material or infer falsity merely because this intake did not read its proof.

Only fresh standard-library Git/ZIP/hash/JSON metadata code was executed: `/tmp/complex_transseries_bd1_metadata.py` and `/tmp/complex_transseries_bd1_finalize.py`, pinned in the JSON. No supplied or frozen program, copied predecessor, mathematical verification suite, PDF build, rendering or external-source fetch was run. No repository or Git mutation was made.
