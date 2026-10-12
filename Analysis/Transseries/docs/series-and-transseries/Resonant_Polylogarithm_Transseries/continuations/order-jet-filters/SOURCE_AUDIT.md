# Source audit and attribution boundary

## Snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `8f5afd4d7565df808359f6a0c22f87f79a119bb9`.
Read date: 12 October 2026.

The source was inspected through connected GitHub reads, not a full local clone.
Search results sometimes pointed at a different indexed commit; relevant source
reads were explicitly refetched at the pinned commit. No remote writes occurred.

## Repository material actually inspected

| Source | Read scope | Use |
|---|---|---|
| `Analysis/Polylogarithms/README.md` | Opening project overview, approximately source lines 1–200 | Project scope, proof-status conventions, bridge topics |
| `Analysis/Transseries/docs/series-and-transseries/README.md` | Selected opening and inventory ranges, including 400–650, 1800–1960, and 2200–2400 | Existing packages, q-product completion and averaging safeguards; not a complete canonical-volume audit |
| `.../Resonant_Polylogarithm_Transseries/README.md` | Complete returned README | Prior scope, date, test methodology and limits |
| `.../Resonant_Polylogarithm_Transseries/article.tex` | Returned source ranges 60–300, 300–580, 580–740, 1080–1350, 1350–1490; some long responses truncated at the later end | Completion theorem, first-jet Gamma kernel, Bell coefficients, periodic dictionary, generic reversion, averaging audit, numerical differentiation warning, research questions and bibliography |
| `.../Nonlinear_Stokes_Transport_Logarithmic_Inversion/article.tex` | Source lines 1–150 and a search-matched arithmetic-averaging statement | General inverse-transport architecture and its prior attribution; not a full audit of the entire proof corpus |
| `docs/incoming/` | Pinned contents listing | Names of pending archives only |

Here `.../` in the last three article paths abbreviates
`Analysis/Transseries/docs/series-and-transseries/`.

Relevant source blobs:

- Resonant article: `d54638582ab147eb4a48a846c3bdc371643aaf39`.
- Resonant README: `fcc4cd0dcd7f873566f9e7f6aac32327a07fe668`.
- Nonlinear transport article: `1e8b24325554d1f1c94c29f21b794ba62feff755`.

The existing resonant article was discovered during the source comparison and
already contained several formulas independently derived early in this research.
Those formulas were reclassified as credited background before the report was
written. Its positive-integer Gamma/Bell results and dilogarithm exact-radius
results are **not** novelty claims of this contribution.

## Incoming archives: unresolved read boundary

The pinned listing contained:

1. `ProveIt_Lambert_Polylog_Order_Jets_2026-10-12.zip`
2. `ProveIt_Quadratic_Polylog_Boundaries_2026-10-12.zip`
3. `Resonant_Lambert_Inverse_Transseries_2026-10-12.zip`

The raw binary fetch was rejected as non-UTF-8 by the text reader; container
network retrieval was unavailable, and the alternative routes attempted did not
supply usable bytes. A Library search did not locate the relevant archive
contents. No claim about their actual theorem statements is made. Nonduplication
relative to these archives remains a required integration check.

## Primary mathematical references inspected

- NIST DLMF 25.12, especially current Eq. 25.12.13 (Jonquiere inversion),
  the Fermi integral, and the polylogarithm/Fermi index relation:
  https://dlmf.nist.gov/25.12
- NIST DLMF Gamma, reciprocal-Gamma, digamma integral, and sectorial asymptotics:
  https://dlmf.nist.gov/5.5 ; https://dlmf.nist.gov/5.7 ;
  https://dlmf.nist.gov/5.9 ; https://dlmf.nist.gov/5.11
- NIST DLMF Hurwitz zeta:
  https://dlmf.nist.gov/25.11
- A. Gil, J. Segura, N. M. Temme, *Complete asymptotic expansions for the
  relativistic Fermi–Dirac integral*, arXiv:2108.11210v2, Section 3 and Lemma 3.1.
  https://arxiv.org/html/2108.11210v2
  Published in Applied Mathematics and Computation 412 (2022), 126618,
  DOI 10.1016/j.amc.2021.126618.
- M. Karatarakis and F. Wiedijk, *A formalization of the Gelfond–Schneider theorem*,
  arXiv:2603.24823v1, Theorem 3.1 and the explicitly chosen complex logarithm in
  its proof setup. https://arxiv.org/html/2603.24823v1
  This is a source for the classical theorem, not evidence that this report has
  been formalized.

These sources were used for specific classical inputs, not as a basis for
claiming the new filter or inverse results have already been peer reviewed.
No third-party source text or PDF is redistributed in the package.

## Search scope and novelty statement

Repository searches included `Sommerfeld`, an arithmetic-averaging theorem label,
and `Stokes-neutral`. The last exact phrase returned no repository match.
Web queries included combinations of `polylogarithm`, `order derivative`,
`digamma`, `Stokes`, `filter`, and `Stokes-neutral`. No matching sharp
logarithmic-node ideal theorem or exact moving-order curve was identified in
those returned results. This is a bounded search, not a proof of absence or an
exhaustive priority clearance.

## Claims promoted versus claims not made

Proposed additions are the sharp order-filter classification (including its
robustness and algebraic-coefficient restrictions), the analytic neutral curve,
and the assembled Stieltjes/positive-integral/digamma inverse theory at order
zero. Theorem proofs are contained in the report.

Not claimed: newness of Jonquiere inversion, complete Sommerfeld asymptotics,
Gamma reflection, Bell polynomials, interpolation, Lagrange inversion, Rouche's
theorem, Gelfond–Schneider, or the general nonlinear averaging obstruction.
The small inverse disk and large-core inverse disks are sufficient, not exact.
No newly verified mathematical error was found in the accepted source statements
actually inspected; unread material was not assessed by inference from titles.
