# Scoped source comparison

Checked 1 October 2026.

- OEIS A202061 (https://oeis.org/A202061) still describes classical 120-avoiding ascent sequences, credits the 0..500 b-file to Liang Chengwei, Shi Lecun, Cai Zhongyu (0..74 Conway/Conway), and reports no known formula or GF in the inspected entry.
- Conway, Conway, Elvey Price, Guttmann, EJC29(4)2022 P4.25 final PDF: https://www.combinatorics.org/ojs/index.php/eljc/article/download/v29i4p25/pdf/ . The final pp.14–15 contain the O(n^3 log^2 n) high-school enumeration claim; no recurrence, code, or separate reference accompanies it. Primary source searches on all three names did not locate the algorithm.
- The final paper explicitly treats the 3/8 exponent and other subexponential parameters as numerical estimates. It says the 500-term analysis reinforced the same estimate; it supplies no proof of a stretched exponent.
- Classical 120 avoidance is essential. Lin–Fu, arXiv:2003.11813, concerns vincular adjacency and is not the same sequence.
- GitHub connector code search scoped to VladimirReshetnikov/ProveIt for A202061 returned no results. The scoped ascent-sequences search returned only unrelated prose hits in three documents. The code-search result URLs referenced commit 63b9d68407f21832316eb296fd0885e40e033c90, so index freshness is not established from that result alone. A separately available tree snapshot from earlier in this session at b4d1ba280aca1c7f57051b39a7a2e6216bab20fb had no A202061, A202062, or ascent-named paths in its complete Combinatorics subtree and docs tree. Its repository-wide recursive listing was truncated, so no global absence claim is made.
- Public web searches did not locate a later proof of the classical 120 stretch. This is a scoped novelty check, not a comprehensive publication-priority determination. The commuting-gap reduction may overlap the unpublished 2022 students' algorithm.
- An attempted read of the OEIS b-file returned HTTP403; no conclusion is inferred from inaccessible data, and no workaround or bulk archive download was used.

The theorem drafts are derived from explicit finite-state recurrences and positive coefficient identities. They do not rely on the availability of the 500-term b-file or on numerical curve fitting.

Follow-up scoped GitHub commit searches for A202061 and `120 avoiding` returned HTTP401 Unauthorized. That route was stopped, and it supplies no negative-result evidence.
