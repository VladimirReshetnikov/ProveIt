# Literature and overlap receipt: A331120

Checked 2 October2026,03:49UTC. No external publication or repository changes.

## Verified identity and established baseline

A331120 counts minimal complete deterministic automata recognizing finite languages over a fixed binary alphabet, up to state isomorphism, with n transient states plus one rejecting sink. Equivalently it counts the associated finite languages by minimal-state complexity. Official export A331120.seq was retrieved through the OEIS GitHub repository, blob b0a6339831f74705a34159c90247a33b70db94dc, entry revision6August2024. https://github.com/oeis/oeisdata/blob/main/seq/A331/A331120.seq . Twenty displayed terms were independently reproduced.

Elvey Price–Fang–Wallner, *Asymptotics of Minimal Deterministic Finite Automata Recognizing a Finite Binary Language*, AofA2020, DOI https://doi.org/10.4230/LIPIcs.AofA.2020.11 ; readable primary PDF https://combinepic.math.cnrs.fr/2020.11 . Proposition5 gives the exact recurrence, and Theorem1 proves the Theta scale. This is the established starting point, not the new theorem. The same source explains the minimal-state-complexity interpretation and distinguishes arbitrary automata, whose asymptotic enumeration had already been addressed by Korshunov and Bassino–Nicaud–Sportiello.

Ghosh Dastidar–Wallner, *Asymptotics of relaxed k-ary trees*, AofA2024, https://arxiv.org/html/2404.08415v1 : Proposition11 gives the general-arity exact DFA recurrence. Its asymptotic theorem concerns relaxed trees; its introduction continues to cite the2020 binary-DFA result. General-arity formulas are not a later positive-amplitude theorem for A331120.

## Bounded later check

The current project bibliography https://dmg.tuwien.ac.at/mwallner/stretched-exponentials/ was checked, along with targeted searches for A331120, finite-binary-language asymptotics, minimal-automata amplitude/constant, and2025/2026 results. No later binary finite-language amplitude or arbitrary-order result was located. The2026 decompression material concerns a different statistic/regime. This is bounded negative evidence, not a universal novelty guarantee. General minimal automata for arbitrary languages are a different family.

## Repository overlap

Current authorized ProveIt default-branch code searches for A331120, "minimal automata", "finite binary language", and "7/8" "Airy" returned empty result lists. Raw connector receipts are in duplicate-check.json. A separate "finite languages" search returned unrelated insertion-degree-spectrum papers and computability notes, not this asymptotic family. Thus semantic overlap was checked as well as the ID. Searches do not certify every branch or unpublished file.

The two complete previously cached canonical inverse sources were searched for A331120, minimal automata, finite binary language, finite languages, and acyclic automata, all with no matches. canonical-source-scan.json includes their sizes and hashes. Existing relaxed and compacted tree results are deliberately used as mathematical inputs, not hidden as independent new work.

## Scope

The new result is the finite positive leading amplitude and the all-finite-orders relative expansion, plus a precisely selected real model inverse. It does not newly discover the Airy exponential or7/8 power. No numerical amplitude enclosure is claimed. A wider weighted-exclusion parameter family is not asserted because general strict positivity still needs separate lower estimates.
