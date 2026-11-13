# Independent conditional free-J graph population audit

This reviews paired evidence `d8246d0182`. The compiled theorem
`FreeJPopulationClient.graph_population` says that, in every IΣ₁ model, a
positive zero `v` of the exact free-J literal has `3h+2≤population(R)` under
**all** of these explicit conditions: the port and variable positivity and
inequalities `p₀>0`, `p₂<p₀`, `p₃<2p₀`, `vⱼ>0`; `p₀≥46`; and the radix
identity `q=1+v₀p₀=2^h`. Its rank is

```
R = ((q−1)(q−v₁)+v₂)(q²−1)+(p₂+q p₃)v₀.
```

The proof composes the exact free-J graph power and ordinate-index results,
first-factor divisibility and the population-facts theorem. It does not
supply the radix identity or the bound `p₀≥46` from this theorem's other
hypotheses. It does not bind the retained compact44 port tuple, calibrate a
checker, simulate a machine, or construct an iPRA derivation.

The read-only audit independently checks every one of the 22 compiler rows:
nine frozen closure sources and two client sources on each same-side free-J
provider, all source/object/log hashes, exact source-declared direct imports
against the objects available at that point in the ordered build, and paired
object identity. It checks all 97 inherited provider objects per side and the
standalone `FreeJPowerFinish` seed, reruns its independent parent audit, and
verifies the earlier warning-gate review. The protected outer session 11239,
all compiler steps and all dependency queries are recorded as exit 0. The
terminal observation reports launch HEAD
`b28da1e6ed671e9b10a4759ac4b21e864cf91075` and removal of the three named
loader variables before Python; this audit verifies that recorded observation,
not a continuous external HEAD or environment history.

Each side contains exactly the allowed `ArithmeticBinomLegendre.lean:78:10`
`unnecessarySimpa` warning, including the full expected note. No other
warnings, errors or `sorryAx` occur. Both exact named client axiom reports
list Lean metatheory `propext`, `Classical.choice`, and `Quot.sound`. The
first, failed protected attempt is separately retained and reviewed; it is not
part of the successful pair.

The audited source/provider hashes are point-in-time checks. Inherited
Foundation outer-wrapper and package-transitive/dynamic ancestry limitations
remain; a sampled RSS figure is not a whole-process-tree quota, and `--deps`
and audit subprocess timeouts are not monitored whole-tree resource bounds.
The audit starts no Lean compiler and needs the original `/tmp` object trees.

Run from the repository root:

```
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary12-freej-population-client-independent-audit/audit.py
```

Actual audit session 85224 exited 0; see `CHECK.json` and
`terminal-observation.json`.
