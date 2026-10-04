# Targeted primary source verification

4 October 2026. Read-only source checks during Report65 assembly:

- Durand-Lose, MCU 2004/2005 author manuscript, Section 3, manuscript pages 6-8: two fixed scale signals, two counter positions and an instruction signal; cardinality-preserving computation. https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2004_MCU.pdf
- Durand-Lose and Emmanuel 2021, Section 4, manuscript page 8: a border-and-back signal delay proportional to the width, with speeds selected for the desired delay. https://arxiv.org/pdf/2106.11176
- Durand-Lose, CiE 2006 author manuscript, Section 2.2, manuscript page 5: time reversal uses opposite speeds and inverse collision rules. https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2006_CiE.pdf
- Dudenhefner FSCD 2022 publisher record: stated increment/conditional-decrement model and the dependence of universality statements on instruction semantics. https://doi.org/10.4230/LIPIcs.FSCD.2022.16
- Exact retained Pell source read inertly at lines 760-766 and 860-864, plus surrounding constructive proof. No Lean build. Hash and commit are in the article and input pins.

This targeted check supports the explicit attribution and scope boundaries only. It does not establish firstness, absence of prior equivalents or an exhaustive novelty search.
