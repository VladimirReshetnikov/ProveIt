# Three-variable implication research

## Actionable result: two arbitrary-formula schemas

Use ordinary modus ponens and these two axiom schemas:

- H(p,q,r) = (p -> q) -> ((q -> r) -> (p -> r)). Polish: `CCpqCCqrCpr`.
- PW(p,q,r) = ((p -> q) -> p) -> (r -> p). Polish: `CCCpqpCrp`.

Every schematic variable ranges over arbitrary formulas, not just atoms. This is a different complete basis, not a substitution restriction of the four-variable Lukasiewicz axiom.

A locally generated finite certificate derives Peirce and K from H/PW in **10 condensed-detachment steps**. An independently written checker reconstructs each step as explicit uniform substitutions followed by ordinary modus ponens. It uses disjoint variable namespaces for the premises, performs occurs checks, and checks the resulting instantiated major antecedent equals the minor and the consequent equals the claimed schema. All twelve displayed rows also pass Boolean tautology checks. This is a small trusted Python verification, not an independently certified proof-assistant theorem.

Files:
- `H_PW_certificate.json`: compact twelve-row certificate (two axioms + ten CD steps).
- `H_PW_VERIFIED.json`: all explicit substitutions and instantiated MP premises.
- `verify_certificate.py`: independent replay checker, no search-code imports.
- `search_pair.py`, `search_pair_short.py`: original local proof searches, not external code.

## Exact classical-strength bridge

The resulting H/K/Peirce basis is exactly the Tarski–Bernays basis on page 2 of Frank Pfenning's primary CADE 1988 paper, including arbitrary-formula substitution and detachment as the inference rules:
https://www.cs.cmu.edu/~fp/papers/cade88.pdf

For an explicit finite proof of the standard S schema from precisely H/K/Peirce, official Metamath theorem `tarski-bernays-ax2` gives a proof using only those three schemas and modus ponens:
https://us.metamath.org/mpeuni/tarski-bernays-ax2.html

Here H is literally Metamath `imim1`, not a silently exchanged form:
https://us.metamath.org/mpeuni/imim1.html

S is `(p -> (q -> r)) -> ((p -> q) -> (p -> r))`.
Thus H/PW proves K/S/Peirce. Conversely H and PW are classical implicational tautologies, so this is precisely classical implicational logic. The existing ZFC-formalism bridge still needs its native-code transport check; formula-level completeness alone does not certify a TM candidate.

## Constructor counts and recommended native alignment

H has 5 implication occurrences; PW has 4. There are 3 independent formula fields and 2 output rows.

Use PW with the **permutation (q,r,p)**:
`((q -> r) -> q) -> (p -> q)` (Polish `CCCqrqCpq`).
It generates the same schema family, but gives a **7-constructor combined DAG**:

1. a = p -> q
2. b = q -> r
3. c = p -> r
4. d = b -> c
5. H = a -> d
6. e = b -> q
7. PW = e -> a

Counts: tree = 9, separate DAGs = 5 + 4, joint optimally permuted DAG = 7 (plus three variable leaves). The unpermuted alignment has joint DAG 8. No claim about actual TM state count follows from these counts. Pricing must include two emitted rows, stack/register duplication, parser overhead, and native numeric normalization.

## Compact certificate

D(i,j) means independently freshen i and j, unify the antecedent of major i with minor j, then instantiate the consequent.

1. CCpqCCqrCpr [H]
2. CCCpqpCrp [PW]
3. CCCCpqCrqsCCrps = D(1,1)
4. CCCpqrCCCqsqr = D(1,2)
5. CpCqq = D(2,2)
6. CCCCpqrsCCCCqtCptrs = D(1,3)
7. CpCCCqrqq = D(2,4)
8. CCCppqCrq = D(1,5)
9. CCCCpqCrqsCCCptps = D(6,4)
10. CCCpqpp = D(7,1) [Peirce]
11. CCCpqpCrCsp = D(9,8)
12. CpCqp = D(10,11) [K]

## Literature search result and firm lower bound

No genuinely three-variable single axiom with a verified finite completeness certificate was located in this bounded primary-source search. This is a search result, not a nonexistence theorem.

Toshihiko Sekimoto (1972), *On the Uniqueness of the Shortest Single Axiom for the Implicational Calculus of Propositions*, proves the four-variable `CCCpqrCCrpCsp` is the unique shortest single axiom, resolving the remaining Tursman candidate. Consequently any three-variable single axiom needs at least 15 Polish symbols, i.e. at least 7 implication occurrences.
https://www.jstage.jst.go.jp/article/pjab1945/48/5/48_5_290/_pdf/-char/en

Important exclusions:
- Meredith `minimp` is intuitionistic/minimal implication, not classical; its verified Metamath form has five schematic variables and 8 implications. It is not a 3-field replacement: https://us.metamath.org/mpeuni/minimp.html .
- Sheffer-stroke 3-variable Boolean *equations* are not implicational schemas and require an equational proof engine. They are not drop-in replacements.
- Modal strict-implication C4/C5 axioms are not classical material implication; Fitelson's primary results explicitly separate these systems: https://fitelson.org/ar.html .

Research and replay date: 2026-10-20 UTC. No downloaded code was executed.

## Follow-through: explicit S proof also independently replayed

`H_K_P_to_S_certificate.json` stores all 97 rows of the official Metamath H/K/Peirce-to-S proof. `verify_metamath_S.py` parses the retrieved public-domain proof table, checks every axiom row against exactly K, H, or Peirce, checks each ordinary MP step syntactically, and confirms the last row is `CCpCqrCCpqCpr`. Result: PASS; 4 K instances, 40 H instances, 5 Peirce instances, and 48 MP steps. No downloaded code was run. `metamath_S_source.txt` preserves the retrieved proof-table data.

An independent native-code reviewer also replayed the H/PW bootstrap using the explicit substitutions and no unification or search. Its result is `/workspace/scratch/ce29ab924f1c/research217_native_basis_review/H_PW_NATIVE_REPLAY.json`. It confirms the universal equalities survive interpretation under I=4P, including I(0,0)=0, with schematic variables ranging over arbitrary natural formula codes. This is logical-calibration evidence, not a compiled machine or a <=217-state certificate.
