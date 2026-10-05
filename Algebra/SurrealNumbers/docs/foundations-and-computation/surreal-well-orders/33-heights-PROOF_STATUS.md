# Proof status and assumptions

## What is proved in the manuscript

All references below are to theorem labels in `article.tex`. Numbered PDF
references are generated from those labels by LaTeX.

| Label | Result | Sufficient assumptions |
|---|---|---|
| `lem:wftest` | Descending-set-sequence characterization | GBC; standard background |
| `prop:setlike` | Set-like class well-orders stop at Ord | GBC; standard background |
| `cor:successor` | No embedding W+1 -> W | GBC |
| `thm:power` / `prop:laws` | Finite-support powers and arithmetic identities | GBC |
| `thm:division` | Canonical W = Omega*Q + alpha | GBC |
| `thm:polycond` | Explicit polynomial condensation tower | GBC |
| `thm:digits` | Finite-digit embedding into Omega^Gamma | GBC plus a supplied uniform exhausting tower |
| `prop:converse` | Converse from embedding | GBC + ETR_(Gamma+1) |
| `prop:exhaust` | Exhaustion along W+1 | GBC + ETR_(W+1), sufficient bound only |
| `thm:fixedpoint` | Explicit finite-tree direct-limit fixed point | GBC; not arbitrary class-valued omega recursion |
| `thm:diagonal` | Strict domination of a uniform family | GBC |
| `thm:bounded` | Diagonal above fixed finite definability complexity | GBC, named global order, fixed standard n |
| `cor:paramfree` | Parameter-free presentations externally cofinal | Same fixed language with G |
| `cor:nodefcofinal` | No definable uniform cofinal family | Same fixed language with G |
| `thm:fullspectrum` | Full spectrum [0,kappa^+) | External ZFC; inaccessible kappa; full classes over V_kappa |
| `thm:height` | Countably cofinal definability ceiling | Same rank model; fixed G |
| `cor:heightclosure` | Arithmetic closure and epsilon-number ceiling | Same rank model; fixed G |
| `thm:truthjump` | Strict increase after adjoining truth | Same rank model; truth for the original G-language |

## Critical qualifications

- Omega denotes a class order, not a set ordinal in the same universe.
- An embedding is not assumed to be initial.
- Quotients by class-sized blocks use least representatives, not class objects
  as members of another class.
- Every family used in a diagonal sum must have one uniform class code.
- The D_n construction is a schema at standard finite syntax levels. It does
  not supply one definable evaluator for all levels.
- Parameter-free means without SET parameters, relative to the fixed named
  class predicates. Pure-language parameter elimination needs a definable
  global order.
- The digit theorem consumes a tower. The theorem does not assert its
  existence in GBC for every W.
- The full-spectrum and height results are external statements about a
  specified inaccessible rank model. They do not transfer without proof to
  arbitrary transitive, non-beta, or nonstandard class models.
- Countable cofinality of delta_G is external; it is not countable cofinality
  of the internal class of ordinals.

## Novelty and prior work

The manuscript derives the stated structural and definability consequences.
Historical priority has not been established. Basic class orders beyond Ord,
class-recursion theory, and the existence of long condensation constructions
are not claimed to be new. The repository guide already records related
condensation work.

The paper gives no reversal of class comparison to ETR and no claim of a
solution of Hamkins--Woodin Question 7. It also does not claim the canonical
digit map always has initial image.

## Verification actually performed

- pdfLaTeX compilation with resolved internal references and bibliography.
- Finite Python checks: 155,530 assertions passed.
- PDF rendering and layout inspection; final checks are recorded in the
  generated package manifest and final delivery.

The finite tests only check coding conventions. They are NOT machine proofs
of the class-theoretic statements. No Lean, Rocq, model finder, or independent
referee has certified the arguments as part of this delivery.
