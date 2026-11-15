# Transfer assessment: ZFC, Diophantine consistency, and concise iPRA

All source references below are to ProveIt revision `8d31445d858761a8f6150c2e5012adae8895e932`. The source manifest records the exact Git blob identifiers of the files examined. This assessment distinguishes reductions in the final binary transition table from reductions in another representation.

## ZFC: transferable machine techniques

The concrete K215 construction is directly relevant as a source of engineering methods. Its command-local field reader removes reads from common dispatch and inserts them only into commands that require them; command permutation and source reassociation expose better sharing. Its proof separately checks the ordered instruction stream, both guarded control-flow branches, physical allocation, whole-tape local marker identities, arbitrary-natural runtime contracts, and the blank startup. The local `81/0` repair replaces a three-transition block by an equal block and frees a row for decoder use. These are useful templates for the present loop-return and short-block work. [Z1, Z2]

They are not additive state credits. The K215 proof explicitly scopes its marker folds to their particular predecessor contexts; the source count and the physical state count are checked separately. Its numerical calculus is calibrated to ZFC. Importing that calculus unchanged would change the target consistency statement, and importing a physical fold requires the PA table to satisfy that fold's actual incoming-row premises. The PA family already exploits restricted rho8, no-push MP, and contextual decoder sharing, so finding those mechanisms in ZFC does not itself produce an additional PA reduction. [Z2; PA comparison inventory]

The practical lesson is to price a logical/source change all the way through allocation and startup. Closed source reassociation followed by literal contextual shortcuts is a justified transfer of method; numerical differences between ZFC and PA state totals are not a theorem about spare capacity.

## Diophantine consistency: useful calibration, different cost measure

The exact Lean endpoint in `Compact44/IPRAOrdinary12.lean` starts from a twelve-variable polynomial expression whose positive zeros, in every stated IΣ1 model, correspond to halting of machine215. It then applies the existing native, standard, and equality-only iPRA bridges to the mapped Foundation **ZFC** refutation predicate. The file explicitly separates that formal symbolic expression from external coefficient/PDF binding. [D1]

This is useful for the present task in two ways: it demonstrates a disciplined all-model witness bridge, and it separates the positive witness transformations from the negative intuitionistic consistency conclusion. The candidate iPRA language is intensional: finite primitive-recursive construction codes give function symbols, while the induction schema is stated explicitly. That matters when asserting that a clock or proof compiler is available inside iPRA. [D2]

A smaller number of polynomial variables or arithmetic operations does not bound the number of states needed for a blank-start, two-symbol TM. Such a machine must enumerate the witness domain, evaluate the arithmetic expression, represent and initialize its fixed coefficients, and halt exactly on a zero. Variables can be eliminated by moving information into degree or constants. The maintained README itself uses several size coordinates and notes coefficient tuples such as `2^590069 - 1`; those constants are mathematical data that still need a machine implementation. [D3]

Nor may the ZFC endpoint simply replace the PA checker. A new route would need a polynomial calibrated to the exact PA predicate, with both required weak-arithmetic directions, followed by a fully costed evaluator. Specializing a generic halting-to-polynomial representation to a PA machine is possible in principle, but supplies no automatic reduction below the state count of the original encoded machine.

## ConciseIPRA: rule fusion, with a different object theory

The concise-iPRA project explicitly measures standalone Python proof checkers by normalized source tokens, AST nodes, and bytes. Its native scalar calculus is bi-interpretable with iPRA: `NativeBiInterpretation.lean` states faithful readings in both directions, formula round trips, and equivalence of inconsistency predicates. These are not PA-calibration theorems. Replacing the existing numerical PA calculus by that checker would require an additional argument connecting the new object's refutations with PA's refutations. [C1, C2]

There are nevertheless useful design ideas. `NativeEvalDischarge.lean` combines evaluation and witness elimination into one discharge rule, leaving three inference families. Its deterministic local operation has zero, successor, and identity cases. This suggests looking for an evaluator operation that can share an already-required elimination return, rather than paying separately for each rule. The current PA AX-fallthrough design is an example of exploiting that kind of shared control shape. [C3; GH/GHS protocol]

The three-family count hides neither the need for coded substitution nor the management of contexts and fresh binders: those operations remain explicit in the Lean constructors and translations. Some other concise presentations move computation into normalization, which likewise relocates checking work rather than proving a smaller binary transition table. A compact Python module can use powerful built-ins, recursive syntax manipulation, or large arithmetic in one expression. Its token or rule count therefore cannot be read as a TM-state count. [C1, C3]

The most plausible transfer is local rule fusion whose executable cost can be checked in the existing PA source language. No complete new PA-calibrated checker or sub-194 binary compilation was obtained from these three directions in this work.

## Exact source references

| ID | Repository path | Git blob |
|---|---|---|
| Z1 | `Computability/BusyBeaver/Research/ZFC/candidate-k215/README.md` | `2768ef3f05b6b0a7415aa2194e8a92c5ef645f06` |
| Z2 | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` | `5b62cecff23a798a4b34255d1f843e72ad11b623` |
| D1 | `Computability/DiophantineConsistency/Lean/DiophantineConsistency/Compact44/IPRAOrdinary12.lean` | `c6740c3fd45cdfc148a8be02eae4da4e8ba364b7` |
| D2 | `Computability/DiophantineConsistency/IPRA_AXIOMATIZATION.md` | `80719342dede31be952f9e788d23e7fd5f5cdfd2` |
| D3 | `Computability/DiophantineConsistency/README.md` | `62b1ce4f0828926ce87cbe48265f87310e09280e` |
| C1 | `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md` | `8f810145b9ac8502748080a4ec4f15f2ad4c99bb` |
| C2 | `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean` | `ccfe499b9687ea0e176f832686d8e492fe15544b` |
| C3 | `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeEvalDischarge.lean` | `292b5846373a6eac600a86eae45e273e16e90d87` |

The machine-specific GH/GHS source identities and command statements referred to here are documented in `calibration_audit.md` and its JSON replay receipts. The inventory is the separate comparison output of this research packet.
