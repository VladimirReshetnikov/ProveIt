# Exact context arithmetic and the assumption-rule validator

This checkpoint supplies literal primitive-recursive programs for validating
and shifting actual contexts, looking up their formulas, and checking the
original assumption rule. It extends the independent annotated sealed-ZFC
checker route. It does not yet supply all seventeen rules or the full numeric
proof-line loop.

## Raw context validation and shifting

The codec is exactly the frozen `quoteContext` format:

```text
contextCode []       = 1
contextCode (f :: G) = forkCode (formCode f) (contextCode G).
```

Its terminal marker differs from the zero terminal used by workspace lists.
`AnnotatedContext` uses a numeric spine scanner. Each nonterminal witness
entry supplies an input head code, its claimed shifted code, and a frozen
head-renaming table. The scanner checks exact fork equations for the two
current context codes and verifies that head-renaming certificate. It then
advances to the two tails and the remaining evidence. Invalid steps reset
to zero; the terminal condition requires both context codes to be one.

`scan_sound` and `checkNat_sound` hold for all raw natural inputs. They
recover an actual list of Lean formulas `G`, with the exact original context
code and the exact output code for `G.map (rename Nat.succ)`. No context or
formula parser premise is used. The first head-renaming certificate validates
its raw head formula code; the exact fork equations then reconstruct each
cons cell. Accepted empty contexts are handled directly by their fixed
terminal marker.

Completeness follows by list induction, choosing the already proved finite
renaming evidence for each actual head formula. The witness exists in Prop;
the supplied executable program data do not select it. The context code is
proved to dominate the list length, providing the canonical scan fuel.

`AnnotatedContextPR` supplies the entire local check, scan, and terminal
comparison as explicit `ScalarPRCode` data. Its main theorem is

```text
(∃ evidence, program.eval
  (inputCode (contextCode G) output evidence) = 1)
↔ output = contextCode (G.map (rename Nat.succ)).
```

The raw-input soundness theorem recovers the actual `G` from any accepted
packet. This operation directly supplies the context-shifting part of the
original `allI` and `exE` rules; their complete arithmetic rule validators
are not claimed here.

## Guarded lookup and the actual assumption rule

`AnnotatedContextLookup` supplies literal head, tail, drop, lookup, and
reference-comparison programs for this quoted context format. Its guarded
lookup returns zero for a missing entry and `formCode f + 1` for an actual
entry. The roundtrip theorem proves this for every context and index.
`reference_raw` recovers a real context member from a matching raw formula
code, and `reference_context` proves exact agreement with `G[index]?`.
Lookup alone does not certify an arbitrary natural context code.

`AnnotatedAssumption` combines the context validator with this reference
check. Its raw-input soundness theorem proves that accepted codes denote
an actual context `G` and a formula `f ∈ G`. `program_provable` supplies the
actual `Prov G f` constructor. On actual context and formula quotations,
`exists_program_iff_line` gives exact agreement with the frozen checker:

```text
(∃ shifted evidence index, program.eval
  (inputCode (contextCode G) (formCode f) shifted evidence index) = 1)
↔ (AnnotatedProofChecker.Line.mk (.ass G f) []).valid [] = true.
```

Thus the context-validity obligation required by lookup is discharged in the
combined raw-sound assumption validator. Neither an axiomhood oracle nor an
untrusted formula-decoding assumption is introduced.

## Checked sizes and regressions

Lean `decide` theorems certify these actual program-tree counts:

| Supplied program | Nodes | Optimized nodes |
| --- | ---: | ---: |
| Context validation and shifting | 4177 | 3855 |
| Context lookup | 207 | — |
| Exact context reference comparison | 501 | 485 |
| Combined assumption validator | 4753 | 4391 |

The context local validator has 3941 nodes, its scan has 4087, and its terminal
comparison has 89. These numbers are program syntax sizes, not the size of
a compiled polynomial or a claim of improvement over the closed baseline.

The dedicated checks cover valid empty contexts, a wrong terminal, an invalid
zero code, an atomic code in place of a context, missing evidence, quoted
context lookup at both valid indices and beyond the end, rejection of a
missing member, and exact original assumption-line semantics. Positive
nonempty context certificates are supplied by the universal completeness
proof, including binder formulas. Runtime controls execute only bounded or
tiny cases; whole nonempty canonical scans can be very slow because the
numeric code itself is used as fuel and supplied arithmetic uses literal
primitive recursion.

## Stage boundary

Still separate are the remaining rule validators, their shared parent-line
loop, a numeric sealed-axiom dispatcher, and assembly of a complete new
primitive-recursive refutation checker. The previous independent numeric
proof-code checker already has external soundness/completeness, but its full
PR implementation is not inferred from these local modules.

Transport to arbitrary internal omega codes also remains a distinct proof
obligation. It requires an actual interpretation of these numeric context,
lookup, and finite-table conditions inside a model, and agreement with its
existing internal coded-form operations. The external-natural theorems and
the internal semiring laws do not automatically provide that transport.

The next [shared-coordinate checkpoint](ANNOTATED_RULE_COORDINATES.md)
now gives exact supplied output/premise programs for all17 actual rules.
It retains side conditions, backward references and the full line loop as
separate obligations.
