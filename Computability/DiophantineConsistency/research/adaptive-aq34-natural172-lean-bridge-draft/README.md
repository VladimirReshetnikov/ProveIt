# Proposed AQ34 natural-172 Lean evaluation bridge

This packet contains inert source for the exact [34-variable, 172-operation
natural-domain graph](../adaptive-aq34-natural172-signed-cancel/README.md),
and proposes its evaluation bridge to the existing positive-shifted AQ34
literal. The graph is the historical current-2011-port branch, not the
separate natural-79 compact-port equation. All `.lean.src` declarations,
tactics, `rfl` steps and `#print axioms` commands are **unelaborated**.

The generated source transcribes all 172 rows and names the same 22 squared
residuals as the AQ34 parent. Its proposed sum-to-literal equality is `rfl`;
the source check separately verifies this ordered square sum as a syntactic
DAG, not a Lean reduction. The bridge proposes the all-port, all-commutative-
ring identity between the new literal at `v` and `positiveShift` of the AQ34
literal at `v`. It includes named identities for the three canceled shifts:

```text
(wPositive+1)-(wNegative+1) = wPositive-wNegative
(dPositive+1)-(dNegative+1) = dPositive-dNegative
(vPositive+1)-(vNegative+1) = vPositive-vNegative.
```

The proposed proof checks each of the 22 residual evaluations separately,
uses the existing ring-substitution lemma, and combines their squared sums.
The `EvaluationIdentity` proposition states the exact missing universal ring
identity. Native, standard and equality-only reference iPRA clients all take
that proposition as an explicit premise and reuse `IPRAAQ34Native.bridge34`;
a separate candidate proof of the premise is included but has not run. The
historical AQ34 endpoint has its own matched-replay and inherited provider
limits; this new client is not a checked extension of that replay. No physical
TeX/PDF interpretation is asserted.

The read-only checker pins the parent, 172-row candidate and generated sources.
It independently interns the parent and child expression DAGs, applies exactly
the three displayed cancellation rewrites to the shifted parent, and checks
all 144 resulting parent row terms against the candidate. It also checks the
22 residual mappings and explicit conditional endpoint. The author's external
DAG/degree checker and both source receipts reproduce. These exact external
checks do not parse Lean, execute tactics, authenticate providers, report
axioms or prove iPRA derivability.

From the repository root, reproduce the read-only receipt:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/adaptive-aq34-natural172-lean-bridge-draft/check_source.py | cmp - Computability/DiophantineConsistency/research/adaptive-aq34-natural172-lean-bridge-draft/source-result.json
```

`generate.py` regenerates only the three inert source files and result in this
packet; it does not invoke Lean or create a build tree.
