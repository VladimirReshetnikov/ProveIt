# Shared quartic graphs for complete fixed formula construction

`AnnotatedSharedSyntax` compiles every finite tree, and hence every existing
`quoteForm f`, into a single stored system of quadratic rows. Its actual
sum-of-squares graph has total degree at most four. The entire constructor
system has exactly `4 * forkCount` natural witnesses and
`4 * forkCount + 1` quadratic residuals.

The compiler supplies explicit finite data. It never inserts a large quoted
formula value as a numeral coefficient, and its metadata theorem does not
construct closed formula-graph expressions.

## One common scope

A tree fork allocates four naturals in a fixed `Fin.addCases` block:

```text
stored quote output, branch bit, order slack, maximum pair component.
```

The two child blocks follow this block. An atom introduces no witnesses; its
root expression is the original label expression `n*n+1`. Every fork adds the
four already checked `ForkCertificate` residuals from
`AnnotatedSyntaxGraphs`. Child expressions read stored fork outputs or inline
atom expressions. Their degree is at most one, so each instantiated residual
remains quadratic.

`residual` retains every local row and both child row blocks in the same
scope. `valid_fork_iff` proves its exact decomposition. `rootValue_sound`
proves that any natural assignment satisfying these stored rows computes the
actual tree quote. `valid_exists` proves completeness by structural induction,
with explicit finite witness assembly. No witness is selected into executable
compiler data from a Prop.

The final system adds one equality between the claimed external output and
the computed root. `holds_iff` and `holds_split` connect the exact stored
system to those rows. The supplied `graph` and `formulaGraph` then expose
ordinary `GraphRep` data. `graph_degree` and `formulaGraph_degree` prove the
quartic bound for these complete stored expressions, including all child
constraints and the final equality.

## Exact fixed-body counts

The count proof uses only the four-slot recurrence, linked to the actual
graph witness count by a universal theorem. It gives these counts for the
seven unsealed fixed ZFC bodies used by the direct axiom dispatcher:

| Body | Natural witnesses | Quadratic residuals |
| --- | ---: | ---: |
| Extensionality | 84 | 85 |
| Regularity | 84 | 85 |
| Power set | 108 | 109 |
| Pairing | 104 | 105 |
| Union | 108 | 109 |
| Infinity | 188 | 189 |
| Choice | 264 | 265 |

One additional natural coordinate is the claimed output. These graphs have
exact degree bounds and witness counts; no bound/sealing certificates or
schema-argument processing are included in this table. The earlier ordinary
compositional constructor graphs used five witnesses per fork and did not
have a proved complete quartic bound. The shared-row construction uses four
and proves the bound throughout the system.

## Checks and remaining interfaces

Dedicated checks evaluate the actual stored system rows on both fork
branches, atom output equality, a nested constructor, a wrong claimed output,
and a forged child output. In the forged case the parent's local rows agree
with the fake child value, while the retained child rows reject it. This
checks that the shared compiler preserves child constraints. The main module
and dedicated checks both compile with no errors or warnings; seven runtime
controls return true. Twenty-six printed axiom audits use only the standard
three axioms, or fewer.

The checkpoint compiles fixed syntax supplied as actual finite data. The
complete external PR refutation checker remains unchanged. To compile its
variable-code schema and proof-table operations economically, further
interfaces must combine constructor templates with variable ports, guarded
local relations, and bounded scanner traces in shared contexts. No complete
checker quartic, variable minimum, or internal nonstandard-code transfer is
asserted here.
