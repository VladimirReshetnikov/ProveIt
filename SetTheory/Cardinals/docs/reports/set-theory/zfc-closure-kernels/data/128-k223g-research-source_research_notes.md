# Source and compilation investigation for G223

The successful construction keeps the existing proof enumerator and its eight logical row positions. It replaces the old equality row and its separately emitted equality-vacuity helper by a single stronger row

\[
G(a,b,c)=\operatorname{Eq}(c,a)\to
 \bigl(\operatorname{Eq}(c,b)\to
   \operatorname{All}_{\operatorname{RelCode}(a,b)}\operatorname{Eq}(a,b)\bigr).
\]

The gated theory bundle becomes `And(core_f, RV)`. The separate mathematical certificate establishes deductive equivalence with the old numerical calculus on all natural codes. The constructor and emitter checker establish the connection to the literal optimized register program.

## Successful source transformation

The source is derived from the parent225 source shipped inside the pinned K224 package. Its source digest is

`309358206463f8e8d88d86304e7c9f2273e3cdde64984b6db20c412516010878`.

The unchanged baseline macro contracts use the constructors

\[
I(x,y)=4P(x,y),\quad R(x,y)=4P(x,y)+1,\quad
Q(x,y)=4P(x,y)+2,\quad E(x,y)=4P(x,y)+3.
\]

The old equality row has 300 primitive source instructions. The new G row has 409. Removing H from the theory bundle removes 300 instructions for H itself and 27 instructions from the fused conjunction constructor. The net change is therefore

\[
4799+109-327=4581
\]

primitive source occurrences. A local insertion preserves the optimized sharing in the old row's two antecedents. Rebuilding the entire row from its visibly shorter list of named macros lost substantial sharing.

The first successful layout had one seven-zero address, belonging to an `INC 1` primitive. The existing eight-zero reset mechanism did not support that layout: the universal symbolic runtime checker found a concrete failing frame case. This was an actual implementation defect, not merely a conservative source metric.

One closed right rotation at source address `1110100100111000` repairs the defect without changing the number of DAG nodes. Its three factors are closed source programs, and both complete guarded-CFG resolvers verify that the rotation preserves every source control-flow edge. The resulting source has:

| Metric | K224 parent source | G223 source |
|---|---:|---:|
| Primitive instruction occurrences | 4799 | 4581 |
| Distinct source subtrees | 210 | 209 |
| Maximum source depth | 38 | 38 |
| Longest consecutive-zero address run | 6 | 6 |

The final source digest is

`fe3713adaf008a71ba4fbc6433de760ef124b8638efbc5c75e3afa2c1142c24f`.

The deterministic source compiler initially emits a 226-state binary parent, digest

`e7069fe4dc12fe62ba66cd88c27a51bfd83d548daad07591d3e0b0afaf6afe3d`.

Three separately certified table reductions yield the 223-state candidate. The temporary increase from 225 to 226 states despite reducing the source DAG is instructive: the baseline uses source-prefix-dependent decoder sharing. A source state whose old source meaning disappears may still be needed as microcode by another decoder entry. Literal machine size cannot be inferred from the source DAG count alone.

## Reproduction and independent source binding

`construct_g226.py` accepts the K224 package directory, its upstream K226 utility directory, and an output directory. It explicitly pins both baseline inputs and both resulting artifacts. It reproduces the source and parent table, checks every compound source decoder entry, and checks the closed rotation with independent source CFG resolvers. It does not claim that decoder-prefix checks alone prove the entire binary runtime.

`check_g_emitter.py` is a separate check of the calculus-to-source connection. It:

1. Pins the parent source, parent table, final source, and upstream Dag230 source.
2. Checks all-register local bisimulations for twelve macro bindings against the pinned upstream programs and their retained proof contracts. These account for earlier increment commutations and loop rotations, so textual equality of macros is not assumed.
3. Evaluates symbolic arithmetic expression trees for the old and new equality rows and theory bundles. Equality of these trees establishes equality of the emitted numerical codes for every natural choice of parameters; the check does not sample small values.
4. Verifies that the complete primitive instruction word changes only in the equality row and theory bundle.
5. Independently builds a direct closed-macro reference source and compares its entire guarded CFG with the final optimized source under two different resolvers. Both checks cover 5956 control cases.

The unchanged gate is `if c=a or c=b then 0 else And(core_f(a,b,c), RV(a,b,c))`. The eight logical row positions remain unchanged, so the existing enumerator's cache and stack-position contracts can be reused with the changed row and bundle expressions.

## Other measured routes

These figures are finite experiment results, not lower bounds on what a different compiler or encoding can achieve.

| Experiment | Scope actually searched | Best observed source result |
|---|---|---|
| Replace the old equality row by primitive symmetry, retaining H | Six ordered parameter pairs and all 132 binary parenthesizations of the seven-macro row | 215 DAG nodes, zero run 7 |
| Closed rotations after the symmetry replacement | Heuristic search with a 180-second budget | 212 DAG nodes, zero run 7, depth 35 |
| Replace the equality row by general specialization `All_a b -> b` | Six ordered pairs and all 14 parenthesizations of its five-macro word | 211 DAG nodes, zero run 7 |
| General specialization plus a gated crossed helper `Eq(a,b) -> All_c Eq(b,a)` | All 46,656 independent parameter permutations of the six retained logical rows around one best local layout | 214 DAG nodes; no improvement over that layout |
| Independent parameter permutations in the unchanged baseline | A heuristic traversal covering 242,676 distinct assignments of the seven row permutations | No source below 210 DAG nodes |
| Independent parameter permutations in the G construction | Exhaustive 279,936 assignments of the seven row permutations | No source below 209 DAG nodes |
| Closed rotations of the initial G layout | Heuristic search with a 120-second budget | 209 DAG nodes; depth improved to 34, but the zero run remained 7 |
| Targeted single rotations of the table-compatible G layout | All eligible closed rotations with at most 212 DAG nodes and zero run at most 6 | Two candidates; one retained 209 DAG nodes and yielded the final source |

The symmetry row has only 191 primitive instructions, compared with 300 in the original row, yet its straightforward source layouts grew. The specialization row has 134 instructions but also initially grew. The successful G row is larger than the old row by itself. Its benefit appears only when the corresponding equality helper and one conjunction are removed and the shared source fragments are retained.

The search therefore supports a practical method: prove a calculus transformation, preserve the useful existing source factors when implementing it, and measure the literal binary machine after context-dependent decoder reductions. A shorter formula or a smaller primitive instruction word is not, by itself, a smaller Turing machine.
