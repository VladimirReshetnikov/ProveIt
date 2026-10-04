# Independent radius-two certificate audit

**Result: PASS.** The appendix's finite classification is correct: exactly 428
binary conservative local rules with neighborhood contained in `[-2,2]` exist;
423 have the supplied periodic collisions, and the other five are coordinate
projections. This audit establishes completeness independently of the appendix's
conservation-identity programs.

Audit performed on 2026-10-04 UTC. All deliverables are outside the original
`proof-packet`. No original program was executed or imported. The two original
Python files were inspected only as inert text. The only Python execution was
the newly written, then text-inspected, standalone checker
`check_radius2_graph.py`, using standard-library integer, JSON, hash, and graph
operations. It evaluates no evolving trajectory, physical simulator, stored
schedule, external scientific interpreter, or Lean program. The periodic checks
are simultaneous Boolean truth-table equations; no output is reused as a later
state. No uploads were performed.

## 1. Self-contained conservation criterion

Let a local rule be `f:{0,1}^5 -> {0,1}`, with the five inputs ordered from
coordinate `-2` to `2`. Construct the binary order-four de Bruijn graph:

- Its 16 vertices are four-bit words
- Its 32 directed edges are five-bit words `abcde`
- Edge `abcde` goes from `abcd` to `bcde`
- Its integer weight is `g(abcde) = f(abcde) - c`

The graph is strongly connected: appending the four bits of any target vertex
reaches that vertex from any starting vertex.

### Necessity: conservation implies an integer potential

A number-conserving rule on finite configurations has `f(00000)=0`, since the
zero configuration must remain zero. Fix any finite periodic word, and place
`N` consecutive copies between infinite zero tails. Away from a bounded number
of boundary positions, the difference between output and input particle counts
is `N` times the sum of `g` around one period. The boundary contribution is
bounded independently of `N`. Finite-configuration conservation therefore gives
`0 = N * delta + O(1)` for every positive integer `N`, forcing `delta=0`.

Every directed closed walk in this graph is the sequence of overlapping
five-bit windows of a periodic binary word. Thus `g` has zero sum on every
directed closed walk.

Set the potential `p(0000)=0`. For any vertex `v`, define `p(v)` to be the sum of
`g` along a directed path from `0000` to `v`. This is well-defined: if `P,Q` are
two such paths, append the same directed return path from `v` to `0000`; the
two resulting closed walks both have weight zero, so `P,Q` have equal weight.
Consequently every edge satisfies

    f(abcde) = c + p(bcde) - p(abcd).

### Sufficiency: an integer potential implies conservation

Conversely, suppose a Boolean table satisfies this equation. At the zero
self-loop it gives `f(00000)=0`. On a finite configuration, the sum of
`f(x[i-2],...,x[i+2]) - x[i]` is a telescoping sum of adjacent four-bit-window
potentials. Both tails eventually equal `0000`, and the sum is zero. Therefore
the rule conserves the number of ones on every finite configuration.

This proves the criterion in both directions without appealing to an external
conservation-identity implementation, empirical sampling, or a literature count.

## 2. Exhaustive enumeration from a mixed-orientation tree

A spanning tree of the underlying undirected graph has 15 edges. Choose a
Boolean value for `f` on each tree edge. Its weight `f-c` and the edge direction
uniquely determine all 16 integer potentials with `p(0000)=0`. The potential
equation then forces the values on all 32 edges. Retain a choice precisely when
every forced value belongs to `{0,1}`.

There are exactly `2^15 = 32,768` choices. Every conservative rule appears,
because its own tree-edge outputs are one of the choices and recover its
potential. No two different choices produce the same rule, because the tree
edge outputs themselves differ. By the criterion above, every retained rule is
conservative. Hence this is a complete enumeration.

The fresh checker constructs its tree by breadth-first search of the undirected
graph. Its tree edges, in traversal order, are the five-bit word indices

    1,16,2,3,8,24,5,18,6,7,20,28,11,13,15.

Six are traversed against their graph direction. This is a mixed leading- and
trailing-bit construction, independently derived from a graph criterion, not a
reimplementation of either original leading-zero or reversed-identity formula.

Observed exact counts:

- Tree assignments examined: **32,768**
- Assignments rejected because a forced output was non-Boolean: **32,340**
- Distinct complete conservative tables: **428**
- Duplicate retained tables: **0**

`independently-enumerated-tables.txt` contains the sorted complete set, in
lexicographic input-word order `00000,...,11111` for each table.
`independent-graph-potentials.json` gives an integer potential for every table,
providing a compact independent conservation certificate. Vertex order is the
ordinary integer order `0000,...,1111`.

## 3. Direct collision and completeness checks

Each original collision record contains a 32-bit rule table, a period `L`, two
different `L`-bit words `a,b`, and a claimed common word `image`. All integers
were checked for the correct type and range, and all rule tables for the exact
32-bit format, membership in the independently generated conservative set, and
uniqueness among certificate rows.

For every position `i`, the checker evaluates the two local Boolean equations

    f(a[i-2],a[i-1],a[i],a[i+1],a[i+2]) = image[i]
    f(b[i-2],b[i-1],b[i],b[i+1],b[i+2]) = image[i]

with indices modulo `L`. This directly checks the supplied finite witnesses,
without running either supplied producer or verifier. Repeating `a` and `b`
bi-infinitely yields two distinct full-shift configurations with exactly equal
images, proving noninjectivity. Fundamental period need not equal the record's
word length for this implication.

Observed exact checks:

- Distinct nonprojection tables with valid collision witnesses: **423**
- Local bit equalities checked: **4,062**, namely twice
  `(164*4 + 179*5 + 80*6)`
- Witness records at length 4: **164**
- Witness records at length 5: **179**
- Witness records at length 6: **80**
- Certified tables plus independently constructed projections equal all **428**
  tables, with empty intersection

The checker additionally exhausts the static truth-table equations for every
binary word of each length `1,...,6` and every one of the 428 rules. It examines
**53,928** rule/word assignments and **274,776** local table lookups. These checks
show that each record's length is the smallest positive collision length for
that particular rule. The numbers of rules with a collision at each individual
length are:

| Length | Rules with a collision at that length |
|---:|---:|
| 1 | 0 |
| 2 | 0 |
| 3 | 0 |
| 4 | 164 |
| 5 | 311 |
| 6 | 417 |

These are individual-length counts, not cumulative counts. Their union has
423 rules, and the first-length histogram is exactly **164 / 179 / 80**. A
length-five collision need not imply a length-six collision, so the individual
length-six count of 417 is consistent with 423 total certified exclusions.

## 4. The five remaining maps

The survivors were independently constructed as coordinate projections. Their
rule integers use the appendix's convention: the output for input integer `w`
is bit `w` of the rule integer.

| Coordinate offset `j` in `F(x)[i]=x[i+j]` | Rule integer |
|---:|---:|
| -2 | 4294901760 |
| -1 | 4278255360 |
| 0 | 4042322160 |
| 1 | 3435973836 |
| 2 | 2863311530 |

All five are bijections on the full binary shift, with inverse offset `-j`.
The `shift` field is a coordinate offset; particle displacement has the
opposite sign. Every survivor table, offset, and rule integer in the original
JSON agrees with this independently constructed list.

Thus every binary, uniform, one-dimensional, full-shift-injective,
finite-configuration-number-conserving CA with neighborhood contained in
`[-2,2]` is one of these five maps. In the stated standard model, a nontrivial
computationally universal reversible number-conserving binary CA must therefore
have radius at least 3. This is only a lower bound; the finite classification
does not construct a radius-three example, determine any larger-radius
classification, or establish a novelty claim. It does not apply unchanged to
partitioned, time-dependent, second-order, nonuniform, or larger-alphabet models.

## 5. Original receipts, integrity, and reproducibility

Both original receipts are consistent with the independently verified JSON.
Their old successful-execution claims were not relied upon; this audit has its
own observed successful fresh-checker execution and machine-readable result.

All six original appendix files were hashed and their modes, sizes, and
nanosecond mtimes recorded before and after the checker. Both manifests are
identical. Separate shell-generated before/after hash and metadata files were
also compared with `cmp` successfully. The audit does not make an atime
preservation claim.

Important SHA-256 digests:

- Original `radius2_certificate.json`:
  `0ea1237d36f1817fccd2f3e415a1b839d1a419ed508df22c2afdd4db008d995b`
- Fresh `check_radius2_graph.py`:
  `dcc06fb639c3b343726db6d46323ef00eec28b7658d24c16deb5e4ae384883e2`
- Sorted complete table set:
  `014f8e6caa2ce078f24f3504c90dd1eaba58214b1c6061ea003c7d140cddf530`
- Independent potential certificates:
  `7bff273900975a6f00c8636f23026a915db9a697b249cd23959198742877d092`

`audit-result.json` records every original digest and metadata value, the exact
spanning tree, all statistics, and checker/output digests.
`fresh-run.stdout.json` is the recorded successful checker output. Re-running
the fresh checker reads only the six original appendix files and writes only
these fresh-audit outputs; no original files are changed.

Reproduction command, after inspecting the fresh checker:

    python3 /workspace/shared/radius-frontier-20261004/fresh-audit-radius2/check_radius2_graph.py

**No mathematical or certificate defect was found in this bounded radius-two
appendix.** Its stated lack of an external novelty claim is appropriate; priority
and the cited literature were outside this independent certificate check.
