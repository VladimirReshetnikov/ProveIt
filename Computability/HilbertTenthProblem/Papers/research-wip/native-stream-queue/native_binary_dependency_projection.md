# Bounded dependency guards and a materialized Wang example

Two implementation-only guard changes replace full free-input dependency
sets with their exact intersections with the names each guard queries.
The emitted arithmetic sources, accepted guard contracts, positive-domain
proofs and frozen receipts are unchanged. This permits the previously
oversized [erasing-TM bridge example](wang_b_erasing_bridge_compiler.md)
to be materialized and audited as a complete ordinary-input polynomial.

The actual complete example has **312,942=118,706M+194,236A** operations,
312,866 certificate operations,25 comparisons,23,763 positive witnesses
and degree **at most12,092,924**. Its only parameter is the ordinary
positive input x. This is the same illustrative erasing machine, not a
universal table or a reduction of any universal arithmetic bound.

The [audit source](native_binary_dependency_projection.py) and
[receipt](native_binary_dependency_projection.json) reconstruct both
legacy guards, compare them with the optimized guards, and then emit and
check the complete example in a resource-limited worker. No enormous
source JSON needs to be checked into the repository: the deterministic
builder materializes every gate and records exact hashes and counts.

## 1. Exact dependency projection

For a fixed set W define pi_W(S)=S intersect W. For all sets A,B,

    pi_W(A union B)=pi_W(A) union pi_W(B).           (1)

The old guard assigns each free input v the singleton{v}, each numeral
the empty set, and each computed register the union of its two operands'
dependencies. The new guard initializes{v} only when v belongs to W,
otherwise the empty set, and propagates exactly the same unions.
Induction over the source using(1) proves

    new_dependencies[r]=old_dependencies[r] intersect W

for every register r. All keys are retained. In particular an unknown
register still raises the same lookup error; a numeral is still empty.
This is syntactic dependency, so even a row v-v retains v's dependency.
No algebraic cancellation or value-based independence is assumed.

In [the positive-scale guard](native_binary_positive_scale.py), the sole
dependency query intersects dep(q) union dep(r) with{w,beta}. Thus W has
size2. In [strong normalization](native_binary_norm_units.py), every
query intersects with the rebuilt private coordinates{f,i,j,o,y_aux},
so W has size5. This includes the retained comparisons, unit factors,
scale/core inputs and recursive public/interface leaves. Every old query
therefore has exactly the same result after the change.

The arithmetic rewrite following each guard is untouched. The changes
cannot admit a formerly rejected dependency, reject a formerly accepted
one, change a supplied coordinate or emit a different gate. Dependency
storage is now O(|W|N) instead of allowing O(IN), where I is the number
of free inputs and N the source size. This statement concerns these two
guards, not every part of the compiler or its overall runtime.

## 2. Regression checks against the full-set implementations

The checker reconstructs the original functions by changing only the
initial dependency sets back to full singletons. It compares complete
returned packets on18 normalized-unit hosts and7 positive-scale hosts:
standalone AND, motion, toggle, and several actual Wang programs with
both endpoint interfaces. All packet dictionaries agree, including the
literal sources, comparisons, witness lists and inherited metadata.

Across these hosts, nested adversarial exports and64 additional finite
DAGs,40,792 register projections agree exactly with the full dependency
sets. There are90 rebuilt-coordinate rejection cases,14 private scale
consumer rejections, and18 harmless extensions accepted by both versions.
The rebuilt cases include a cancellation followed by a transitive path
and a nested public export. They remain rejected because these are
syntactic dependency guards. The synthetic DAGs separately check both
watched-set sizes under arbitrary addition, subtraction and multiplication.

Fresh default replays of the positive-scale helper, native norm-unit
helper and [computed-action Wang compiler](wang_b_computed_actions.md)
pass against their existing receipts. Those receipt files are unchanged.

## 3. Actual large source and complete framed composition

The unchanged record compiler turns its default one-nonhalting-state
erasing example into42 block controls and1,481 nonhalting binary
non-erasing states. The frozen Theorem7 expansion has19,254 Wang
instructions,4,443 jumps and23,697 physical control edges.

The actual computed-action literal Wang child now materializes with

    certificate=312723,
    polynomial=312749=118610M+194139A,
    comparisons=9, positive witnesses=23725,
    degree upper bound=6046462.

The hash of repr(the complete ordered polynomial source) is

    ea40aeb6c0aeb08000c1f9fc38ea91174d4b5276e9ec31c6a8a69319207693b5.

Every one of its312,749 gates is an ancestor of the output. The degree
bound is recomputed on the actual guarded native source, and checked
against the frozen Wang bound; no exact degree is claimed.

The record compiler's emitted190-operation input loader supplies the
positive framed word

    y=523615+401563648*frame_repunit+32768*z.

The new audit gives the loader and Wang sources disjoint register and
witness namespaces, replaces the child's input leaf by this computed
port, and appends exactly two squares and one addition:

    complete_output=loader_output^2+wang_output^2. (2)

The full312,942-gate source is actually assembled, checked for unique
producers and available operands, and traversed iteratively from its
output. Every gate is an output ancestor. There are25 comparisons and
38+23725=23763 positive witnesses; the only parameter is x. Actual gate
counting gives118,706 multiplications and194,236 additions/subtractions.
The affine input substitution preserves the child's degree envelope, so
(2) has degree at most2max(402,6046462)=12092924.

The complete ordered-source hash is

    aae419b3e69f5d84f633c0afd257aa43bd570b2a2c6ca3ae3942ad86590e5416.

Four bounded off-zero assignments independently evaluate the two old
component sources and the assembled source. Every renamed register
agrees and(2) holds exactly. The history edge hats are1, giving zero
edge words and P=1, to keep this large-source audit's integers bounded.
These are namespace and whole-output identities, not claimed positive
Pell zeros or accepting computational histories.

The bridge's historical312,967-operation formula remains a valid
conservative bound. The smaller312,942 count is now measured on the
fully emitted schedule; it does not arise from a new arithmetic rewrite.
The two guard optimizations change only the resources used to verify
and construct that schedule.

## 4. Replay and resource scope

```sh
python3 native_binary_dependency_projection.py
```

The large worker has a3,584MiB address-space limit,150-second soft CPU
limit and180-second wall alarm; the parent also imposes a185-second
subprocess timeout. The deterministic receipt excludes observed timing
and peak resident memory. A successful author writer took21.174 seconds
inside the worker and reported444,668KiB peak RSS on this environment.
Those measurements are observations, not cross-platform performance
bounds or promises. The full source and its ordinary-input semantics
remain the same if another environment takes different resources.

Author receipt generation and a fresh default replay pass; all six local
links resolve. Independent root review checks the complete source and
projection proof, every dependency query in both helpers, the disjoint
composition and its degree envelope. Restoring the single initialization
in each modified helper makes its entire module AST identical to the
committed predecessor; there are no other implementation changes.

A separate fresh root replay passes all small audits and reconstructs the
complete source with the same counts, hashes, ancestor closure and four
whole-output identities. Its large worker observed20.161 seconds and
444,672KiB peak RSS. No frozen arithmetic receipt is modified by this
packet. The finite evaluations do not assert a full positive Pell zero.
