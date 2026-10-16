# Native epsilon / ground closure proposal

This is a complete finite reference interface for a proposed consistency search.
It is not a compiled binary Turing machine, a state record, or a Lean proof.
The ordinary mathematical calibration is in `epsilon_final.tex`.

The input theory is generated from two families: native epsilon-language ground
closure instances and ground epsilon-critical formulas. Closure matrices have
only x,y free; arbitrary closed epsilon terms provide every parameter value in
the ground-term extraction. There are no outer parameter quantifiers in the
primary generator. A finite candidate is accepted
exactly if its generated formulas are propositionally unsatisfiable. The public
checker has no field for arbitrary assumptions or claimed conclusions.

Run the finite regression suite with Python 3.10 or later:

```sh
python test_epsilon_native.py
```

The suite regenerates `epsilon_evidence.json`, the exact generated ground axioms
`native_ground_edge.json` and `native_ground_mixed.json`, the four-slot reference
axiom `native_epsc2_edge.json`, and the generic diagnostic
`generic_critical_unsat.json`. It also regenerates short `.bits` candidates.
Each .bits file stores one ASCII line of binary digits; remove the text
line ending with read_text().strip() before passing it to decode_candidate
or accepts_bits. The decoder itself permits only 0 and 1 and checks exact EOF.
The edge JSON contains a finite shared syntax DAG; its expanded tree has
306,100 nodes. The much larger expanded counts in the evidence are computed
as exact integers without materializing those trees. A retained DAG node count
is distinct from cumulative arena allocation, and neither counts machine states.

`epsilon_native.py` includes:

- two syntactic sorts, canonical DAG interning, and capture-safe substitution;
- the primary two-slot native ground-closure wrapper and a four-slot EPSC2 comparator;
- ground critical-formula construction with scope checks;
- finite exact Boolean checking, plus a direct natural atom-index mask variant;
- a binary candidate serializer with exact framing and backward DAG references;
- mutually decreasing all-natural term/formula codecs and a natural candidate decoder;
- fair bit-string enumeration and the ideal unbounded search pseudocode;
- independent finite-model semantics used only by diagnostics.

`Arena.unsat` can test generic finite formula families for research diagnostics.
`Arena.verify`, `accepts_bits` and `accepts_natural` are the fixed ground-theory
public entry points. `Arena.verify_full_reference` is the earlier four-slot
comparator and cannot be selected through certificate data.
The file `generic_critical_unsat.json` uses extra assumptions to test the logical
interface; it is **not** a refutation of EPSC2 or ZFC. The `.bits` candidates
are valid but nonaccepting finite samples, not evidence for consistency.

The optional `max_atoms` and `max_index` arguments raise `ResourceLimit`; this
never means acceptance. Memory and recursion failures likewise cannot mean
acceptance. `ideal_search` has no such limit mathematically. Do not start an
unbounded run expecting a practical result; its role is to specify the fair
finite-certificate algorithm.

## Attribution and scope

The equality-free EPSC theory, hereditary saturation interpretation, and EPSC2
parameter-budget argument are inherited from the ProveIt sources identified in
`theory_sources.json`. Hilbert's epsilon calculus and ground critical formulas
are classical; the report cites Richard Zach's primary modern exposition.
The native extension uses definable least witnesses inside a model of
ZFC + V=L. It does not assume an arbitrary expansion of a set-theoretic model
preserves schemes involving new functions.

The ordinary proof gives a ZFC-level equivalence between finite Boolean
refutability and inconsistency of ZFC, composing with the inherited ordinary
EPSC calibration. The primary ground construction extracts full EPSC with
arbitrary finite parameter lists; EPSC2 calibration is sufficient but its
special two-parameter packing theorem is not a necessary dependency.
This does not establish calibration for parameter-free EPSC in its original
membership language. A PA version, literal binary implementation, machine-size
comparison, and complete formal proof remain separate work.

