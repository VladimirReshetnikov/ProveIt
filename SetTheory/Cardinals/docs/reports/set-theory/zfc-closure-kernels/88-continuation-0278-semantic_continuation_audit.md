# Semantic continuation quotient: proof and novelty audit

## Result of the prior-art check

The proposed change—accepting a canonical output PC whose next guarded source
instruction is bisimilar to the originally prescribed successor—is not the
same as the prior packages' "semantic" frame searches.

- Archive2's `agent_states/semantic_search.cpp`, function `matches`,
  compares `ex.pc` bit-for-bit. It relaxes head position, separator gap,
  and spare-list shape only.
- Archive1's `semantic_frame_folds.cpp`, function `same_frame`,
  compares the first40 padded PC bits bit-for-bit. Its maximum source
  address depth is at most34. It likewise relaxes only workspace geometry.
- Archive5's finite-block algorithms generate specified finite descendants
  with exact primary-register offsets, with a maximal13 source instructions
  in the stored arithmetic-block endpoint family. They do not form an
  arbitrary guarded-continuation bisimulation quotient.
- Archive1's grammar campaign called "Semantic continuation" is continued
  annealing of semantic sequence-word grammars, not this runtime relation.
- Archive2's `finite_quotient_frontend.md` is a quotient-model encoding
  for a different finite ground-theory checker; it is unrelated.
- Archive3's `map_chain_semantics.py` associates failing source leaves
  with older helper names using in-order ancestry. It is not a quotient.

This is a concrete new search relaxation relative to the inspected six
packages. No claim of historical novelty of bisimulation or compiler
continuation sharing is justified or needed.

## Independent source calculation

`audit_work/independent_cfg.py` parses the actual `Prog254.v`
literal table without importing any delivered checker. It checks all6459
tree rows, each node's DFS occurrence, all6460 leaves and8390 successor
edges. Path arithmetic is read from the actual RegisterPath source:
increment modulo2^length, break as strip-zero followed by increment,
continue as strip-one, and implicit zero padding on the next decode.

Successor arrays use zero before positive for a decrement.

The independent coarsest partitions are:

| Labels | Classes | Nonsingleton classes | Largest class |
| --- | ---:| ---:| ---:|
| Literal instruction kind and argument (including exact break/continue) |6217|243|2|
| Same, except all break/continue instructions have the semantic no-effect label |6214|246|2|

The JSON gives every leaf, exact successor array, both class vectors, and
the refinement history. The quotient statement is purely about source
continuations, not binary state count.

## Soundness theorem for a strong guarded quotient

Let V be a finite set of source leaf occurrences. Each v has one of labels
`halt`, `inc r`, `decnz r`, or `noop`. Halt has no successor;
inc/noop one; decnz has an ordered zero and positive successor. Break and
continue may both have label noop because their effects have already been
resolved into the occurrence's exact successor.

A partition pi is stable if equivalent leaves have the same label and their
corresponding successors have equal pi-images. For every vector R of natural
register values, configurations (v,R) and(w,R) with pi(v)=pi(w) then have the
same halting behavior. In fact their executions match one source step at a
time: the common label selects the same guard, induces the same updated
register vector, and stability relates the successors. This argument covers
divergence and control cycles; it does not assume termination or fairness.

A convenient proof is simultaneous induction on finite source halting length.
A halt class is terminal on both sides. For a nonhalt class one step gives
identical register updates and another related pair; apply the induction
hypothesis. Swapping the related pair proves the reverse direction.

The binary relation may therefore bind a complete dispatch frame to the class
of its actual next source leaf and its exact nine primary values, instead of
binding the literal PC word to one prescribed representative. A passing binary
instruction contract must still:
1. read a complete canonical clean PC frame with adequate gap and spare suffix;
2. perform a positive finite literal run;
3. update the primary registers by the source instruction's exact operation;
4. restore a complete canonical clean dispatch frame;
5. land in the class of the prescribed guarded source successor.

All possible actual starting leaf representatives must have their contracts,
not just a selected class representative. The finite boot must enter a safe
class with the intended primary vector. Accepted full-tape contracts and
class stability then compose by the same finite induction as exact-PC
simulation.

The binary frame still needs the no-stray-bit invariant. RegisterPath itself
truncates the old PC to the consumed leaf depth before updating, but the
binary runtime is certified on zero-filled gap after the consumed path.
A nonzero residual suffix cannot be silently hidden by matching only the next
leaf's class. Absolute origin, excess gap and unobserved spares may be hidden
only according to the already proved complete-frame rules.

## Why unrestricted weak bisimulation is different

One may be tempted to skip arbitrary control-only chains and quotient their
visible continuations. Halting equivalence of the SOURCE is easy to prove
after separating control-only divergence cycles. However, using that weak
equivalence as an unconstrained BINARY acceptance criterion can lose progress.

A mutated binary machine could repeatedly return to a different control PC in
the same weak class, making positive binary steps but never executing the next
visible increment/decrement. All such local endpoints could look weakly
equivalent although the source would eventually halt. Positive binary duration
does not itself rule out infinite abstract stuttering.

A sound extension needs one of:
- each accepted macro executes at least one visible source instruction;
- a strict well-founded control-distance rank on silent transitions;
- a bounded-stuttering simulation certificate that supplies equivalent data.

The strong guarded quotient described above has no such gap: every matched
binary macro realizes one genuine source step in the class transition system.

