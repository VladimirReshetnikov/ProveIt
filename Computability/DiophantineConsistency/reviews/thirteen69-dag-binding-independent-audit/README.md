# Independent 69-row model binding audit

The read-only audit of `047484be73` actually exited 0 in session 6599; its
[receipt](CHECK.json) and [terminal observation](terminal-observation.json)
bind the result. A separate parser in [audit.py](audit.py) compared the
ordered operand and operation of each of the 69 Lean node definitions with
the pinned JSON rows, including the thirteen variable indices, four port
slots and output. It checked topological order, that all nodes contribute to
the output, and the histogram of 39 multiplications, 16 additions and 14
subtractions. This is an external source comparison, not a Lean theorem
about parsing JSON, nor a 69-operation claim about the unshared syntax after
positive shifting or about decimal numeral size.

The audit checked both 64-link project provider overlays, four rebuilt
source/object chains per side, all eight recorded compiler and eight direct
dependency exits, and the author's outer session 17498 exit 0. The parent
comparator was rerun and exited 0. Both copies of each object match. The
compiler reports contain only `propext`, `Classical.choice`, and
`Quot.sound`, and no warnings, errors, or `sorryAx`; these are Lean
metatheory axioms, not added object-theory axioms. No Lean compilation was
rerun by this audit. Foundation's original outer-wrapper exit and complete
package-transitive/dynamic ancestry remain inherited qualifications; the
temporary provider tree is required to reproduce the artifact checks.

The Lean scalar equality is quantified over arbitrary commutative rings and
arbitrary four-port and thirteen-coordinate inputs. The internal and shifted
zero theorems require the ordered natural-like semiring and difference-ring
instances specified in the source. The fixed 2011 specialization uses exactly
`(beta, K, lowPort, highPort + beta)`, with beta=(2^47)^2011−1 and K the
source-defined `rawWord radix`; it shifts each coordinate by one. The
phase-split2471 graph's frozen beta is 2^(47·2471)−1, so the fixed tuples
are distinct even though the symbolic row theorem admits either tuple.
The audit did not independently recompute the entire 2011 K or mask digits;
the exact definitions are inherited from the pinned 70-source provider.

This binding does not determine the exact degree after 2011-port
specialization, prove the all-model carrier converse, calibrate the
phase-split tuple, or construct an internal iPRA proof. Earlier global
expansion failures and their incomplete transcript retention are described
in the canonical-binding packet and are not promoted to proof evidence.
