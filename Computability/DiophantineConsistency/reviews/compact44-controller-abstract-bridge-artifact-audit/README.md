# Source and artifact review: symbolic compact controller unit

Reviewed commit `9c6fc48668`. The final declaration
[`CompactActualUnitTransport.actual_unit`](../../research/ordinary12-ipra-bridge/compact44-controller-abstract-bridge-prototype/ActualUnitTransport.lean)
has the stated coefficient `(paramKernel rho : V)` and **no residue
premise**. Its assumptions are the displayed `ORingStructure` and IΣ₁-model
instances; `m` and `e` are arbitrary model elements. It concludes existence
of an inverse for the defined `Gamma` modulo `590069*581197^(m+1)`.

The four-stage transport has the expected orientation. The first unit client
retains the alias residue as a premise; the independent numeral client
transports the checked alias residue from the modulus abbreviation to the
numeral; the third client supplies that premise; and the final `congrArg`
transports the alias theorem along `kernelAlias_eq` to the actual symbolic
kernel. The relevant conditional unit theorem and alias equality have
separate [unit](../compact44-controller-unit-mathematical-source-review/README.md)
and [alias](../compact44-symbolic-kernel-alias-source-review/README.md)
source reviews. No defect was found in the inspected four-stage composition.

[`audit.py`](audit.py) checks the retained four-stage receipt and runner, the
four repository and live frozen source hashes, the four output objects and
logs, the four prior same-side objects, and the checked alias object. The
recorded dependency listings name the expected direct stages; the four logs
contain exactly the expected axiom reports (`propext`, `Classical.choice`,
and `Quot.sound`) with no warnings or `sorryAx`. The normal audit exited 0;
optimized Python was rejected. It does not rerun Lean or independently
regenerate dependency listings.

The build is incremental and single-author. The prior objects and alias are
hash-checked at the runner's start; the listing and object checks here are
point-in-time, and do not exclude intervening mutations or authenticate the
transitive, package, dynamic-loading or full project closure. The earlier
controller-data stage has the separately documented linter warning. The live
`/tmp` objects are required to repeat this audit.

This is a model-level unit theorem for the symbolic expression. It does not
identify retained file or PDF bytes, prove `Gamma` is the actual packed-rank
variation, construct safe dummy locations or a positive graph zero, or
establish an internal iPRA equivalence.
