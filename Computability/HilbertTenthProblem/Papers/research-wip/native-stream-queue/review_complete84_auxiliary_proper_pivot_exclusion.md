# Independent review of the proper-pivot exclusion

**PASS within the stated auxiliary circuit model.** The new chronological specialization argument excludes the sixteen proper monomial pivots and leaves direct cancellation to Q open. No author change is requested. This does not prove that every nine-gate circuit is impossible or improve the complete84 upper bound.

The reviewed frozen files are:

| File | SHA-256 |
|---|---|
| `complete84_auxiliary_proper_pivot_exclusion.py` | `ff8f5126e6e04f9c09f47763624e4a4f2d20cb19df42646f43ae7fa9a28fa8d0` |
| `complete84_auxiliary_proper_pivot_exclusion.json` | `1147fab5fb69fcecf3b77c982118af147f5938bc57c786ebed64317c26217793` |
| `complete84_auxiliary_proper_pivot_exclusion.md` | `027c1945025f4bf1e6b9d585ba2befe1af697239787928226b0fd10f868fdf20` |

I read the complete new helper and [companion proof](complete84_auxiliary_proper_pivot_exclusion.md), the full pinned [nine-gate frontier proof](complete84_auxiliary_nine_gate_frontier.md), and the full pinned [mixed-cut proof](complete84_auxiliary_mixed_cut.md). All nine dependencies listed in the new packet were separately authenticated. Predecessor programs were not imported or executed. The inherited frontier classification remains an explicit premise; the present review's new proof challenge concerns its proper-pivot consequence and the exact source boundary.

The paid polynomial space is exactly the span of 1, Delta,c,i,f,T,R,c²,Delta*c². It is not enlarged by the output of a cancellation, and Delta*c² retains its dependence on Delta and c. Every listed pivot has positive i exponent and is a monomial distinct from every paid monomial. Linear independence of monomials therefore places it outside that original span. This guarantees at least one nonzero scalar coefficient among the multiplication outputs available before its addition. The coefficient is a fixed rational, so it survives specialization and can be divided out in the multiplication-only relaxation.

Choosing the latest nonzero multiplication coefficient is essential: after setting i=0, its output is expressible using only specialized paid ports and strictly earlier multiplication outputs. Substitution at all later uses gives a chronological circuit with that product deleted. Nonhomogeneous products and arbitrary additions do not invalidate the scalar-span induction. The argument does not make the whole pivot computation free.

For a proper pivot U, the inherited unique-cancellation theorem supplies a monomial path from U to Q. A nonzero monomial product cannot contain a nonmonomial polynomial factor over this polynomial ring. After scalar aliases are removed, the final Q wire consequently comes from a genuine multiplication later than the pivot addition; otherwise Q would be proportional to U. That product has positive i exponent and becomes zero at i=0. It is absent from the earlier linear relation by chronology. Deleting it first and then the earlier pivot multiplication therefore removes two distinct products, preserving all surviving downstream uses exactly. Other products becoming scalar or zero can only lower the count further.

The specialized outputs are V and W=Delta*f². They are computed from a subset of the original paid ports using at most three products. This contradicts the inherited four-product lower bound even in its more permissive free-linear-combination model. In particular no c³, c⁴ or pivot value becomes a new paid input during this reduction. The specialization is a polynomial lower-bound device; it is not claimed to be a positive compiler tuple.

For U proportional to Q, the mandatory later product disappears from the argument. Only one product deletion is guaranteed, leaving four and giving no contradiction. The statement that this case remains open is necessary and correct. Scalar aliases cause no extra exception: nonzero scaling preserves both the outside-span argument and vanishing at i=0.

Independent finite checks reconstructed all thirty positive-i divisors, the seventeen inherited shapes and the sixteen proper cases. A separate sparse six-variable interpreter checked V,W,Q,S in both saved complete arrays, retaining c² and Delta*c² as the stated dependent paid values. The original full array matches its frozen source receipt. The attaining array differs at exactly the five quotient rows; no deleted private intermediate has an outside consumer. Both complete graphs have 84 live rows, 47M+37A, 25 live supplied ports and 18 positive witnesses. The local output identities and literal surrounding rows preserve the full polynomial and its inherited degree187; no new full lower-count source is claimed.

The independent scratch checks passed, as did fresh normal and optimized exact receipt replays of the new author helper from `/` with dependency root `/tmp`. Only that new helper and fresh review code were executed. These checks authenticate the finite census and complete source interface; they are not a machine formalization of the unbounded circuit proof.

The conclusion remains local to producing V,Q,S from the stated paid interface. It does not exclude additional source dependencies, changed outputs, positive-coordinate charts or changes to the surrounding norm and finalizer. No repository or frozen author file was edited.
