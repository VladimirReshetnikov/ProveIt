# Exact audit: four-field entry reservation

**Inspected program:** `agent_kernel/entry_four_bytes.py` on 2026-11-13, with packet `[s,u,t,m]`, eager opener, initial context `[[]]`, strict phase `k == 0`, and successor image `[k]`. The inspection is a mathematical review, not a proof-assistant certificate.

## Theorem

The replacement of return-time allocation by the entry reservation in this program preserves the ordinary theorem set of the inherited four-field calculus, provided the following existing facts about its codec are used: successful no-image scans preserve the sorted reading and validate its scope; opening a validated template gives its numerical substitution reading; direct computation leaves with the repaired zero counter `1` are sound; and canonical native derivations compile to the four-field rules. In particular the change introduces no stronger induction principle.

## Exact order and scope

Let `K` be the global floor at a call's entry. Python evaluates `i(a)` before the right-hand membership tuple, so the goal is scanned at `K`. It then evaluates `(k := k-1)` before either the existing context or the computation candidate. Thus the public root alone is scanned in strict mode, and all later opening is auxiliary.

The eager fallback evaluates its image even at even depths. With the missing-image function this fails; therefore a successful no-image scan contains no out-of-range raw scalar. This is stronger than the corresponding property for a short-circuit opener. Its scalar outputs are either admitted scalars at least `K`, or the zero alias `1`, and its other outputs are arrays. The new marker `K-1` consequently cannot equal the scan result. Adding that marker to the membership tuple does not add a terminal proof.

The extra name first admitted after the scan is an unconstrained numerical parameter. The exported goal and prior context were already scoped at the older floor, so this change is ordinary parameter weakening. They cannot acquire a dependence on that name merely because the floor decreases.

## Why the delayed endpoint test is safe

For a nonterminal call Python constructs the new context argument before the new goal argument. The expression `m*3 or (a := i(*a,t,2))` is evaluated before the major call `c(g,m)`. The major is scanned at the current floor and that call then reserves at least one lower value. Its returned `k` is therefore fresh for the old context, the major, and any witness-instantiated matrix just constructed.

The endpoint equality and the instances `i(t,s)` and `i(t,u)` are evaluated **after** that major call. This does not create an eigenparameter leak; the cases are distinct:

* **Transport:** the matching major is the binary tree `[s,u]`. The added hypothesis `m*3` has arity six and reads as neutral truth. There is no witness discharge or induction eigencondition in this case. Any extra parameter in the template is allowed by ordinary parameter weakening. The target instance is literally the old scoped goal. The source instance and the proven equation give that target by transport.
* **Closure specialization:** the matching major is the ternary tree `[t,t,t]`. Its repetition has arity nine and is again neutral truth. The major's older scan already scopes its matrix `t`. The chosen numerical target can use a newly admitted parameter; specialization permits this, and its target instance is required to equal the old goal. There is no witness discharge here either.
* **Paired elimination:** its major is unary, so it cannot equal either endpoint major above, of arity two or three. The endpoint branch is therefore not selected. The exported goal remains the old goal, which is fresh for the returned `k`, and opening the major adds the required closure at that fresh witness.
* **Introduction:** its accepted false-valued major is the neutral empty array. It likewise cannot equal an endpoint major. The matrix at the chosen witness was opened before the major call, and the returned `k` is fresh for it. The hypothesis is its value at `k` exactly when `len(a)==2==u`, and at zero otherwise. The first condition permits progression only for a literal binary equation with the explicit marker `u=2`; compound matrices use numerical cases. The continuation is its value at `S(k)`.

This case separation is the reason no blanket claim that “every pre-opening happens before the major” is needed or correct. Only the witness pre-opening must precede the major. Delayed equality/closure instances belong to inferences with neutral added hypotheses and no eigenparameter discharge.

## Computation leaves

The raw repaired candidate is compared with a goal scanned at the older floor. If it matches, its left side and repeated seed have that same validated spelling and ordinary reading. For a false-valued source it is zero iteration, with `1` the canonical zero spelling. For a true-valued source it is successor iteration; the right opener validates the recursive image when the state occurs. If the state is absent, that image is irrelevant. This is the established direct-leaf argument, including dummy-slot erasure. Admission of extra parameters while constructing the candidate does not enlarge the class of matched old-floor goals.

## Completeness and limits

Compile native derivations using a finite environment of abstract eigenparameters and the actual entry-allocation schedule. Every major call reserves at least one new name, so its returned floor supplies a fresh eigenparameter whenever one is required. Additional unused entry names need not occur in the certificate. Terminal pruning and packet order follow the existing canonical compiler. The new program therefore proves the same ordinary formulas, but old certificates need not work without renaming/recompilation.

The claim is equivalence of ordinary theorems under this certified scheduling change. It is not equality of all accepted raw JSON inputs, not a smaller mathematical axiom basis, and not a proof of a global minimum for proof-checker size.
