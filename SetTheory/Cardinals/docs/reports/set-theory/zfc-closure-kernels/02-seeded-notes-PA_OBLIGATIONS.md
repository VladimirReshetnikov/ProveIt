# Certification interfaces

The required final statement, for a frozen literal machine M, is
`PA |- Halt_blank(M) <-> exists p Prf_ZFC(p, bottom)`.
The article gives mathematical calibration proofs, not an exported PA proof.

## Freeze the interfaces first

Specify classical first-order syntax, formula coding, bound-variable
conventions, the exact ZFC schema list, proof records, and the TM semantics.
The machine convention must include alphabet size, initial state, blank
symbol, halt convention, and whether the halt state is counted.

ZF_0 in this report uses functional Replacement, full Separation, and no
Foundation or Choice. Do not silently replace it by a foundation-free
Collection presentation. For equality-free Q_sub, arbitrary equality-free
matrices are allowed and the entire schema wrapper is equality-free.

All parameters are universally closed. The seed and output variables are
fresh for the matrix; an intended seed may occur as an ordinary parameter
and then be instantiated to the actual seed variable. Certificates should
carry the matrix and fresh-variable data, rather than relying on reverse
pattern matching to recover them.

## Core proof constructors to implement

Implement finite derivation constructors for Empty Set, singletons,
Separation, Power Set, two-cycle Pairing, membership-closure Union,
Russell-rooted partial functional images, and successor-closure Infinity.
Implement the reverse closure derivation by exact-fiber formation and
positive omega-iteration. The source formula is a syntactic parameter in
these fixed proof templates, not an input to a semantic decision procedure.

For Q_sub implement equality translation:

`D(x,y) := forall z (z in x iff z in y)`

`EC := forall x y (D(x,y) -> forall w (x in w iff y in w))`.

Prove substitution for every formula by syntax induction. The translated
Extensionality axiom is a tautology; translated subset-seeded closure axioms
are literal allowed schema instances. In the reverse direction Extensionality
and logical equality derive EC. Deleting EC is not covered by this proof.

For each direction, certify a primitive-recursive proof transformer f:

`PA |- Prf_source(p,bottom) -> Prf_target(f(p),bottom)`.

## Standard bridge: ZF_0, ZF, ZFC

The standard effective well-founded/constructible-class reductions stay in
the correctness proof, not in the machine. Implement formula relativization
and uniform expansions of every translated axiom instance, then verify the
transformation by induction on finite proof codes in PA. A proof in a stronger
proof assistant that a class has certain mathematical properties is not by
itself the required internal PA theorem. The report relies on the standard
syntactic bridge and does not distribute its mechanization.

## Enumerator and backend

Prove soundness and completeness of the certificate checker. Prove fair
enumeration of every finite certificate. The checker must halt on each finite
candidate, including malformed candidates. Then prove
`Halt(search_T) <-> exists p Prf_T(p,bottom)` in PA.

Compile to the selected register or stack language and then to the exact TM
model. Verify initialization, tape invariants, transition simulation, and
halting in both directions. Audit optimization certificates and state merges
against the literal final table. The table digest, not a theorem name or
source-code length, identifies the final object.

## Target encoding

A positive theoremhood presentation is an auxiliary search theory, not a
ZFC-equiconsistent theory. Replacing bottom by the closed formula
`H = forall x y E(x,y)` is justified only with the stated explosion and
reverse-calibration proofs. An open off-diagonal atom may be a theoremhood
target after universal-generalization checks, not a bottom macro inserted
inside arbitrary formulas. Diagonal-falsity aliases require their own
refutability hypotheses; do not remove irreflexivity from an inherited
machine while keeping that alias without a new soundness argument.

## Not provided in this archive

No serialized PA proof, full proof checker, theory proof compiler, proof
assistant build, new TM table, or independently verified minimality claim.
`code/` implements formula metrics and finite regressions only.
