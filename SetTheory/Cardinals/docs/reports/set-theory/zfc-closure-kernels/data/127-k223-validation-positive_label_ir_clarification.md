# Bottom, literal Rel(0,0), and positive-label irreflexivity

## The distinction is made before numerical encoding

The uniform interpretation uses an abstract genuine-bottom syntax with distinct constructors `Bottom` and `Rel(a,b)`. It sends `Bottom` to the native falsity code F=1, preserves every membership atom, and sends primitive equality to E. Consequently `Bottom` and the literal atom `Rel(0,0)` have the same encoded image, but they are distinct inputs to the interpretation. Raw renaming changes the latter's labels and fixes only the former. No argument may infer an encoded raw-substitution rule merely from that collision.

This restriction is already explicit in the inherited K224 material: `portable/theory/source116/audit/mathematical_audit.md`, section 1, warns that the tuple generator's qf_spec renamer fixes the tuple Rel(0,0), so it is not an implementation of arbitrary raw-syntax substitution. Its permitted E-body inputs avoid an initial raw Rel(0,0) because each membership atom contains a safe auxiliary distinct from the endpoints. A specialization can produce Rel(0,0) as its target without difficulty. Section 3 then defines tau on genuine-bottom NF syntax and transports the full substitution-free Tarski.Thm proof system by induction on axioms, MP and GEN. It never requires tau to commute with arbitrary raw renaming or substitution.

The finite representative certificates support their explicitly checked endpoints; they are not by themselves the uniform raw-substitution theorem.

## Direct derivation at every hygienic positive label

The following uniform derivation makes the IR premise available without using any raw renaming of the encoded identity `All_0(F->F)`.

Fix x>0 and write

    A = Rel(x,x),
    B = A -> F.

The already established interpreted equality laws include E symmetry, both membership congruences, and the witness theorem `Ex_0 E(0,x)`. In detail:

1. E(0,x) implies E(x,0). This follows from the translated ternary rho7 and E(0,0) reflexivity, or directly by symmetry of the two bidirectional E matrices.
2. The first-argument congruence with endpoints x,0 and third label x gives
   `E(x,0) -> (Rel(x,x) -> Rel(0,x))`.
3. The second-argument congruence with endpoints x,0 and third label 0 gives
   `E(x,0) -> (Rel(0,x) -> Rel(0,0))`.
4. Propositional composition and the numerical equality `Rel(0,0)=F` give the closed theorem `E(0,x) -> B`.
5. Existential monotonicity at label0, followed by the proved witness `Ex_0 E(0,x)`, yields `Ex_0 B`.

It remains to eliminate that existential, which can be done directly from retained membership vacuity and rho6:

6. Since x>0, the retained membership-vacuity row gives `A -> All_0 A`. It is an enabled instance because the requested binder0 differs from both endpoint names x.
7. Existential monotonicity gives `Ex_0 A -> Ex_0 All_0 A`; rho6 then gives `Ex_0 A -> A`.
8. Classical contraposition gives `not A -> not Ex_0 A`. Since `not Ex_0 A` is literally double negation of `All_0 not A`, double-negation elimination gives `B -> All_0 B`.
9. Existential monotonicity applied to step 8, followed by rho6 at B, gives `Ex_0 B -> B`.
10. Combine steps 5 and 9 to derive B, and apply closed theorem GEN at x to obtain

    All_x (Rel(x,x) -> F).

All monotonicity and generalization steps act on closed theorem implications. No open equality premise is generalized. The E-congruence proofs begin with safe auxiliary membership matrices and can produce Rel(0,0) as an output; they never need to rename an input tuple that has already been identified with designated bottom.

Choose the ordinary comparison theory's IR axiom at this hygienic positive label from the outset. Its translated premise is supplied directly by the derivation above. Any ordinary proof manipulation takes place in the distinct-bottom syntax before translation through the complete substitution-free calculus. This establishes precisely the IR premise needed for the conditional-K finite-refutation argument and avoids relying on alpha-renaming the already encoded identity.

## Scope

This is a uniform ordinary finite-derivation scheme using the already established E laws, interpreted equality witnesses, retained membership vacuity, rho6, classical propositional reasoning, MP and closed GEN. It adds no axiom, source edit, test-based generalization or proof-assistant endpoint. It applies to the actual conditional-K 223 calculus and also to the experimental uniform-witness bases once their E laws and witnesses have been established.
