# Independent audit findings

Pinned source: ProveIt commit `76697262071ada91f29c14d9cf3801a64dacb994`.

## Known reductions that must not be advertised as new

- `ipra_one_context_2026-11-11`: crossed one-term-context transport, `s=t, h(s)=u => u=h(t)`; exact consequence equivalence, including seven-rule composition.
- `ipra_kernel_refinement_2026-11-11`, section 5: ordinary left-occurrence replacement `s=t, C[s]=r => C[t]=r`, one hole only, recovers full transport by repeated replacements and symmetry.
- `ipra_uniform_progress`: a root-directed progressive/conditional Q interpretation with reversed iterator orbit elimination; seven rules, smaller than its eight-rule matched comparator, larger than existing witness-sensitive seven-rule comparator.
- Compact incoming envelope: 256 significant tokens / 278 AST nodes / 521 normalized bytes, attained by different programs. These programs assume canonical public goals; they do not enforce the full canonical goal grammar themselves. Strict programs must be compared separately.

## Representation audit

The apparent padded binders under successor and iterator are intentional. The arity decoder maps unary numerical nodes to successor with two dummy zero slots, and ternary iteration to one zero slot in its counter/seed and one genuine state slot in its body. This supports the uniform depth update `5 - len(a)`.

The inherited written proof also addresses fractional fresh coordinates: any additional real coordinates in a newly opened unit interval are fresh parameters, not aliases for the designated integer eigenparameter. The computation-supply branch substitutes zero for all such new parameters before applying an arithmetic theorem. These features are not immediate soundness counterexamples.

Progress at Q-rooted formulas is unsafe with the ordinary Q reading: `Q_z gate(z,P(n))` is equivalent to arbitrary P(n), so allowing its progress introduces full formula induction. Public-goal restrictions do not cure this internal strengthening.

## Self-seeded cancellation investigation

The weaker self-seeded precursor has 0, S, actual-equality Boolean test epsilon, staged F with `F_h(0)=S(h(0))`, `F_h(Sn)=h(F_h(n))`, separation, and literal-equation induction. It already derives quantifier-free induction, coverage, a finite-case right predecessor P, and absence of fixed successor cycles of each fixed standard length. The remaining equation is `P(Sn)=n`; right inverse `S(P(Sn))=Sn` does not imply it.

Here is a supplementary valid stopped-clock fact, but it does not solve cancellation. For fixed a define h_a(v)=v if v=0 or v=a, and Sv otherwise. This is a literal source term using epsilon, Boolean disjunction, and D(c,v)=F_(u.v)(c). Let U(j,a)=F_(h_a)(j). Its base is 1, and quantifier-free induction with a fixed proves

    U(j,a)=Sj OR U(j,a)=a.

For a nonzero, the existing right predecessor gives SPa=a. Specialize the invariant at j=Pa: both alternatives imply U(Pa,a)=a. Then the step equation and SPa=a yield U(a,a)=a. If Sa=Sb with a,b nonzero, the recursor equations give U(Sb,a)=a. If U(b,a)=Sb=Sa, its next step would be S(Sa), different from a by fixed-cycle exclusion; hence U(b,a)=a. Similarly U(a,b)=b. These two stopped clocks induce a preorder-like identification of the colliding branches; they do not yield a=b.

Attempting to shift the original predecessor clock requires `S^2v=S^2n => Sv=Sn` on relevant states. Neither the right-inverse theorem nor the stopped-clock diagonal supplies that implication. No noncircular proof of successor injectivity was found, and no independence model was established.

Finite cyclic tail structures do not provide an immediate countermodel: a parameterized stop-at-a update can have a transient extending past the cycle entry, so its recursor cannot obey the counter's periodicity. A genuine independence result would require a more careful nonstandard branching structure and all staged recursors/induction instances.
