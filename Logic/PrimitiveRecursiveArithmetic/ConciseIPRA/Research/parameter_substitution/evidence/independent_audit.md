# Independent audit: raw parameter-only equality

## Assessment

The proposed raw calculus is equivalent to the inherited raw Eq/D clause calculus, provided its rules have the stated freshness and typing conditions. The reduction needs no term normalization, equality characteristic, numerical induction, or full formula transport in its bootstrap. It genuinely weakens proper-subterm replacement to free numerical parameters; arbitrary numerical sources are handled only at the root.

The five instruction families are Compute (the two iterator computations), ParamEq, Use, Open, and Close. Calling Compute one family does not turn its two computation cases into one axiom; comparisons should count its branches consistently with the inherited Eval instruction.

## The equality operation

Given proved equations s=t and u=r, ParamEq returns r=Psi(s,t,u), where:

- if u is literally s, Psi=t;
- otherwise, if s is a free numerical parameter, Psi=u[t/s], with ordinary capture-free, one-pass parameter substitution;
- otherwise Psi=u.

The root case takes priority. Free-parameter substitution is not repeated until a fixed point, even when t contains s.

## Bootstrap, in a noncircular order

1. Put W(a)=I(0,a;v.0). Compute gives W(a)=a. Using this equation as both ParamEq premises invokes the root case and yields a=a.
2. In particular 0=0 is derivable. ParamEq with major 0=0 leaves its minor's left term unchanged: the root case returns 0 when that term is 0, and the nonparameter fallback returns the term otherwise. Thus u=r yields r=u.
3. Common-left joining is immediate: s=t and s=r yield r=t. Together with symmetry it gives ordinary transitivity.
4. For an arbitrary term s introduce the alias D_{b,y}(C(y,s,b)=s), where C(y,a,b)=I(y,a;v.b). At witness s, the successor branch C(Sz,s,s)=s is exactly a successor computation axiom. The local assumption is unused, so the proof works in either witness-selected Close mode.
5. Open the alias at fresh b. Its clause antecedent C(0,s,b)=s is a zero computation axiom. Use at 1 gives C(1,s,b)=s. A successor computation gives C(1,s,b)=b. Common-left joining, with these premises in the appropriate order, yields b=s.
6. Given s=t and h(s)=r, work under this alias. Derived reflexivity gives h(b)=h(b). ParamEq at free source b and major b=s yields h(b)=h(s). Transitivity gives h(b)=r, and b=s together with s=t gives b=t. ParamEq at source b now yields r=h(t). Close Open because b is absent from the retained context and desired conclusion.

This recovers crossed transport in every term template. The template is used only in the metatheoretic derivation; it is not supplied to the primitive equality instruction. Only the alias's fresh free parameter is replaced properly inside h(b).

## Equivalence with the inherited kernel

Every new rule is sound in the old calculus. ParamEq's root case is common-left joining; its parameter case is an ordinary crossed-transport instance with template h(v)=u[v/s]; its fallback is symmetry. Both computations and the clause rules are inherited.

Conversely, the preceding derivations recover Refl and full crossed term transport. The old computational-equality Eval cases then follow from the two computation axioms and transport. Hence all sequents in the unchanged Eq/D language with reusable clauses agree. The inherited native/iPRA bridge supplies the whole-domain interpretation and identity numerical composites; no new arithmetic equivalence theorem is assumed.

For the single Close rule, ordinary case introduction at an equation with literal witness 0 can be repaired with W(0)=I(0,0;v.0), which is not literally 0 in this RAW syntax and is provably 0 by Compute. Only atomic term transport is needed for this repair. Prove full formula transport afterward. The normal-form complication from the previous candidate is absent.

Direct admissibility of arbitrary parameter substitution in the primitive rule need not be claimed: substituting a compound term for a free source changes which ParamEq branch applies. Full transport and the equivalence translation supply the admissible substitution theorem instead.

## Implementation review

Inspected file: agent_kernel/neutral_marker/raw_parameter.py.

The generalized opening routine correctly distinguishes positive bound indices from negative free levels. For a positive index it increases the index when descending under a binder and decrements larger bound indices after opening. For a negative index it keeps the index fixed and substitutes matching free levels without changing positive bound indices. Values inserted by the rule interfaces are well scoped with no free positive index, so no additional lifting of the inserted value is required.

The term validator distinguishes integer leaves from booleans, validates successor tags, recognizes the iterator's bound body, and validates Eq/D formulas at their correct binder depth. Invalid computation counters are rejected by validation or by unpacking failure, caught by the public driver. Major or minor non-equations in ParamEq likewise cannot pass the unpacking and derivation invariants.

Independent bounded denotational validation used a fixed random seed and 3,000 nested-term cases for each of three operations: opening bound index 1, opening bound index 2 while retaining the other variable, and substituting a negative free parameter. All 9,000 comparisons agreed with direct evaluation under the corresponding changed environment, and all results retained the expected scope. This is test evidence for the binder implementation, not a machine-checked proof of the calculus.

No defect was found in the mathematical reduction or inspected implementation.
