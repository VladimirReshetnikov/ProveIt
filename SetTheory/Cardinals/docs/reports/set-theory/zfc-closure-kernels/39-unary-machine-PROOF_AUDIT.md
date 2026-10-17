# Independent proof audit: unary support barrier and finite Pairing repair

Audited on 2026-10-16 by the machine-investigation subagent, independently of the authors of the two arguments. This is a mathematical proof audit, not a proof-assistant certificate or an exported arithmetic proof-code translation.

## Audited versions

| Source | SHA-256 |
| --- | --- |
| `research_theory/unary_support_theorem.tex` | `6970712cde71f097866f8a62d77b8753844b6465a93ed03ef52d158a2eda18ff` |
| `research_repo/support_deletion.tex` | `008791fd850e1eccd737337b9e622c3101380d805deffb1231372763740ea521` |

The first source includes the one-support construction, bilateral-chain variant, extensional Pairing fallback, equality-free repair `EPSC_1 + DP`, fixed two-parameter exception `Theta`, and fused schema `P-EPSC_1`.

## Verdict

No substantive mathematical flaw was found in either the countermodel arguments or the finite Pairing repair. The new interpretation of full extensional EPSC in `EPSC_1 + DP` respects the one-free-parameter budget throughout. Its advertised ZFC consistency calibration additionally relies on the separately cited unrestricted EPSC/PSC calibration; this audit checks the new bridge and does not replace that upstream calibration proof.

Two earlier presentation issues were corrected before the versions recorded above: an omitted LaTeX backslash, and wording that could have confused the well-founded part in the intended ambient universe with external well-foundedness in an arbitrary nonstandard starting model. The support-deletion text now consistently uses incoming-profile equivalence `Delta` for its separating constant matrix.

## 1. The extensional tagged universe

The primitive nodes have prescribed singleton extensions. Ordinary constructors representing these same singleton extensions are excluded. That exclusion is exactly what is needed for injectivity of the extension map: two primitive nodes have distinct singleton extensions; two retained ordinary nodes agree precisely when their extension sets agree; and no retained ordinary node has the extension of a primitive node.

For any ambient set of nodes, Replacement bounds the least construction stages of its elements. It therefore has a representative at a later stage, apart from the explicitly normalized primitive singleton case. Both identities `ext(rep(X)) = X` and `rep(ext(u)) = u` hold. Coding nodes as ordinary tagged sets does not require their actual set membership to reproduce the interpreted relation.

The permutation action is defined by construction rank, so it does not recurse along the cyclic interpreted membership relation. The hereditary condition guarantees that every member and every descendant of a domain object remains in the domain. If a set of domain nodes is invariant under a stabilizer of at most one index, its representative satisfies the same support condition; all lower descendants already satisfy the hereditary requirement. No closure of the support family under unions of supports is being assumed.

## 2. Exact fibers and proper-class interpretation

The crucial fiber argument is valid. For a fixed translated formula and input, choose any local subset bound `b`. Heredity makes interpreted subset inclusion equivalent to inclusion of actual member extensions. Every possible output is therefore in the ambient set

```
{ rep(S) : S is a subset of ext(b) }.
```

Separation forms the exact fiber inside this set. This exact fiber is unique independently of the chosen bound, so Replacement collects fibers over a set of inputs. There is no need to choose bounds simultaneously, no appeal to a global choice function, and no assumption of a uniform truth predicate for the proper-class structure. Each fixed formula is translated syntactically into a fixed ambient formula.

For a one-parameter matrix, every permutation fixing a support of the parameter preserves its translated truth relation. The iterative exact image closure from the unique empty node is therefore supported by that same set of at most one index. The stage argument proves both ordinary EPSC and the asserted stronger least exact fixed-point property. The text correctly treats the latter as an additional property of the model, not as an unproved deductive consequence of EPSC alone.

Taking `I = omega` makes the ambient interpretation parameter-free. Proving its individual translated axiom instances by syntax induction is compatible with relative syntactic interpretation and does not assume an externally well-founded set model of ZFC.

## 3. Finite containment, H, and the separating pair

The full permutation group `Sym(omega)` is an ambient set. Hence the orbit of an ambient set of nodes is an ambient set, even though the complete universe of nodes is a proper class. The full orbit of any fixed finite tuple has empty support and supplies a common membership container. Applying the same operation to the union of their extensions supplies a common subset bound. Iterating member extensions supplies transitive common bounds.

Internal incoming-profile equivalence is actual equality because the domain is hereditary and the ambient extension map is injective. Thus every object is saturated. The transitive member closure of any one-supported object has the same support and gives the witness required by `H`; consequently `H` is the whole domain.

The exact pair of primitive nodes at distinct indices has no support of size at most one. Given a proposed such support, swap an unprotected selected index with a fresh index. The extension changes. Extensionality prevents a different representative from avoiding this obstruction. A common subset bound nevertheless exists, so bounded Pairing really fails. The explicit two-parameter matrix `J` likewise forces precisely the three-member extension consisting of the empty object and the two selected primitive nodes.

The bilateral-chain modification preserves all representation and support arguments. Ordinary membership edges decrease construction rank, and primitive membership edges advance the integer phase uniformly, so finite directed cycles cannot occur. Foundation still fails on the represented full chain at one index. The source correctly distinguishes these assertions.

## 4. Deleting support

The unrestricted support-free closure proof does not require the parameter tuple to have one support. At each stage it takes the exact image under the fixed relation and then closes the resulting set under the entire set-sized group. This restores full invariance. The next stage processes all newly inserted inputs, so iteration still establishes recurrent closure.

This argument remains valid when the parameter tuple destroys full-group equivariance of the relation: no such equivariance is used. The relation need only have the assumed local bounds, which suffice for its exact fibers to be sets. The resulting representative belongs to the hereditary one-support domain because it has empty support and every inserted node is already a domain member.

For the constant relation selecting the two distinguished primitive nodes, the construction produces the full orbit at that phase. The extra orbit members lack relation-preimages. This identifies exactly why the support clause cannot be restored. The conclusion is a deductive separation and failure of the specific inherited interpretation, not a separation of consistency strengths.

## 5. Extensional Pairing fallback

Pairing and Extensionality suffice to construct Kuratowski tuple codes of each fixed finite length and prove coordinate uniqueness. The proof does not need Foundation, an internal set of all finite tuples, or Replacement. Its statements about intersections and unions are membership descriptions, not an invocation of separate set-existence axioms.

Replacing logical equality by incoming-profile equivalence is legitimate in the extensional setting. Existentially decoding one tuple code then gives an arbitrary finite-parameter matrix as a one-parameter matrix. Conversely, the fixed empty/nonempty branch relation produces Pairing from unrestricted EPSC, with the empty cases handled separately. This fallback is sound.

## 6. Equality-free repair: EPSC_1 + DP

The equality-free sentence DP asserts an exact union of two incoming-profile classes. The important new point is that all construction resources except this fixed sentence can be obtained with one ordinary parameter.

### Raw resources

An exact globally subset-bounded class is supplied by a constant EPSC matrix. The bound is a witness used to prove the premise; it is not a free matrix parameter unless it actually appears in that matrix.

Full incoming-and-outgoing profile equivalence `O` is a membership congruence in pure logic. Exact `O`-singletons are therefore available using one parameter. For the decoder `W`, if `x` is an `O`-singleton of `t`, every `y` decoded from it is `O`-equivalent to `t` and is subset-bounded by `t`; otherwise the subset branch is bounded by `x`.

The transitive-container matrix correctly gates its initial subset-of-`a` branch by emptiness and its decoder branch by nonemptiness. If a member `y` of a hull member `x` is not directly decoded, its exact `O`-singleton is a subset of `x`, is emitted first, and is nonempty, so the next enabled step emits `y`. This proves raw transitivity without combining two bounds in one matrix.

Raw Union uses only its argument `A`. Saturation under incoming-profile equivalence uses only `A` and is bounded by its raw union. Both are valid constant-class applications.

### H and the purity cut

Incoming-profile equivalence preserves `H` in pure logic. The defining transitive witness proves heredity: every raw member of an `H`-object is again in `H`. Every empty object is in `H`.

If an object `A` is saturated and all its members lie in `H`, take a raw transitive container `V` containing `A`. The exact cut

```
U = { u in V : H(u) }
```

uses only `V` as parameter, since `H` is a fixed formula. Heredity of `H` and transitivity of `V` make `U` transitive. It contains every member of `A`, and each member of `U` is saturated. Thus `U` witnesses `H(A)`. A further container bounds this cut as stated in the source; in fact transitivity of `V` already makes `V` itself a sufficient subset bound for its members.

This proof establishes purity of the saturation of any raw object whose members are all in `H`. It never needs a matrix containing both that raw object and a separately packed parameter tuple.

### Interpretation and direct closure transfer

On `H`, membership is congruent under incoming-profile equivalence: incoming equivalence handles the target, and saturation of that target handles its members. Heredity implies that interpreted emptiness and subset inclusion coincide with the raw predicates for `H`-objects. It also proves interpreted Extensionality.

DP applied to two `H`-objects has only `H`-members and is saturated, so the purity cut puts this exact pair in `H`. The quotient therefore has Pairing and Extensionality before tuple coding begins. Interpreted tuple coordinates are unique up to the interpreted equality, which is all the formula-invariance argument needs.

The guarded matrix `R(x,y;t)` includes `H(x)` and `H(y)` and has only the tuple code `t` free. Interpreted local bounds give raw local bounds because of subset absoluteness; non-`H` inputs have no outputs. Support of its raw hull `C0` makes every member of `C0` pure. Saturating `C0` requires only `C0` as parameter and produces a pure final hull `C`.

Initial closure transfers by emptiness absoluteness. For recurrent closure, any input in `C` has an incoming-equivalent copy in `C0`; congruence transfers the intended edge to that copy. For support, any output in `C` has a copy in `C0`, and raw support supplies a pure input whose edge transfers to the desired output. These are exactly the full interpreted EPSC clauses. No separate seed or support-filter parameter is introduced.

### Fixed exception and fusion

The fixed two-parameter matrix `Theta` is locally subset-bounded in logic by using its first parameter at empty inputs and its second otherwise. If the first parameter is nonempty, its hull must contain both profile classes. If only the second is nonempty, swap parameters. If both are empty, the classes coincide and the one-parameter exact singleton suffices. This proves DP.

Conversely, if the first parameter is nonempty, its DP pair is a `Theta` hull. If it is empty, use only its profile singleton: every active hull input is empty, so the second branch never becomes active. This case is necessary and is handled correctly.

The fused schema `LB_rho -> (DP and Hull_rho)` is deductively equivalent to `DP + EPSC_1`: project the EPSC conjunct; use the false matrix, whose premise is a logical theorem over a nonempty domain, to obtain DP; the reverse direction is propositional logic. Fresh renaming prevents accidental capture. The fusion does not establish a smaller compiled program.

## 7. Scope of the conclusion

The proof supports the finite-repair calibration at the ordinary mathematical level. It does not establish a new literal Turing-machine table, a lower compiled state count, or a proof-assistant-checked arithmetic equivalence for a particular machine. An eventual machine claim must still supply the complete implementation, blank initialization, fair proof-search theorem, and the formal internalization linking halting to the intended proof predicate.

## Addendum: a shorter fixed Binary Union clause

After the source snapshot above, the theory agent proposed replacing DP by the equality-free closed Binary Union sentence

```
BU := forall A B, exists C, forall y,
        (y in C <-> (y in A or y in B)).
```

This replacement was also independently audited and is sound. Over `EPSC_1`, exact incoming-profile singletons of `a` and `b` exist from the one-parameter constant matrices `Delta(y,a)` and `Delta(y,b)`, subset-bounded by `a` and `b` respectively. Applying BU to these two singletons gives DP.

Conversely, apply DP to `A,B` and then take the raw Union of the resulting object. Every member of the DP object is incoming-profile equivalent to `A` or `B`, so the Union has no members outside the union of their extensions. Both `A` and `B` themselves belong to the DP object by reflexivity of incoming-profile equivalence, so every desired member occurs. This proves BU. Raw Union was already obtained with a one-parameter matrix in the audited bootstrap.

Thus `EPSC_1 + BU`, `EPSC_1 + DP`, and the fused schema `LB_rho -> (BU and Hull_rho)` have the same deductive calibration. In the displayed syntax, BU has three membership-atom occurrences, while DP has five after expanding its two incoming-profile tests. BU also avoids the tests' extra nested quantifiers. These counts measure formula payload in this syntax, not generated-machine states; compilation can alter the comparison.
