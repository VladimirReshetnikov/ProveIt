# Proof audit

## Scope and foundations

- Basic setting: transitive same-ordinal inner models M subset N of ZFC, with M
  available as a definable or suitably amenable class predicate.
- Forcing is set forcing in the indicated ground; all products and coordinate
  subproducts in the main construction are originally formed in M.
- Sizes, types, gap characters, and isomorphisms are interpreted in N.
- GBC with Global Choice is used only for the global, uniform class-isomorphism
  and involution construction. Stages of the back-and-forth are sets.
- No set of all surreals, no set containing proper-class maps as elements, and
  no unrestricted class-choice or class-truth principle is assumed.

## Main dependency chain

1. Classical sign order and the simplest-separator theorem imply the fresh-sign
   correspondence (reproved in Section 3).
2. Ordinal block coding and bounded ground coding of cofinal prefixes imply the
   cofinality-compression theorem (Section 4).
3. The forcing truth lemma and a cofinal pigeonhole argument imply the external
   density bound (Section 5).
4. Closure and substring enumeration imply the no-GCH Cohen and collapse
   singleton spectra (Section 5).
5. A proved small-head/closed-tail localization lemma and a proved mutual-generic
   intersection lemma handle relative coordinate grounds (Section 6).
6. The published product-preservation and successor-of-singular fresh-function
   input is isolated as Proposition 6.5. It is not reproved.
7. Density ceilings, localization, and fresh witnesses from independent
   subproducts imply the exact spectrum for every omitted F (Section 7).
8. The coordinate cardinals in the spectrum recover F; positivity by squares
   makes this an abstract field invariant (Section 7).
9. Short-code preservation and RCF quantifier elimination give the exact
   saturation threshold. Set-stage class back-and-forth gives all the
   involutions uniformly (Section 8).

## Critical checks

**Ground versus outer cofinality.** Fresh functions are indexed by ground
regulars, whereas gap characters are outer regulars. The transfer takes an
image under outer cofinality; it is not an intersection of two cardinal lists.

**Pointed versus possible-generics spectra.** The article works with the actual
pair M,N. It does not collect characters from different lottery-sum branches
and attribute all of them to one generic extension.

**Binary coding.** A fresh ordinal-valued function is encoded by a sign that
can be much longer. The proof never assumes a fresh subset of the same domain.

**External density.** The dense set is old, but its cardinality is computed
in the extension. The generic substring argument is what gives the sharp
Cohen bound even when the ground tree has large size.

**Intermediate closure.** Old Cohen posets are not assumed to remain closed
in M_F. Closure is used in M for a head-tail localization, followed by an
intersection argument over the common coordinate base.

**Infinite omitted sets.** The lambda^+ lower witness comes from the published
singular-product result in the independent F subextension, then stays fresh
over the complementary ground. It is not inferred merely from the existence
of the individual coordinate generics.

**Uniform class choices.** One fixed global well-order specifies every
one-element extension and all back-and-forth recursions. The family is one
class relation with a set-valued parameter, not a set of proper-class maps.

**Intersection scope.** Binary coordinate-field intersections are calculated.
No arbitrary-intersection or field-compositum assertion is smuggled in.

## Imported background

- Gonshor: sign representation, simplest separators, real closedness, and the
  usual surreal arithmetic framework.
- Standard forcing theorem, closure, and product factorization; elementary
  instances used for the main relative proof are supplied explicitly.
- RCF quantifier elimination and basic algebraic closure facts, as in Marker.
- Fischer--Koelbing--Wohofsky (2023), Proposition 4.10 and Corollary 4.21: the
  advanced product facts. Their Proposition 6.1 and Theorems 7.21 and 7.23 are
  used only in the comparative example table.

## What has actually been verified

- The manuscript's arguments were internally reviewed for the failure modes
  above, and all formal assumptions have been made visible.
- The LaTeX was compiled and cross-references stabilized.
- PDF page images were inspected for layout and clipping.
- The finite Python tests were run; exact results are in the JSON file.

No independent referee review, Lean check, theorem-prover certification, or
computer verification of any infinitary forcing theorem was performed.

## Priority and unresolved scope

The proposed contributions are the transfer/relative-field synthesis and the
explicit new consequences for the repository questions, not the published
forcing inputs. Literature priority is not certified. The result classifies the
displayed coordinate family, not all old surreal fields with equal spectra.
The eight research questions in Section 10 include countable intersections,
composita, longer products, weaker cardinal arithmetic, equal spectra outside
this family, birthday recovery, expansions, and foundations/formalization.
