# Proof audit

This is an internal mathematical audit, not independent peer review or a
formal proof certificate. The theorem numbers refer to the delivered PDF.

## Main theorem (1.1) and obstruction (Section 3)

**Base category:** all proper filters on ω containing the cofinite filter.
A unique arrow G → F exists exactly when G contains F. The category is a set,
not a proper class.

**Topology:** a sieve D at F is extension-closed and dense among all proper
extensions of F. The full sieve in the proof is the union of all extensions
of each displayed generator. Merely listing the generators would not satisfy
the source's definition of a cover.

**Rows:** B_n = {2^n(2k+1)−1 : k ∈ ω} are disjoint, infinite, and partition ω.
**Tails:** T_m = ⋃_{n≥m} B_n.

**Filters:** F_n consists of sets containing almost all of B_n. F_infinity
consists of sets containing almost all of some T_m. Their membership tests
were derived directly from their bases; the tail test has an existential
index m, not a universal index and not an infinite-intersection requirement.
Each filter is proper and has an explicit countable base.

**Incompatibility:** B_n and B_k are disjoint for n ≠ k; B_n is disjoint from
T_{n+1}. A proper filter cannot contain either displayed disjoint pair.
The tail filter contains every tail, not just one selected tail.

**Density:** for one arbitrary G, either some B_n is G-positive, in which
case adjoining it is proper, or all complements of B_n belong to G. In the
second case each T_m is a finite intersection of these complements, so
F_infinity ⊆ G. No countable intersection and no simultaneous selection
for all G are used.

**Matching:** on all extensions of F_n use the class of constant a0; on all
extensions of F_infinity use the class of constant a1. The components are
pairwise incompatible and hence disjoint. Extension cannot switch a
component, so the assignment is well-defined and persistent.

**Contradiction:** a hypothetical sequence f equals a1 except for finitely
many points in some T_m. The condition at F_m says that f equals a0 except
for finitely many points in B_m. Since B_m is infinite and contained in T_m,
the two equality sets meet. Distinct a0 and a1 make this impossible.
No uniform error bound over every row is assumed. Values of f outside
{a0,a1} are allowed and do not affect the contradiction.

**Boundary cases:** for |A|=1, every value is a singleton. For A empty, every
value is empty, and every covering sieve is nonempty, so no matching family
exists. Classical ZF proves the required dichotomy.

**Foundations:** all steps above use ZF only. There is no ultrafilter,
almost-disjoint-family selection, dependent choice, or cardinal comparison
with the continuum in the main construction.

## Separatedness and finite pasting (5.1–5.3)

If an equality set E is not in F, adjoining its complement is proper. A
dense sieve then detects failure of equality. Thus only existence of gluing
fails, not uniqueness.

For finitely many filters, agreement at their generated common filter gives
large sets whose pairwise intersections lie in the corresponding equality
sets. For incompatible filters, empty intersections give the same property.
Intersect finitely many witnesses on each side and paste using the least
index. Every selection is finite. The theorem is stated for arbitrary proper
filters on an index set so that the finite tests are honest instances of the
pasting result (though not of the Fréchet site).

Sharpness concerns the number of sieve generators: no finite-generator
counterexample can exist, and one with a countable generator set does exist.

## Positive rows and countably generated bases (6.1, 7.1–7.2)

Above general F, define T_m as the complement of the first m rows, not as
the union of remaining rows: the rows need not exhaust ω. This distinction
is necessary for density.

T_m contains the F-positive set B_m, which guarantees properness of the tail
filter. Membership there means C∩T_m is contained in the desired set for
some C in F. Combining this with the row condition leaves a nonempty
intersection because B_m is F-positive.

For countably generated F, fix a decreasing base C_s. At stage s choose
s+1 new elements from C_s by the least-unused-integer rule. This is a uniquely
defined recursion in ZF. Each row eventually lies within each base member,
so every row is F-positive. The constructed filters remain countably
generated. The same density proof applies inside the smaller site of
countably generated proper free filters.

## Local Boolean classification (8.1–8.5)

I_F = {S : complement S belongs to F}. A set is F-positive exactly when its
class in P(ω)/I_F is nonzero. Every extension of F is saturated under
I_F-equivalence, giving the filter correspondence.

If the quotient is finite, the entire extension category is finite. Finite
pasting and separatedness give sheafness, with no choice principle.

If the quotient is infinite, DC constructs a disjoint sequence of nonzero
Boolean elements by repeatedly retaining an infinite interval in a Boolean
split. Countable choice, which follows from DC, selects representatives.
Finite disjointification preserves the Boolean classes. The positive-row
obstruction then applies. The paper does NOT claim that DC is necessary or
optimal for this implication.

Finite quotient filters are intersections of finitely many explicitly
constructed ultrafilters. This finite construction does not invoke a general
ultrafilter lemma. The finite-product reduced-power decomposition is proved
by finite pasting.

## Sheafification (9.1–9.3)

The entire section is explicitly in ZFC. The ultrafilter lemma ensures both
that ultrafilter extensions exist and that they form a dense sieve. Every
dense sieve contains every maximal filter above its base.

The product presheaf S_A(F) = ∏_{U ⊇ F} A^ω/U is shown to be a sheaf by
gluing coordinates. The universal map from R_A is injective because a
failed equality can be witnessed at an ultrafilter. The universal property
is proved by gluing the images in any target sheaf on the ultrafilter cover.
It does not assume the original presheaf was already a sheaf.

For A=2, old sections are Boolean classes / clopen subsets of the Stone
space; sheafification permits arbitrary subsets. The manuscript expressly
distinguishes this inclusion from an order-dense Boolean completion.

The tail set K is closed but not clopen. It is NOT asserted to have empty
interior: the explicit row selector gives a nonempty basic open subset.
In the real-valued case the new idempotent is a global product section, not
a nontrivial idempotent inside a single hyperreal field. Old reduced-power
rings already have many idempotents.

## Computation and validation limits

The scripts check exact arithmetic and finite pasting, not the infinite
proof. A finite index set has no proper filter containing all cofinite
subsets; the code and article explicitly acknowledge this.

The delivered test results were produced by executing the scripts, and
repeated with Python optimization enabled. No external network service,
CAS, or proof assistant is used in those checks.

The PDF was compiled without final-pass LaTeX warnings and all 20 pages were
rendered and visually reviewed in contact sheets. This checks layout, not
mathematical correctness.
