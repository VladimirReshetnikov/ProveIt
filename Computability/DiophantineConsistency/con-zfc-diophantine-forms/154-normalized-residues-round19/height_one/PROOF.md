# Same-logical square polarization: complete reduction argument

Every coordinate below is an unrestricted integer. The five delivered polynomials have exact total degree 4, constant coefficient 1, and every nonzero collected coefficient in {−1,+1}. The coefficient files, not an unevaluated circuit, define these polynomials.

## 1. Sources and exact preliminary equivalence

`SOURCE_BINDINGS.json` binds three original quadratic systems to their surrounding ordinary consistency proofs. `sources/original247.json` is the new exposed signed source; the other two exact sources are the prior grouped and sparse spherical/odd-square systems. Their inherited theorem is, in ordinary ZFC, existence of an integer zero iff existence of a finite ZFC refutation. This package transfers that theorem; it neither proves consistency nor claims a new complete proof-assistant certificate.

Here is the full interface for the preliminary algebra. For a source row whose quadratic part is ηL(x)², η∈{−1,+1}, introduce a uniquely defined z=L(x)+k, replace the row by ηz²+R(x)−η(L(x)+k)², and retain the monic definition. Shared identical affine definitions are reused. Exact substitution verifies each source row; all new coordinates are uniquely determined. The selected rows and shifts are fixed finite certificate data, not parameters in the final equation. `check_factor.py` independently checks every coefficient and pivot.

Next define every needed positive integer constant by a triangular monic addition chain, and every selected scale coordinate by s=cx. Coefficient-factor vertex covers select which scales to introduce. Constants, scaled linear terms, and scaled quadratic factors turn each row into a sum of signed monomial occurrences, each coefficient ±1 and degree at most two. All original rows pull back identically, and all added definitions pull back to zero. The independent checker proves this directly, so neither heuristic optimality nor the normalization producer is trusted for equivalence. Multiply each row by its fixed certified sign σ_r. This preserves zeros.

## 2. Incidence energy, equality penalties, and exact lift

Assign a nonempty vertex block to each normalized row and one to a hub. Put a tree of independent integral flow variables inside each block. Each normalized monomial occurrence is either a singleton edge between its row and the hub, or is paired with an identical opposite-sign occurrence in a different row and represented by one direct edge between the two rows. The certificate binds every occurrence exactly once, with its exact signed row boundary. Each prescribed edge label is a degree-two monomial in aliases of its logical factors, using aliases of one to homogenize lower-degree terms.

Let d_v be outgoing minus incoming divergence, and set E=(1/2)Σ_v d_v². The prescribed boundary sum in row block r, after substituting logical values, equals T_r=σ_r S_r. The hub sum equals −Σ_r T_r. Internal tree flows cancel in each block sum. Thus no independence assumption about source rows is needed.

For k≥3 aliases of one logical value use C(a_1,...,a_k)=Σa_i²−Σa_i a_(i+1), cyclically. Its doubled value is Σ(a_i−a_(i+1))², so C≥0 with zero set exactly equality of all aliases. A singleton needs no penalty. An ordinary two-alias class is completed with a unique equality dummy d or uses

    Q(a,b)=a⁴+b⁴−a³b−ab³=(a−b)²(a²+ab+b²).

Here Q≥0 and Q=0 iff a=b; the second factor is positive unless both coordinates vanish. Equivalently 2Q=(a²−b²)²+(a²−ab)²+(ab−b²)². For unit aliases u_1,...,u_l, l≥2, use

    U=1+Σu_i²−u_1−u_l−Σ_(i<l)u_i u_(i+1).

Its doubled value is (u_1−1)²+Σ_(i<l)(u_i−u_(i+1))²+(u_l−1)². Hence U≥0 and vanishes exactly when every unit alias is one. The final polynomial is E+ΣC+ΣQ+U.

The source graph is simple, so the initial formal incidence expansion has unit diagonal and cross coefficients 0 or ±1. Identifying aliases can cause further collisions. Therefore every accepted identification and the final full collected polynomial are checked arithmetically; graph simplicity alone is not used as a final height proof.

Given ANY original source tuple x, evaluate all monic definitions, give every alias its logical value, and give equality dummies the common class value and units the value one. For each internal tree rooted at its first listed vertex, let b_v be prescribed divergence and let τ_v=±1 be the sign of the tree edge at child v. Assign that edge the integer polynomial

    w_v=−τ_v Σ_(t in subtree(v)) b_t.

Leaf elimination gives zero divergence at every nonroot, source residual T_r at row root r, and −ΣT_r at the hub root. Consequently the canonical lift L satisfies the UNIVERSAL identity

    P(L(x)) = (Σ_j R_j(x)² + (Σ_j δ_j R_j(x))²)/2,

where δ_j are the certified signs of rows descending from original residuals and constructor rows vanish identically. This is not in general the bare sum of source squares. The full row/source composition through affine refactorization preserves the identity.

Conversely, P=0 forces all its nonnegative summands zero. Therefore all aliases agree within logical classes, units are one, and every divergence is zero. Summing divergences over a row block gives T_r=0 and thus S_r=0. Monic definitions force exactly their intended values, so projection gives an original source zero. The constructors and alias values are unique, and tree leaf elimination uniquely determines every flow. Thus the canonical lift and coordinate projection are inverse bijections on integer zero sets.

## 3. New operation: polarize a square and delete its equality dummy

Suppose a logical class has two ordinary aliases a,b plus an equality dummy d, hence penalty C(a,b,d). A prescribed square a² (or b²) causes a positive a⁴ (respectively b⁴) in E, obstructing direct use of Q because coefficients would collide.

Replace the selected square edge labels by ab, without changing their incidence endpoints, sign, or occurrence ledger. Replace C(a,b,d) by Q(a,b), and delete d. The delivered algorithm tries all square-edge labels in such a class together, and ACCEPTS the change only if the ENTIRE resulting energy, including every other equality and unit penalty, collects to coefficient height at most one. It finally checks exact degree four, height one, constant one, and participation of every claimed variable. Successful steps are fixed in the certificate.

This transformation always preserves the logical proof, irrespective of whether its height test passes. The new E remains exactly a half-sum of divergence squares. The new Q is nonnegative and forces a=b. At logical equality, ab has the same value as the old square. Therefore the source-row boundary sums and every prescribed divergence under the canonical lift are unchanged. The same tree flows provide the forward lift and the same row-block argument provides the inverse. The old dummy has its uniquely forced value d=a=b, so deleting and restoring it are inverse operations on zero sets. The universal off-zero lift identity of Section 2 is unchanged as well.

Full coefficient collection is essential: replacing a² by ab can introduce other collisions. We make no claim that arbitrary polarizations preserve height one. The exact full checks establish this finite property for the five literal polynomials supplied here, independently of the unbounded zero-set proof.

## 4. Consistency equivalence and evidence boundary

Combining Sections 1–3 with each pinned source theorem, ordinary ZFC proves

    (∃ integer tuple z, P(z)=0) ↔ (there is a finite ZFC refutation).

Negating both sides yields

    (∀ integer tuple z, P(z)≠0) ↔ Con(ZFC).

No consistency assumption is used to prove these equivalences. They do not themselves establish either unsolvability or Con(ZFC).

The independent audit imports no polynomial producer. It reconstructs every coefficient from the literal divergence squares and equality/unit square identities; checks all source pullbacks, occurrence boundaries, graph trees, alias bindings and coverage; and verifies the universal canonical lift at every vertex. A separate parser checks the literal polynomial text. Tests remain active under Python -O. Four deliberately malformed polarization records and thirteen other mutation classes are rejected per endpoint; finite mutation controls supplement, not replace, the proof above. Deterministic regeneration reproduces every selected source, certificate and polynomial byte for byte. Four matched-source comparisons regenerate the exact round18 baseline polynomial/certificate hashes before applying the new operation.

`INHERITED_NETWORK_PROOF.tex` retains the complete previous normalization, incidence, contraction and tree-lift proof. No global minimum, exhaustive Pareto frontier, or literature-priority claim is made.
