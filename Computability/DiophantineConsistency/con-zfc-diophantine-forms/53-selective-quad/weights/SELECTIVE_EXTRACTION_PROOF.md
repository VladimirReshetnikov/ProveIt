# Selective isolation and sparse target padding

The complete current proof is `section.tex`, with a standalone five-page
rendering in `report.pdf`. The following is a concise guide to its obligations.

1. A monomial of degree at most two is represented by an unordered pair from
   the 31 source coordinates and one padding coordinate of weight zero.
   Only source-supported pairs must be distinguishable from every possible
   input-square pair. Absent pairs may collide.
2. The frozen row targets satisfy q_k - e(alpha) >= 0 and
   q_k - e(alpha) + e(gamma) = q_j only for k = j and alpha = gamma.
   Weighting the residual coefficient by (2-|alpha|)! times the product of
   alpha_i! makes the marked coefficient exactly 2 r_j(x).
3. The same isolation condition forces all reversed exponents in D to be
   distinct. Its coefficient bound A is therefore a maximum, not a sum over
   22 residuals. Product coefficients have magnitude at most
   A * (1 + sum x_i)^2.
4. Original source row 5, placed at the largest target, has shifted constant
   coefficient 1. Thus D has degree 5190 and leading coefficient 2, and
   D(B) > 0 for B > A + 1. The zero vector is not a common source zero.
5. For product coefficients a_s with |a_s| < B/4, put
   J = 2 sum a_s B^s + sum_target B^q. Incoming signed carries lie in {-1, 0}.
   At a target, the output digit is 0 or 1 exactly when a_q = 0, regardless
   of the incoming carry. The outgoing carry is then zero. Hence the binary
   mask (B-2) sum_target B^q tests each residual separately, without dense
   centering and without assuming away incoming borrows.
6. For B > 4096 A b^2 and 0 <= g < 2 b B^183, the source words satisfy
   0 <= S, T and S + T < B^5741 before b is known to be a power of two.
   Once b and B are powers of two, the low mask decodes g into distinct
   source digits 0 <= x_i < b, and the high mask tests all residuals.
   The final sparse wrapper has N_src = B^5741, not the old dense-wrapper
   value 4 B^5741.

The finite certificate has 71 marked pairs, 136 source terms, and 71,808
interactions. Exactly 136 interactions reach marked targets, all intended.
Among the 528 possible pairs only 267 sums are distinct, so this construction
is genuinely weaker than a full B2 construction. The check is a complete
finite verification of the isolation premise, not empirical sampling.

Selected coefficients come from original package31 with every positive source
variable replaced by x_i + 1. Package45 is independently cross-checked, with
its exact row-15 transport difference of -beta*(x_J+1). These two source
versions must not be silently exchanged in a finalizer proof. The code works
for both supports, but this release selects the original source throughout.

The four compiler ports must be replaced by the finalizer's specified fixed
tuple; they are not free variables of the final equation. The source compiler
and arithmetic finalizer theorems are inherited dependencies, not purported
consequences of the finite checker. No proof of ZFC consistency or globally
minimal equation is claimed.
