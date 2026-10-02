# Removing the old-ground spanning hypothesis by parallel copies

Status: proposed ordinary corollary, awaiting independent pin. October 1, 2026. This simplification was independently proposed by the root reviewer. Earlier approved sources and delivered packages remain unchanged.

## Statement and polynomial convention

Let M be any finite matroid of rank q with two distinct distinguished elements A,B, and let E be the complement of those two elements. Define U0 to count the old q-subsets that are bases of M; it may be zero when r_M(E)<q. In that case U0 must not be interpreted as the lower-degree basis polynomial of M restricted to E. Define UA,UB,U,V by the same extension-to-a-full-M-basis conditions as in FULL_SELECTED_TAIL_THEOREM.md.

The Lorentzian conclusion for

  F_M=z²U0+z(aR0+bR1)U0+ab M2 U0
                    +z²(aUA+bUB)+abzW+abz²V

follows from the corresponding theorem with an old spanning ground set, without any further derivative or support argument. Thus the already approved representable theorem immediately extends to all representable M. Once ALL_MATROIDS_EXTENSION.md is independently approved, the same argument gives the theorem for all finite matroids M.

## Parallel-extension reduction

For each distinguished element which is a nonloop, add one new old parallel copy: A' parallel to A and B' parallel to B. If a distinguished element is a loop, no copy is needed. Call the extended matroid Mtilde, and put all added copies into the new old set Etilde. Its distinguished elements are still the original A,B.

Parallel copies do not change rank. Every distinguished nonloop lies in the closure of its added old copy, and every loop lies in the closure of the empty set. Therefore Etilde spans Mtilde, and r(Mtilde)=r(M)=q. Parallel extension also preserves representability whenever the starting matroid is representable, by repeating the corresponding nonzero column. For arbitrary matroids it is the rank-one instance of a free-on-flat principal extension, covered by Bonin–Kung, Lemma 3.1, https://arxiv.org/pdf/1210.0626.

Apply the established spanning-old-ground theorem to Mtilde, with exactly the original population parameters. Then specialize every added old-copy variable to zero. The restriction of Mtilde to the original ground set is M. Hence the surviving monomials of each of the five old-set polynomials are exactly the original U0,UA,UB,U,V. This is true for the Boolean union U as well: for every surviving old subset, extension feasibility by A or B is unchanged by restriction.

Thus the specialized polynomial is precisely F_M. Nonnegative linear specialization preserves Lorentzianity or gives zero. The result is not zero, since its no-Y term contains

  z²[U0+aUA+bUB+abV]=z² B_M(w_E,a,b),

and every finite matroid has a basis. This completes the reduction.

## Scope

The final abstract statement has no representability or old-spanning assumption once the preceding all-matroid extension is approved. The graph corollary is unchanged: it retains selected-tail variables individually for physically disjoint bipartite shores. Y activity parameters remain constants, and no physical-role collision or general balanced rank-six theorem is inferred.
