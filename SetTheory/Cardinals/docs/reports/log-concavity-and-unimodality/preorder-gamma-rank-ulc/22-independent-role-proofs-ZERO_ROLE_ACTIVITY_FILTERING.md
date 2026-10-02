# Zero role activities can be removed within preorders

Let R be a preorder with nonnegative tail/head activities u_i,v_i. Set U={i:u_i>0} and V={j:v_j>0}. Form R' by retaining an off-diagonal arc i->j exactly when it belongs to R and i belongs to U and j belongs to V; then include every reflexive loop.

R' is a preorder. For a nontrivial surviving path i->j->k with i!=k, transitivity in R gives i->k, while survival of the first and second arcs gives i in U and k in V. Hence i->k survives. Cases involving reflexive loops are immediate, and a path returning to its start is covered by the added reflexive loop.

Now replace every zero activity by 1, keeping the other activities unchanged. The formerly zero tail roles have no outgoing off-diagonal arcs in R', and formerly zero head roles have no incoming off-diagonal arcs. Thus their new positive values are unused. A positive-weight support of R has all its tails in U and heads in V, so all arcs of any matching witness survive in R'. Conversely every feasible support in R' uses only originally positive roles. Therefore the support polynomial is exactly unchanged.

All modified activities are positive, so the matching number of the undirected comparability graph of R' equals the actual surviving degree of the original weighted polynomial. Consequently, the now-proved general role-weighted theorem for preorders of underlying physical matching rank at most three automatically extends to every nonnegative activity assignment whose surviving degree is at most three, even when the original unfiltered preorder has larger matching rank.

This is a scope-reduction lemma. The role-weighted seven-vertex cases are now complete, as recorded in the final article and complete role ledger. For single vertex activities u_i=v_i=x_i, deleting zero-activity vertices is simpler and already supplies the corresponding extension of the vertex-weighted theorem.
