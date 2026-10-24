# Other leads and explicit obstacles

The direct-X carrier is the concrete new size tradeoff in this packet.
The following simpler-looking changes do not currently have correctness
proofs and are not endpoint claims.

* Replacing I=i*c^2 by I=i*c would reduce degree, but the retained rank
  lemma needs c^2|I to force c|m, not merely p|m for c=psi_A(p). The
  auxiliary-index congruence then gives R=+/-p+2m*phi modulo c; without
  c|m the small R,p bounds no longer force p=R. No replacement argument
  for this step has been found.
* Fixing i=1 is not a valid canonical restriction. Existing completeness
  chooses a much larger strong Pell index to get c^2 divisibility.
  The old construction does not provide I=c^2.
* Reusing i as the auxiliary T or final n also lacks a positive witness
  map. In the known construction auxiliary ordinates grow much faster
  than I, and n contains their positive excess. Renaming two coordinates
  does not identify their values. This is an obstacle to the existing
  maps, not a claim excluding every different encoding.
* Taking a degree1 Pell scale instead of mu=q^2+1 shrinks the first-index
  congruence modulus below the q^4 rank bound. Recovering the unique
  first index then becomes circular with the later exponent projection.
  No unbounded replacement index proof has been established.
* Replacing the product XY by a direct variable using a rational change
  requires clearing powers of X+1 in the complete polynomial. Basic
  degree bounds do not show an improvement, and no such packet is
  claimed here.

The accepted modulus-root separation already removes the old full-mu
lower-bound shift. These remaining obstacles concern the separate rank,
index and positive witness requirements; they cannot be repaired merely
by an additional finite test or a smaller evaluator count.
