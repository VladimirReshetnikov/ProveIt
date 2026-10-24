# Independent peer review: prime-three twelve-integer family

Reviewer: a separate OpenAI research agent, working on the positive-domain lane.
Review snapshot: the six literal JSON files hashed in REVIEW_FRONTIER_CHECKS.json.

## Scope and finding

I read the entire new PROOF.md and the inherited INTERPOLATION12.md, including
its generalized signed-kernel restoration and full-residue completeness lemma.
I independently checked the new bootstrap order, the fixed prime-three radical
separation argument, the pure19 intersective polynomial, the reduced carrier
scale, and the exact-degree arguments. I found no gap in those new steps.
This review retains the inherited unbounded native/compiler/refutation
calibration as a stated dependency. It is not a new Lean/Rocq certificate, an
encoded internal ZFC derivation, a historical-priority finding, or a proof of
global optimality.

## Points requiring care

1. **Zero scale before guards.** H is nonzero on every supplied integer tuple.
   If S=srH^5 is zero, then I=src^2 is zero and delta=-1, so every variant
   specializes to (A^2-B^2 Dm)^16. Dm is positive unconditionally, and the
   quintic has no root in a real quadratic field. This excludes S=0 without
   presuming any guard or Pell root is integral.

2. **The c=0 case.** S nonzero no longer immediately proves c nonzero. The
   proof handles that correctly: when c=0, I=0 and the auxiliary squared root
   is still positive (Da=1 or Cy/delta=1). Prime-three separation therefore
   recovers a rational guard root, gives P>0 and eta*zeta>0, and contradicts
   eta*zeta=-Y(Y+1)k^2<=0. Only after this step is Q>1 used.

3. **Square-class collisions.** The squared normalized terms have valuations
   -2v3(S),0,2,4,6+v3(Dg), with the zero guard omitted. These are all distinct.
   The first is negative because v3(S)>=5. In each nontrivial square class,
   a putative cancelling signed sum would have a unique least-valued
   rational coefficient, which is impossible. Character projections thus
   force all roots rational even if some radicands share a square class.
   Negative guard values do not evade the argument; their square class is
   included, and rationality of its root implies nonnegativity.

4. **The pure19 quintic.** The polynomial (x^2+3)(x^3-19) is not monotone.
   Monotonicity is unnecessary here: B=1 modulo3 proves B nonzero, and no
   Archimedean magnitude bound is used. For p=3 the substitution x=1+3u
   reduces the lifting problem to 3u^3+3u^2+u-2, whose derivative is1 modulo3.
   Other prime powers follow from the quadratic/cubic residue split and
   simple-root lifting. The cubic is Eisenstein at19, so the real quadratic
   zero-exclusion argument also holds.

5. **Reduced carrier scale.** Soundness needs H^5 divisibility only; S=srH^5
   supplies it. The monic leading term of the homogeneous quintic forces
   H|(u+d). Completeness chooses I|pi(T+gamma), which is stronger than the
   needed sr|pi(T+gamma), because I=src^2. Thus removing c^2 from S does not
   lose either direction or introduce a circular witness choice.

6. **Centered degree.** Pairing the auxiliary signs gives exactly
   delta[2SV(Wc-L)+(Wc-L)^2]+S^2(1-V^2). Its unique leading contribution is
   the guard part of -2delta SVL, of degree32+32+25+55=144; the square term
   has degree at most142. The16-factor product has degree2304 with leading
   form2^16 delta_top^16 S_top^16 V_top^16 A4_top^8. This is a universal
   upper-degree and nonzero-leading-form proof, not an inference from a
   finite test. The2848 and2336 variants have the stated unique dominant
   auxiliary radicand/numerator.

I also independently expanded all three claimed leading monomial coefficients
from S_top, Q_top, V_top, and Dg_top. The exponents2^2848 3^1760 beta^1408,
2^2400 3^1440 beta^1152, and2^2512 3^1592 beta^1248 are correct for their
respective displayed monomials.

## Reproducible finite evidence

The independent standard-library review_integer.py checks all six frozen DAGs
for topology, liveness, variable census, and their operation counts. It
re-authenticates all six coefficient payloads, proves the new quadratic-algebra
carrier identity by full exact sparse-polynomial expansion, checks finite
intersectivity for every modulus1 through512, and explicitly lifts the3-adic
cubic root through modulus3^22. Its receipt is REVIEW_FRONTIER_CHECKS.json.

I also ran the author's complete portable verify.py once, producing
PEER_REPLAY.json. It passed all six counts, literal rebuilds, identities,
actual-coefficient line degrees, predicted leading coefficients, and its
negative control. A replay is supplementary to the independent mathematical
review above; neither finite check proves the inherited unbounded calibration.
