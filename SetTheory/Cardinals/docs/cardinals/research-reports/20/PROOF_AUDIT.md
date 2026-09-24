# Mathematical proof audit

## Scope

The new main theorem is Theorem 1.1. The local combinatorial theorem is 4.1,
the forcing-size step is Proposition 5.3, and the singular chain-condition
endpoint is completed after Lemma 5.4. No Lean verification is claimed.

The new conditional incompatibilities are stated explicitly in Corollaries
4.3, 6.2, and 7.4. The canonical-ground applications are Theorem 7.3 and
Corollary 7.6. Corollary 6.3 treats the additional cardinal-preservation case.

## Dependency route for the general theorem

1. Cofinality transport: cf^V(alpha) = cf^V(cf^W(alpha)).
   Proof uses a ground increasing cofinal map and pullback of an ambient
   cofinal set. No closure of W under ambient sequences is assumed.

2. Ground clubs remain clubs. Stationarity passes downwards, not generally
   upwards. Upwards preservation later comes from a chain condition.

3. A stationary subset of E_eta cannot reflect at an ordinal of uncountable
   cofinality <= eta. Applied once in W and once in V, this supplies both
   strict inequalities needed at each recursive stage.

4. Strong compactness supplies simultaneous reflection for fewer than delta
   stationary subsets of E^theta_{<delta}. The fine-ultrafilter proof uses
   a seed covering j``theta. It does NOT assume that j``theta is an element
   of M or that M is closed under theta-sequences.

5. At stage i < delta, reflect S_lambda together with every earlier S_mu_j.
   The family has size < delta, including at limit stages. Define
   mu_i = cf^W(alpha_i) and tau_i = cf^V(alpha_i). Their strict growth
   follows from step 3. The recursion is in V, not in W.

6. There are delta distinct new cofinalities below delta, hence they are
   unbounded in delta. A ground successor-cardinal induction gives
   mu_i >= (lambda^(+(i+1)))^W. Its limit stages use the ground singularity
   of (lambda^(+i))^W for nonzero limit i < delta.

7. If nu bounds the ground size of a dense presentation, choose
   theta = (nu^+)^W. Chain-condition preservation gives a common regular
   height at which every ground stationary stratum survives. All mu_i
   are ground cardinals below theta and therefore <= nu.

8. Every ground regular chi with lambda < chi < Theta fails the chain
   condition: some mu_i >= chi is regular in W but has small ambient
   cofinality. A chi-cc forcing would preserve its regularity.

9. Theta is singular in W, with cf^W(Theta) = delta. Erdős–Tarski's theorem,
   applied inside W, promotes the failure of cofinally many regular chain
   conditions to failure of the Theta chain condition. This is the actual
   antichain argument, not an inference from density alone.

## Imported information for applications only

Input A: exacting lambda has ambient cofinality omega and is regular in
HOD_{V_lambda}; Aguilera–Bagaria–Lücke, arXiv:2411.11568v4, Theorem 2.10
for the regularity assertion.

Input B: gamma-cover exactingness gives regularity in HCD(eta) for
eta >= gamma^+; the supplied Large_Cardinals_Synthesis.tex, Section 5.
This is an explicit archive dependency. No new strengthening of that
completeness barrier is assumed.

Input C: if kappa is strongly compact, HCD(kappa) is a ZFC ground with
kappa-cover; Goldberg, arXiv:2103.13961v2, Theorems 4.9 and 4.13.

The main theorem does not depend on Inputs A–C. Only Section 7 does.
The iteration and equiconsistency assertions and Lean admissions in the
input archive are not used in the new general proof.

## Boundary checks

- Strong compactness is assumed in V. It is not silently transferred to W
  or to the intermediate canonical ground HCD(delta).
- The main bound concerns W-antichains and W-densities. Theta may be
  collapsed in V, and the mu_i need not be V-cardinals.
- The initial lambda is explicitly required to be a V-cardinal.
- The iteration has length delta but each reflection request has size
  strictly below delta. No reflection of a delta-sized family is used.
- At the endpoint Theta, the proof uses Erdős–Tarski inside W, not
  stationary-set preservation at a singular cardinal.
- Under kappa-cover, a W-regular mu >= kappa cannot have ambient cofinality
  < kappa. This confines the canonical cascade below kappa.
- Under delta-cover for U, each new cofinality < delta lifts to a U-cofinality
  < delta. The lifted cofinalities are unbounded; their first enumeration
  is not asserted to be increasing or to belong to U.
- HOD being a ground is an explicit extra assumption in the ordinary
  exacting application. The canonical HCD(kappa) ground requires an
  upper strongly compact kappa > gamma, not just kappa > lambda.
- Cardinal preservation is an additional assumption in Corollary 6.3.
  Without it, the conclusion that the mu_i are weakly inaccessible in W
  is not asserted.
- No optimality or matching consistency upper bound is established for
  the new forcing-size threshold. The unqualified large-cardinal
  configuration is not refuted by this report.

## Verification level

The listed steps were checked by direct mathematical reasoning and all are
proved in English in the PDF. References to classical inputs were checked
against primary sources. No proof assistant, theorem prover, or external
referee has verified the complete argument. The comparison is with the
specific uploaded archive; a global claim of novelty or priority is not made.
