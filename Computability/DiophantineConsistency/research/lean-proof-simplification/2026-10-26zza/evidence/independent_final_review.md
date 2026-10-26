# Independent final review: closing correction

**The current recommendation count is three.** The original four-direction review below was made at `96520cd1a5179f470b4da127bd47bc26a8d808ff`. The closing audit at `3b51c69d42ff99bc420698532af3fe1d1f9bd356` discovered six newly submitted incoming ZIPs. The exact boundary-conservation proposal in `ProveIt_Proof_Simplification_Review_2026-10-26.zip` supplies the same finite-support normalize-once payoff after its proposed raw-update/finite-sum interfaces are assumed applied. Accordingly the aggregate direction is **withdrawn from recommendations and saving totals**; it may be retained only as screened-out evidence. See `late-head-audit.md` and `late-head-audit.json` for the precise counterfactual implication, report/member references and verified hashes.

The two local Pell changes and canonical descending-product residue decoder survive the closing semantic screen. Their four original target files (including the withdrawn target) are byte-for-byte unchanged at the closing pin. Compiler-status statements below are historical observations; final candidate validation artifacts control any delivered validation claim.

## Original review at the first source pin

# Independent final review of the four retained directions

Reviewed against pin `96520cd1a5179f470b4da127bd47bc26a8d808ff`, late packets
za-zq, the incoming ZIP, and selected earlier exact source variants. This is
a novelty/logic review, not an additional compiler run.

## 1. ThirteenFreshSeed: prefer first for immediate adoption

The new replacements use `pell_eqz` and `dz_val` at the two exact norm facts in
`auxiliary_exists`. They preserve the natural parameter and the signed second
coordinate, with hA/hS already present. The first replacement normalizes only
the existing f, delta, xz, yz, az definitions; the second retains the same hx
and negative-y substitution. There is no new positivity or sign assumption.
Do not remove hAA globally: it is still used at the subsequent cast of S.

Nearest prior: ze's carrier/affine cleanup (and zk's reflected-affine version).
Decisive evidence is the exact prior file
`2026-10-26ze/replacements/Computability/DiophantineConsistency/Lean/DiophantineConsistency/ThirteenFreshSeed.lean`:
it retains both old `χ_sq` / `congrArg` / `push_cast` norm proofs. Therefore the
new norm-proof edits remain after that prior proposal is assumed applied.
No za-zq/incoming proposal describes replacing these two blocks with pell_eqz.
This is a narrow maintenance delta, not new Pell mathematics.

## 2. SignedPellResidue: immediate local edit after a successful final check

`hn` already says x²=D*y²+1 in naturals. `Nat.sub_eq_of_eq_add' hn` supplies
x²-D*y²=1 directly; pow_two/mul_assoc only align Pell.eq_pell's interface.
The edit does not change the natural truncation domain, signed-residue
classification, parity argument, or witness choice. No extra inequality is
needed because the additive equality already implies the subtraction bound.

Nearest prior: k/m SignedPellResidue changes for parity and signed-congruence
transport. Both exact prior candidates retain the hp/nlinarith/omega block
being removed: `2026-10-26k/native-proofs/modified/SignedPellResidue.lean` and
`2026-10-26m/proposed/Computability/DiophantineConsistency/Lean/DiophantineConsistency/SignedPellResidue.lean`.
No late packet subsumes this precise deletion. Treat it as a small local
simplification. At review time its validation JSON still reported exit1;
use only the eventual final successful receipt for any checked claim.

## 3. Canonical residue criterion: strongest further reusable statement

The exact theorem

    p divides product(t=0..u) (a-t) iff a % p <= u

is correct for every natural a,u with p prime. No u<p or a>=u assumption is
necessary: the forward proof uses min(a,t) to respect truncated subtraction;
the backward proof picks the actual factor t=a%p, and p divides a-a%p.
When a<=u, the product contains the zero factor a-a and the residue criterion
is automatically true. When u=0, this reduces to p|a iff a%p=0.

In BoundedForallCertificate this permits j(i)=a(i)%p, replacing the choose/min
factor-extraction block, while preserving j(i)<=u(i) and the needed congruence.
The prime p itself is still selected from the CRT modulus; do not claim that
the whole decoding construction has become choice-free. The same existential
certificate theorem is preserved, not the arbitrary old chosen witness data.

Nearest prior: n/supplemental/SUPPLEMENTAL_REVIEW.md targets the reverse
direction's `exact?`; j targets BoundedForallDepth arithmetic; old syntax
decoder-graph proposals concern different encodings. No za-zq/incoming
proposal supplies this arithmetic criterion. If used for integer rather than
natural subtraction, formulate and prove the appropriate variant separately.

## 4. Aggregate no-wrap: optional architectural trial

The new bound is sound under rho>=2, K<rho^2022, N>0, and the actual safe
position inequalities. It accepts the empty set and N=1 (where safety forces
the set empty), s=0, arbitrary large N and all safe cells; no cardinality
estimate or global modulus-size assumption is smuggled in. Its proof uses
injective exponent maps and the geometric bound, not card(S)*maximum(term),
which would be insufficient for unbounded N.

Nearest prior: zn's weighted point update, zb's geometric identity, the
incoming two-window capacity fact, zo's reset locality, and zq's broader subset
coverage are all baseline. None supplies the new whole-support ordinary bound
or removes the induction that constructs intermediate normalization witnesses.
This mechanism composes with zq because it handles arbitrary safe subsets.

Recommend only as an architectural option: complete target 181->156 lines,
but the supplied 122-line helper makes literal total source grow by97 lines.
Its generic kernel is compiled, actual-source adapter uncompiled. The useful
change is one final normalization and one endpoint transport in place of
an induction over existential carry witnesses. Do not label it immediate
source compression or faster compilation.

## Overall ranking

For integration: ThirteenFreshSeed, SignedPellResidue after final check,
canonical residue API with one actual client, then aggregate bound only if the
stronger contract is valuable. For mathematical/proof-architecture interest:
canonical residue criterion and aggregate safe-support estimate come first;
the two local Pell edits are modest but low-overhead concrete improvements.
