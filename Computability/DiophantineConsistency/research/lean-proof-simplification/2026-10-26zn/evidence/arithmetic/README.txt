ONE COMMON MODULUS FOR THE LITERAL KERNEL CERTIFICATE
Reviewed revision: e1c8914bc7064d9a8e7c06171a18069a949badd0

Proposal
--------
CurrentKernelResidues2011.lean repeats 59 literal Horner block checks separately
modulo 47, 2011, and 120199. Replace them with 59 checks modulo their common
multiple M = 47 * 2011 * 120199 = 11360848883, then project the result. This is
not a CRT reconstruction: only each p | M is needed for projection. Pairwise
coprimality is irrelevant to the proof of soundness of the replacement.

The exact certificate is:
  2^47 mod M                 = 10653241607
  doubled selector rows mod M = 10463387658
  34 control terms mod M     = 4297442889
  original reflected K mod M = 1491904576
The final residue reduces to 26 modulo 47, 1995 modulo 2011, and 114787 modulo
120199, precisely the original three public results.

Why this is an additional idea
------------------------------
Earlier proposals already include deriving weaker divisibility from stronger
moduli, arithmetic reflection, shared chunk assembly, and interpretation through
ring homomorphisms. Those are assumed available. The additional decision here
is to compute a new single common certificate for three formerly independent
literal residue tables. The existing generic mechanisms then project it. The
new value and all 59 coefficient-block residues have been checked against the
actual 941 literal rows, not an unrelated toy polynomial.

Deliverables and validation scope
--------------------------------
common-modulus.patch proposes a production replacement and preserves the entire
initial physical-order/selector/rawWord_cast bridge verbatim, along with the
existing final natural-residue and Hs wrappers. All three original public K_cast
results retain their statements. CurrentKernelResidues2011.common.lean is the
complete proposed replacement for convenience.

CommonModulusCertificate.lean is a standalone kernel-checked fixture. It copies
only the 59 literal chunk definitions and rows concatenation from the reviewed
source; its arithmetic is the proposed common certificate. The exact copying is
verified by audit_common_modulus.py. This fixture does not reprove the table's
physical-order/permutation connection to the actual kernel. The production
patch retains that connection, but the full production import closure and
clients were not rebuilt in this session. This difference is material and must
remain visible in any integration report.

The candidate source has 426 lines versus 843 before, removing 417 physical
lines inclusive of the new common theorem and generic projection helper. The
941-row fixture is validation data, not additional production helper overhead.
No speedup is claimed. Larger-modulus reductions may cost more, even though
there are fewer separately maintained certificates.

Reproduction
------------
1. Use ProveIt at the pinned revision with its Lean 4.32.0/mathlib dependencies.
2. Run:
   python3 audit_common_modulus.py --repository /absolute/path/to/ProveIt
3. In that project's environment, run:
   lake env lean /absolute/path/to/packet/CommonModulusCertificate.lean
4. Review and apply common-modulus.patch, then build
   DiophantineConsistency.CurrentKernelResidues2011 and its current checks and
   controller consumers. The patch does not alter source coefficients, q, A,
   Gamma, dimension exponents, the literal K, or their semantic assumptions.

Joint follow-up, not a separately measured improvement
-----------------------------------------------------
With the independently proposed power fixed-point lemma x^a=x => x^(a^n)=x,
B has common residue 10287028452 and B^120199 has the same residue modulo M.
Gamma rw n would then have common residue 706142772, coprime to M. This suggests
one uniform Gamma unit certificate followed by projection and prime-power
lifting. GammaCommon.lean now kernel-checks this synthesis, including the ordinary gcd
certificate and unit conclusion modulo (47*2011)*120199^n for every n, with rw
independent of n. The large constants remain symbolic with their exact residue
premises explicit; the natural subtraction is justified from 1 <= B. The proof
imports the separately checked PowerFixedPoint helper. This synthesis is not a
second production patch or a separately measured line saving, and it does not
rebuild the production connection of the symbolic K parameter to the physical
kernel. The radix and B residues and the common fixed-power seed are checked
inside GammaCommon.lean.

Synthesis replay requires compiling the supplied syntax/PowerFixedPoint.lean
with package root set to that file's directory, then adding that directory to
LEAN_PATH for GammaCommon.lean. In a checkout with Lake configured, the parent
packet's replay script performs these steps. Both gammaExpression_residue and
gammaExpression_unit use only the usual axioms propext, Classical.choice, and
Quot.sound. See gamma-validation.json and gamma-common.log.
