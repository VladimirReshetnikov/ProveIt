THE COMPLETE CRITICAL LAW FOR HIDDEN SYMPLECTIC FORMS
27 November 2026

Start with paper.pdf. All proofs and their hypotheses are in that 21-page
paper; paper.tex and sections/*.tex are its complete editable sources.

WHAT IS NEW

This research continues the finite-field spanning and symplectic strand of
VladimirReshetnikov/ProveIt/Analysis/GeneralizedRiemannHypothesis at commit
641cd6296144d7c29bcc6569655b473647428b1b.

Earlier reports already gave the sample threshold, critical nullity law,
dimension-only testing curve, and linear-recovery curve. This paper proves:

1. Total-variation universality of the entire candidate subspace for
   decomposable-bivector observation rows.
2. Joint asymptotic independence of the nonsingularity indicators of all
   distinct projective combinations of any fixed number of independent
   random alternating matrices.
3. The full critical law of the number of compatible nondegenerate forms,
   and therefore exact limiting optimal testing, Bayes recovery, and
   unique-nondegenerate-candidate recovery probabilities.
4. Strict loss from retaining candidate dimension alone at every fixed
   critical offset, a non-Poisson third-moment identity, and an exact
   optimal algorithm with polynomial expected cost in that window.

Every theorem is unconditional, includes characteristic two, and is proved
in ordinary mathematics. No new Lean formalization or upstream GRH rebuild
is claimed. The novelty comparison is scoped to the inspected repository
and the cited primary literature; worldwide priority is not established.

MAIN LAW

Fix q and integer a; let even n tend to infinity, and take
t = binom(n,2)-1+a observations. Let K be candidate-space dimension and Z
the number of nondegenerate projective candidates. Put

  g_j = product_{i=1}^j (1-q^(-i)),
  omega = product_{i>=1} (1-q^(-(2i-1))),
  pi_b(k) = g_infinity*q^(-k(k+b))/(g_k*g_(k+b)),
  m_k = (q^k-1)/(q-1), lambda = omega*q^(1-a)/(q-1).

Under the null: K has law pi_(a-1), and Z|K=k is Binomial(m_k,omega).
Under the plant: K=1+J with J having law pi_a, and
Z|K=k is 1+Binomial(m_k-1,omega).

Optimal testing TV is E|Z/lambda-1|/2 under the null limit. For a>=0 it
equals P(Z=0), because existence of a nondegenerate candidate is already
the exact finite-sample optimal test. Optimal form recovery tends to
P_null(Z>0)/lambda.

At q=2,a=0, full testing TV is 0.411496025791 rather than the
dimension-only 0.288788095087. Optimal recovery is 0.701564718009;
unique nondegenerate recovery is 0.488389858129; linear uniqueness is
0.288788095087. These are limiting quantities, not small-n guarantees.

FILES

  paper.pdf                  Complete compiled paper
  paper.tex                  LaTeX entry point
  sections/*.tex             Proofs and analysis
  references.tex             Primary and pinned repository references
  figures/critical_profiles.pdf, .png
                             Publication figure and raster preview
  code/critical_profiles.py  High-precision evaluations of proved laws
  code/exact_binary_experiment.py
                             Exact F_2^4 observation experiment
  code/pencil_checks.py      Exact finite pencils and labeled simulations
  data/*.json, *.csv         Reproducible numerical records
  provenance.json            Snapshot and verified source identities
  proof_status.txt           Proof/check distinction and review summary
  formalization_plan.txt     Dependency plan, explicitly not a Lean proof
  Makefile                   Build/reproduction commands
  requirements.txt           Python dependencies for optional recomputation
  SHA256SUMS                 Integrity manifest of all other package files

REBUILD

The PDF uses standard LaTeX packages and needs no bibliography executable:

  make paper

The checked figures are already included. To regenerate them and the
high-precision tables (mpmath and matplotlib required):

  python3 code/critical_profiles.py

To recompute the exact observation experiment (standard library only):

  python3 code/exact_binary_experiment.py

To rerun pencil enumeration and fixed-seed simulations (NumPy required):

  python3 code/pencil_checks.py

The last command takes approximately a minute on the preparation machine;
runtime depends on hardware. Simulation timestamps and runtimes naturally
vary; exact integer counts and fixed-seed sampled counts are reproducible
with the same NumPy random-generator implementation.

VERIFICATION

The exact observation computation checks all t=0,...,10 on F_2^4 by dynamic
programming, covering 35^10 = 2,758,547,353,515,625 sequences at t=10.
No sequence sampling is used in that computation. The pencil program has
four exact cases and seven explicitly labeled simulation cases. The
profile script checks 39 parameter pairs at two precision settings.

The mathematical proof establishes the infinite-family claims. Finite
enumeration, numerical evaluation, and simulations are separate checks;
none is presented as a replacement for the proof.
