# Signed round-20 intake review

Scope: the three explicitly supplied Library packages and the later
Shared Factorial Error package, all materialized/extracted without modifying
frozen round19. Library helpers were fetched from the current skill source;
all returned identity attributes were applied. No repository changes occurred.

All four complete supplied root verifiers passed in ordinary and optimized
Python. Exact run records are `intake/VERIFICATION_RUNS.json` with named logs.
Those root passes authenticate finite data and their component checks; they
are not an unbounded number-theoretic proof or a new formal-kernel build.

## Nearest Factorial

Read the entire `direct/proofs/NEAREST_FACTORIAL_PROOF.md` and the literal
source/replay structure. Its acyclic order is adequate: odd square q, exclusion
of q=1 by normalized error, divisibility x>=t+1, representative signs, the
separate F=0 coefficient estimate, signed B/F recovery, nearest factorial,
then remaining range tails. The F=0 exception is explicitly treated rather
than incorrectly applying the m>=1 coefficient lemma. Radius1/2 fixed point
and completeness margin1/32 are proved by finite rational inequalities.
The final242/243 endpoints have only four/three affine deletions; they were
not the latest available signed baseline after the newer Git intake.

## Digit Recovery

Read the entire `proofs/NEW_ARGUMENT.md`. The (6z+3)^2 restriction gives q>=9
before any ceiling signs. The ratio forces x>=t+1; B*mu=F²+C0+1 excludesB=0;
self-radix then gives q>=2^x and |B|<q/2. The endpoint bounds F²+t<=x−1,
so every binomial digit and its canonical low tail is <half the relevant
modulus. This establishes B=binom(F²+t,t)>0 before the rs>=0 guard is used.
Only then do r+s=B−1 and rs>=0 imply both signs. The completeness mod6
representative adjustments preserve the odd N² CRT classes; the larger
explicit dominant representative remains dominant when the frame is chosen
from the actual values. No critical arithmetic issue found in the supplied
new proof. This is a valid alternative, not the selected smallest branch.

## Joint Norm

Read the entire `direct/proofs/BOOTSTRAP_PROOF.md`, including its t>=4
rounding appendix. The changed H=1+2sum(a_i) is nonzero before signs;
the retained constant1 in the norm establishes M!=0. Thus b>=2 and|F|<b
are available before the signed B/BH power requests. The existing ratio
forces x>=t+1, after which |q+1|>=2 recovers all representatives. Signed
short tails, with a separate F=0 case, give B=C>0 by |B−C|<|q|. The nearest
factorial lemma and its strict1/32 canonical margin restore all deleted
signs. Completeness recomputes the actual radix and frame; it does not falsely
claim coordinatewise equality to the old H construction. No critical issue
found in the new ordinary arithmetic proof. Its full finite root checks pass.

## Selected Shared Factorial Error composition

The latest source uses deterministic comparison center plus affine odd radix,
with core244. Its complete source proof is in its report, not the historical
equations/PROOF.md. Independent reviewer acceptance and the complete new
sphere2 ordinary proof are recorded in `PROOF_SPHERE_SIGNED_FACTORIAL.md`.
Removing the norm's constant requires a changed proof order: M!=0 comes from
odd q and signed/unit power recovery, not from the new norm. The F=0 case
initially yields b>=2, not3; odd q and the recovered power identity then force
b odd and b>=3. These corrections are retained in the delivered proof.
The coefficient2 sphere and transported exact round19 operations produce
238/175/5236/H3968 and237/174/18569/H7680, with all literal data independently
checked normally and under genuine propagated optimized Python.

All judgments above are scoped ordinary mathematical/internal reviews, not
outside peer review or machine-checked unbounded theorem claims. The source
calibration remains the named retained C222/ZF/ZFC finite-refutation interfaces.
