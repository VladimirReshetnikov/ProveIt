# Status and scope

Date: 20 September 2026.

## Claimed result

A proposed computer-assisted proof of unique positive aperiodic
Rudin–Shapiro autocorrelation maximizers for all m>=3, and their exact
nearest-two-thirds locations for all m>=40, with sharp threshold 40.
The m=2 tie is an explicit small-index exception. Further claims are the
complete finite exception set, an eventual cubic peak recurrence, the
rational peak generating function, the exact asymptotic constant, and the
periodic-maximizer corollary.

## What was actually checked

The standard-library exact checker was executed successfully on the bundled
certificates. It validates all finite hull compressions through level 402,
strict maximizing-word uniqueness, all 26 parametric transitions, uniform
coordinate separation, entry into a rational rectangle and the six-step
trapping argument. Direct defining-sum comparisons through level 10 and six
additional test methods passed. The PDF was compiled and visually inspected.

## What has not been established by external validation

The proof has not been independently refereed, formally verified in Lean or
another proof assistant, or accepted by the original problem authors.
The primary mathematical reduction and the general induction are explained
in the article and remain subject to human review. Executable checks do not
by themselves replace those arguments or a review of the checker.

The latest located explicit problem statement is Conjecture 1.5 in the 2025
Choi–Tarnu paper. Targeted searches through 20 September 2026 located no prior
resolution of this discrete conjecture. That search does not rule out an
unindexed or unpublished proof. Known growth-rate bounds and matrix
recurrences are credited as prior work; novelty is claimed only for the
maximizer classification and its consequences, subject to this search limit.

## Exclusion manifest

The supplied manifest describes 71 other research packages. It was used as
an exclusion list, not as independently verified evidence that its claimed
proofs are correct. None of its problems concerns the Rudin–Shapiro
maximizing-shift conjecture.
