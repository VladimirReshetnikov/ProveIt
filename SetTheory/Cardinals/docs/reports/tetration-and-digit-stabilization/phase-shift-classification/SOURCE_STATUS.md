# Sources and statement audit

Access date: 19 September 2026. This file records provenance, not an assertion
that all later or unindexed literature has been excluded.

## Selected conjectures

1. Marco Ripà, *Graham’s number stable digits: An exact solution*, Notes on
   Number Theory and Discrete Mathematics 31(3) (2025), 607–616.
   Official publication: https://doi.org/10.7546/nntdm.2025.31.3.607-616
   Consulted preprint: https://arxiv.org/pdf/2411.00015v2
   arXiv version 2, dated 12 September 2025. Definition 3.2 introduces the
   phase word. The appendix on preprint page 9 explicitly conjectures the
   21-word range and the 14-word even-base restriction. The final appendix
   was checked in the PDF, including its rendered page, rather than inferred
   from a truncated HTML rendering.

2. OEIS A376842, by Marco Ripà.
   https://oeis.org/A376842/internal
   Consulted revision #39, 30 March 2026. The comment still explicitly
   labels the 21-value range a conjecture.

3. OEIS A376446, by Marco Ripà.
   https://oeis.org/A376446/internal
   Consulted revision #40, 13 December 2025. The prescribed starting height
   is nu(a)+2, not the minimal permanently constant-speed height. Its
   28-value range is explicitly conjectured in the entry.

4. Original MathOverflow question 481090, 22 October 2024.
   https://mathoverflow.net/questions/481090/
   The retrieved question displayed no answer. Its older 23-word formulation
   includes 1397 and 1793, which the later 21-word formulation removes.
   The article addresses the later formulation and does not treat those two
   removed words as a new counterexample discovery.

## Established background, not claimed as new

Marco Ripà, *On the constant congruence speed of tetration*, NNTDM 26(3)
(2020), 245–260.
https://doi.org/10.7546/nntdm.2020.26.3.245-260

Marco Ripà, *The congruence speed formula*, NNTDM 27(4) (2021), 43–61.
https://doi.org/10.7546/nntdm.2021.27.4.43-61

Marco Ripà and Luca Onnis, *Number of stable digits of any integer tetration*,
NNTDM 28(3) (2022), 441–457.
https://doi.org/10.7546/nntdm.2022.28.3.441-457
https://arxiv.org/pdf/2210.07956

The eventual speed formulas and the general sufficient onset bound are
existing results. The article rederives the particular local identities
needed for a self-contained phase-classification proof.

## Height-one convention

OEIS A371074 explicitly identifies the total matching trailing digits of
a and a^a, including leading zeroes, with the speed at height one:
https://oeis.org/A371074

Accordingly the article takes V_1=k_1. The sum of speeds through height b
then equals k_b, as in Equation (1) of the 2022 paper. A uniform-looking
b-versus-b-1 formulation in the 2025 paper can invite subtracting the
actual v_10(T_1-T_0) at b=1. Doing so changes the anchored invariant.
The 2025 examples APS(301)=3971 and APS(901)=19 support the V_1=k_1
convention used here.

For balanced bases a=1+10^v*c, v>=2, the alternative height-zero count would
move B from 2 to 1 and produce 9,1397,1793,91 instead of 9,3971,7931,19.
The article therefore does not present base 901 as a counterexample.

## Base 21: a separate data discrepancy

The accessed A376842 entry lists 6248 at base 21. Exact local profiles give
k_b=b+1, V_1=2 and V_b=1 for b>=2, so B=2. The onset sequence A372490 also
lists B(21)=2:
https://oeis.org/A372490
https://oeis.org/A372490/b372490.txt

T_2 = 4421 (mod 10000) and T_3 = 2421 (mod 10000), so s_2=2. The phase
multiplier is 2 modulo 5, giving APS(21)=2486. The listed 6248 is the same
cycle begun at height 1. This appears to be an anchoring error in the listed
value. The supplied code preserves the consulted data and reports the
mismatch; no OEIS edit has been made.

All other admissible listed values between bases 2 and 59 agree with the
calculation. These comparisons concern the recorded version and can change
if the online entry is corrected later.

## Base 5

The article consistently uses the modular matching count k_2(5)=5, including
the leading zero in 03125. Discussions that clip the count to the four
written digits of 3125 change the initial speeds, but retain B(5)=4 and
APS(5)=5. This does not change any classification theorem.

## Scope of the status claim

The targeted searches and primary-source checks located no prior proof of
the complete classification. This does not prove novelty or establish
priority. The supplied document is an unrefereed mathematical draft with
full written proofs and executable exact checks, not a formally verified
or externally certified result.
