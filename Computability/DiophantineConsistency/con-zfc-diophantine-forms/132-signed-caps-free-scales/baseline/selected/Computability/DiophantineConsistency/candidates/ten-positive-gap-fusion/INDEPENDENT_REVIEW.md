# Independent review

One adversarial review round was run by an independent Claude subagent that
received the package files and the cited parents (packages 113, 116, 118
and the research zero-offset proof), not the author's conclusions. It worked
read-only and kept its scripts in the session scratchpad.

## Verdict

Sound. No FATAL finding and no GAP. Lemma G and its corollary hold in the
fused kernel (every hypothesis before transport, the Pell-trace parity
argument; exact-integer toy instances at auxiliary index 7, and at index 3
the bound b ≥ c + 1 is shown to be genuinely needed). Lemma T holds for every
centre, both root signs and both coordinates. The later inherited steps use
the old majorant only through W > 0 and W ≡ 1 (mod g). Completeness and the
exact degrees (identity (5), formula (6), every register and term degree,
leading forms independent of K0, MC, MF) are correct. Each circuit is exactly
the stated row edit of 116's pinned schedule.

## Findings and resolution

| Item | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | MINOR | Novelty overtaken: the research session's 90d8b714f9 (16:29:41) has the same 89/288 polynomial (`zero89`, 89 rows), the 94/262 polynomial in 95 rows (`direct95`), and the same fused-kernel fifth-index argument; the reused-b packet (fc77fcd31a) already has the scaled sharp 92/278 polynomial (also package 117's) and the direct sharp polynomial in 98 rows | README and PROOF section 0 now credit both as concurrent; net new points stated as 94/262, 96/258, 97/254 and the lower-centre polynomials |
| 2 | MINOR | "Lemma G is not needed for the centred forms" is true only for the sharp centre; the lower centre's residue tau·f − Gamma can be near D·E | Corrected in PROOF section 0 and the README |
| 3 | MINOR | verify.py did not tie the circuits to section 1: mutations Kpos+3, e = kR−2, lowY = q·Y passed every check | verify.py now evaluates section 1 independently and compares with each circuit; all three mutations are caught |
| E1 | EDITORIAL | "Three published devices" lists four | Fixed |
| E2 | EDITORIAL | INDEPENDENT_REVIEW.md cited but missing | This file |
| E3 | EDITORIAL | Section 5 took the scaled witnesses from 113 (BFS tuple) | Now the zero-offset parent's data at the original tuple, completed by 113's tuple-uniform construction |
| E4 | EDITORIAL | A vacuous clause in the Pell-trace check | Rewritten |
| E5 | EDITORIAL | kappa < X·c understated; kappa < c holds | Fixed |
| E6 | EDITORIAL | Section 4 should name the scaled kernel's inherited interface | Now cites 113's licence section with the zero-offset proof |

## Identity table (actual and random ports)

| Circuit | Same polynomial elsewhere | Gain |
|---|---|---|
| scaled 89/288 | research `zero89` (89 rows) | tie |
| scaled lower 91/283 | none (new centre) | none (reused-b has a different 91/283) |
| scaled sharp 92/278 | reused-b `saturated_sharp` (92), package 117 (93) | tie |
| direct 94/262 | research `direct95` (95) | one row |
| direct lower 96/258 | none | one row against reused-b's 97/258 |
| direct sharp 97/254 | reused-b `direct_saturated_sharp` (98) | one row |

No circuit coincides with another under x = (w − 1)q, nor with 116, any of
113's eight, 118, 98/360 or 97/368. Not done: a full-size canonical witness
(infeasible) and a re-audit of the inherited source61/native/controller
calibration.
