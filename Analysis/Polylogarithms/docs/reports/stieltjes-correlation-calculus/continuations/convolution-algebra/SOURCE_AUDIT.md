# Source audit and contribution boundaries

## Repository snapshot

`VladimirReshetnikov/ProveIt`, main pinned to `0efdbaa6944357e578a8839ec88d040c6e05681c`, dated 10 October 2026. Initial discovery reads used main; the final audit uses this explicit pin. This is a selected-area audit, not a review of the entire manuscript or every incoming delivery.

## Material inspected

| Source | Material used | Consequence |
|---|---|---|
| `Analysis/Polylogarithms/docs/manuscript/polylogarithms.tex` | Manuscript structure, notation, proof/numerics distinction | Retain ordinary-proof versus finite-certificate versus numerical-evidence distinction. |
| `chapters/07-integration.tex` | Log-Gamma examples; Stieltjes Laurent convention; antiderivative ladder; Hurwitz moments | Continue the jet calculus rather than replace it; use the same Stieltjes signs. |
| `chapters/08-differentiation.tex` | All-index elementary-symmetric derivative formula; character/distribution setting | Derive the new contact correction for periodic finite parts. The pointwise theorem is not disputed. |
| `chapters/10-discovery.tex` | Current surviving problems; conventions; proof status | S4 is already proved at this snapshot. Do not claim a new resolution of it or numerical period independence. |
| `chapters/07-reflected-moments.tex` | Reflected pointwise Gamma moments and asymptotic coefficients | These are not the circular convolution powers developed here. |
| `docs/incoming/` inventory and `docs/incoming/README.md` | Delivery structure, pending archive names, intake/placement instructions | Deliver a standalone report package without editing remote files; no claim that pending binary archives were exhaustively read. |

Paths in the middle four rows are relative to `Analysis/Polylogarithms/docs/manuscript/`.

## Primary literature checked

Zhi-Hong Sun, *On the properties of invariant functions*, arXiv:2209.14625 (2022), Remark 3.2: the normalized Hurwitz convolution law for real parameters greater than one is already stated. The article attributes this fact and does not claim the nonsingular semigroup as new. The relevant equation was checked in the extracted paper text; repeated web PDF-screenshot attempts failed, so no claim is made of visual inspection of that source PDF.

NIST DLMF Sections 25.11 and 25.12: Hurwitz Fourier/shift/derivative identities and the polylogarithm framework. Used as standard input, not a novel finding.

Olivier R. Espinosa and Victor H. Moll, arXiv:math/0012078 and arXiv:math/0107082: definite/indefinite Hurwitz-zeta integral calculus, log-Gamma moments, and negative polygamma context. The zero-shift second moment is classical.

Mark W. Coffey, arXiv:0905.1111: all-order derivatives of the Stieltjes functions. The pointwise tower is classical input; its canonical periodic finite-part extension is a separate normalization problem.

## Claims proved in this delivery

1. The canonical finite-part Stieltjes normal form and all-index convolution multiplication rule, including its one-generator algebra interpretation.
2. Explicit absolutely convergent subtractions realizing all products off the singular point.
3. The derivative contact coefficient `(-1)^(n+1) n! e_(n+1)(k)` and the resulting full differentiated-convolution rule.
4. The two-jet polygamma reduction and explicit convergent trigamma integral.
5. All mixed integrated-jet convolutions and the Bell-polynomial formula for every log-Gamma convolution power.
6. Reflected spectral identity and shifted log-Gamma correlation, with rational-shift conversion to finite Hurwitz grids.

These are results proved here, not a comprehensive claim that no equivalent identities occur anywhere in the literature. The article states all conventions and gives its analytic arguments in full.

## Not claimed

No named surviving S6/golden-ladder conjecture is claimed resolved. No period-independence result is claimed. No complete arithmetic reduction of the ordinary cubic log-Gamma moment is claimed. No theorem in the selected current manuscript was conclusively shown false. No remote file edits, Lean proof, interval certification, or exhaustive incoming-archive review was performed.

## Proposed corrections

See `integration/CORRECTIONS.md`. Two are local editorial clarifications in existing material. The contact-term issue is a proved correction to a tempting extension of that material, not an accusation that the source prints the false extension.
