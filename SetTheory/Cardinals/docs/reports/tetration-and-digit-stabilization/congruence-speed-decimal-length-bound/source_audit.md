# Primary-source audit

Checked for this report on 19 September 2026.

## Target statement

Marco Ripà, *The congruence speed formula*, Notes on Number Theory and Discrete
Mathematics **27**(4) (2021), 43–61.

DOI: https://doi.org/10.7546/nntdm.2021.27.4.43-61

Journal PDF: https://nntdm.net/papers/nntdm-27/NNTDM-27-4-043-061.pdf

ArXiv: https://arxiv.org/abs/2208.02622

The statement is Conjecture 1, journal page 46 (PDF index 3), or Conjecture 2.1,
arXiv page 3 (PDF index 2). Both pages were visually checked. It says that
b >= len(a)+2 suffices for V(a,b)=V(a) when a>1 and the final digit is not
0, 3, or 7. The theorem in the accompanying article refutes this statement.

## Later claim of confirmation

Marco Ripà and Luca Onnis, *Number of stable digits of any integer tetration*,
Notes on Number Theory and Discrete Mathematics **28**(3) (2022), 441–457.

DOI: https://doi.org/10.7546/nntdm.2022.28.3.441-457

ArXiv: https://arxiv.org/abs/2210.07956

On arXiv page 10 (PDF index 9), after the bound bbar(a) <= vtilde(a)+2,
the paper claims confirmation of Conjecture 1 of its reference 12. Reference 12
is the target paper. This page was also visually checked. The official journal
landing page supplied the journal bibliographic data; the official full PDF
of this later paper did not load reliably, so the substantive page check uses
the explicitly identified arXiv version.

For the counterexample, vtilde(A)=2547 while len(A)=2544. The exact onset 2547
satisfies the valuation bound but violates the decimal-length bound. The report
therefore does not present the problem as unambiguously still open in all later
sources. It identifies a false claimed implication and gives a direct finite
certificate plus an independent all-height proof.

## Related non-squarefree-radix observation

Marco Ripà, *Radix-r Congruence Speed Verification Tool (Python Script)*,
Zenodo version V3, 25 January 2026.

https://doi.org/10.5281/zenodo.18366408

The record notes that non-squarefree radices can produce periodic digit gains.
The report does not claim novelty for that qualitative observation. Its formula
for radices 2^u 5^v is derived directly from its proved prime valuations.

## Limits of the audit

Targeted searches by the paper titles, conjecture numbering, congruence-speed
terminology, and counterexample terminology did not locate an earlier instance
of the explicit counterexample. This is not an exhaustive priority search and
is not evidence that every unpublished or poorly indexed source was covered.
No author was contacted, no external review was solicited, and no online
publication or repository change was made by this task.
