# Sources and bounded overlap / priority audit

Prepared 3 October 2026. The sources below were inspected during preparation.
The mathematical statements derived in the report are distinguished from earlier
identities and previously posted numerical predictions.

## Primary enumerative source

Emanuele Munarini, Maddalena Poneti, Simone Rinaldi, *Matrix Compositions*,
Journal of Integer Sequences 12 (2009), Article 09.4.8.

- Landing page: https://cs.uwaterloo.ca/journals/JIS/VOL12/Rinaldi/rinaldi.html
- PDF: https://cs.uwaterloo.ca/journals/JIS/VOL12/Rinaldi/rinaldi.pdf
- Proposition 1: rational generating functions.
- Proposition 12: finite roots-of-unity formula.
- Proposition 13: fixed-row asymptotics.
- Proposition 29, equation (36): the positive Stirling/Fubini transform.
- Relevant PDF pages were inspected as images as well as parsed text, including
  printed pages 3 and 18 (zero-indexed pages 2 and 17).

These results are credited, not presented as new identities. The article's kernel,
uniform-error arguments, Gaussian coefficient implementation, and inverse discussion
are developed self-containedly.

## OEIS entries

- A261780: https://oeis.org/A261780
  Definition of the unrestricted-row matrix-composition array; rational generating
  function and the reference to Louchard. Entry originates with Alois P. Heinz.
- A261781: https://oeis.org/A261781
  No-zero-row triangle. The inspected entry explicitly labels recurrence order
  k(k+1)/2 and growth-constant difference limit 1/log(2) as conjectures in a comment
  attributed to Vaclav Kotesovec, October 14, 2017.
- A261784: https://oeis.org/A261784
  T(2m,m). It already posts the leading asymptotic, the Lambert-W growth rate,
  and a long decimal prefactor, attributed to Kotesovec, February 18, 2017,
  updated April 20, 2024. That line is NOT explicitly labeled a conjecture.
- A261784 b-file: https://oeis.org/A261784/b261784.txt
  Identified through the entry and inspected in the web interface. The entire
  file was not transferred into the computation environment, so the package
  does not claim a full 201-term external b-file comparison.

The verifier uses eight displayed triangle rows and fifteen displayed diagonal terms
as independent finite fixtures. The 201 values in results/a261784_exact.txt are computed
by the supplied program, not copied from an externally downloaded b-file.

## Related probabilistic source not retrieved

G. Louchard, *Matrix Compositions: a Probabilistic analysis*,
Pure Mathematics and Applications 19 (2-3), 127-146 (2008), listed in A261780.
The listed legacy URL is
http://www.ulb.ac.be/di/mcs/louchard/louchard.papers/compmat.ps

The full text could not be retrieved during this preparation. The 2009 paper also
lists a related GASCom 2008 conference version. Because this related source was not
inspected, no categorical first-in-the-literature claim is made for the Poisson or
uniform asymptotic results. Proving a result and establishing its historical priority
are different tasks.

## ProveIt repository

Repository: https://github.com/VladimirReshetnikov/ProveIt

The recursive tree request returned SHA:
`d68b65ea064084fb121df9bb431b21d086f7be81`.

The file
`Analysis/Transseries/docs/series-and-transseries/README.md`
was read at that revision; its blob SHA was
`7bdc83aebc78b727bf9f8c5224d2da1d3d96f00f`.
It documents the Fubini / transseries / inversion program and the distinction
between smooth inverses, residual brackets, and discrete staircases.

Indexed repository searches for A261781 and A261784 returned no results.
However, populated search results exposed revision
`ce37e13f4aa16819c87c3ccc611362d15758f2ac`, different from the tree revision.
This is therefore a bounded indexed overlap search, NOT an exhaustive current-tree
proof of absence. An initially considered A260879 topic was rejected after the
search returned an existing report treating it.

No uninspected repository proof or formalization is used as a mathematical assumption.
No GitHub files or OEIS records were edited.
