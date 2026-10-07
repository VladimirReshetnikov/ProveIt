# Data attribution and source scope

## Selected primary records

The bounded fixtures were transcribed from the official public OEIS repository
records read on 4 October 2026:

- A094926, revision 27 (19 April 2016), by Yasutoshi Kohmoto:
  https://github.com/oeis/oeisdata/blob/main/seq/A094/A094926.seq
  https://oeis.org/A094926/internal
  The 41 displayed integers specify the zero seed version. Its 3 June 2015
  asymptotic conjecture is attributed to Manfred Scheucher. The suggestion of
  square-root-order extra delays is prior motivation, not claimed here as new
- A094925, revision 20 (4 May 2021), by Yasutoshi Kohmoto:
  https://github.com/oeis/oeisdata/blob/main/seq/A094/A094925.seq
  The 38 displayed integers begin at index 1. The supplied conjectured
  original-index amplitude has 77 fractional digits. All are independently
  reproduced by the report's exact rational bounds
- A258639, revision 4 (6 June 2015), by Manfred Scheucher and Vaclav Kotesovec:
  https://github.com/oeis/oeisdata/blob/main/seq/A258/A258639.seq
  All 106 supplied fractional digits are checked. No new-digit priority is
  claimed

The JSON stores only bounded integer/digit fixtures and attribution metadata.
The raw record exports, diagrams, comments, programs, and full b-files are not
included. Linked Sage scripts and b-files were unavailable during the source
review; neither their contents nor their execution is claimed. Our geometry
is authored from the stated definition and checked against the listed terms.
All-stage identification relies on the coordinate proof, not finite replay.

## Neighboring model and mathematical overlap

Neil Fernandez's Spiro-Fibonacci Sequences, last modified 11 January 2003,
was read at https://borve.org/primeness/spirofib.html . Its square-spiral
nearest-two-term model and seed linearity are related background, distinct
from the selected rule adding all earlier neighbors of the preceding vertex.
The functioning non-www source was the basis of that inspection.

Public searches included the exact selected IDs, constants, hexagonal spiral
Fibonacci asymptotics, and spiro-Fibonacci growth. They did not identify a
directly preempting proof of these two specific conjectures or their geometric
fixed-order corrections. That is a bounded source review, not global novelty,
priority, or literature-exhaustion evidence.

Relevant prior methodology in the public ProveIt repository was inspected
read-only around revision 6bf7f30d0352f7596e70928b3d4f304914075907:
https://github.com/VladimirReshetnikov/ProveIt
The canonical Transseries_And_Inversion volume discusses Binet continuations,
residual/error transport, and sequence staircase separation. A previously
authored Fibonacci inverse treatment inspected in the source review concerns
the modulus of the real-argument Binet continuation and exponential-oscillatory
inversion. Those generic inverse principles are prior methods, not a novelty
claim of this report. The selected hexagonal feedback yields a different
ring-scale stretched-exponential hierarchy and integer corner layers.

Binet's formula, discrete variation of constants, summable positive product
bounds, finite operator substitution, and monotone interpolation/error transport
are classical mechanisms. The report's scope is the specific geometric model,
its exact certificate, its fixed-order correction hierarchy and profiles, and
a carefully bounded inverse conclusion. It does not claim a convergent infinite
operator series, a closed elementary amplitude, or unconditional exact ceiling
rounding from an asymptotic root.

## Code and release provenance

The geometry, rational certificate implementations, tests, and optional numerical
diagnostic are authored code. Release tooling adapts the preceding authored
report's offline, closed-inventory infrastructure. No external program or
previous research document is copied into this package. The explicit inventory
excludes private source-review material, raw exports, transient logs, bytecode
caches, and unrelated artifacts. The mandatory exact checks use only the Python
standard library; optional mpmath output is explicitly noninterval.
