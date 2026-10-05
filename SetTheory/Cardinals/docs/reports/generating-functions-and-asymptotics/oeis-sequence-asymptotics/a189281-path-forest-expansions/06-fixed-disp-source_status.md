# Source and priority check (2026-10-01)

The current OEIS entry https://oeis.org/A189281/internal (revision dated
2025-11-07) defines a(n) by pi(i+2)-pi(i)!=2. It lists
a(n)/n! ~ exp(-1)(1+3/n+2/n^2), and explicitly labels the order-eight
recurrence conjectural. Neither the OEIS wording nor a failed search proves
that an asymptotic proof does not exist.

Primary sources actually inspected:

1. Kauers and Koutschan, *Guessing with Little Data* (2022),
   https://arxiv.org/abs/2202.07966 and author PDF
   https://www.algebra.uni-linz.ac.at/people/mkauers/publications/kauers22b.pdf .
   Conjecture 10 calls the order-eight, degree-eleven recurrence conjectural.

2. Spahn and Zeilberger, ECA 3:2 (2023), S2R10, author manuscript
   https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimPDF/permsV2.pdf .
   Pages 4--6 give the exact paired-tiling formula used here; the final
   challenges include proof of the guessed recurrence. The live author page
   https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimhtml/perms.html
   has an August 14, 2026 update reporting a proposed solution of the separate
   general-holonomicity challenge by Jaideep Sai Padhi.

3. Padhi, *Holonomicity of the restricted permutation counts a_rs and b_rs*,
   August 2026, source
   https://github.com/jaideepsaipadhi/restricted-permutations-holonomicity/blob/main/holonomicity-note.tex .
   Fetched source blob SHA ec04817377b7531d19cbc0d9b0243242de682a95.
   It claims general holonomicity through a bounded-seam construction. It
   contains no asymptotic expansion, does not derive the guessed operator,
   and cites an integral representation for a22 as a manuscript in preparation.
   Its README says not submitted or externally reviewed. We do not need or
   audit its global closure argument; the elementary seam bijection was
   already in the 2023 paper for a22.

4. Tabuguia, *D-Algebraic Guessing* (2025),
   https://arxiv.org/html/2510.26869v1 , Section 5.2.
   This reobtains the same recurrence by guessing and states Conjecture 5.1;
   it does not prove the enumeration recurrence.

5. Tauraso, *The dinner table problem: the rectangular case*, Integers 6
   (2006), A11, https://math.colgate.edu/~integers/g11/g11.pdf .
   This proves leading and first corrections for the related absolute-
   difference family b_dd and illustrates higher corrections for b_11.
   Component-defect counting and Poisson polynomial sums are therefore
   established antecedent methods, not new principles here.

6. Mendelsohn, *The Asymptotic Series for a Certain Class of Permutation
   Problems*, Canadian Journal of Mathematics 8 (1956), 234--244,
   https://doi.org/10.4153/CJM-1956-027-7 .
   Section 5 restricts to a known special constant-coefficient operator
   recurrence. Printed page 240 explicitly assumes the complete asymptotic
   series exists and then computes its coefficients. Its examples are
   rencontres, menages, ordinary rook-king successions, and adjacent forbidden
   positions. This is a classical antecedent for the correction calculus,
   not a located proof of the present fixed-(r,s) remainder theorem.

The bounded search located no primary source giving the complete directed
fixed-(r,s) expansion, the stable-long-chain universality statement, or the
discrete-threshold inverse estimates derived here. This is bounded search
evidence only. The work neither settles nor relies on the guessed recurrence.

ProveIt duplication check: origin/main 1512ef8, the current named-path and
incoming inventories, and the combinatorial-inverse companion were checked.
The companion covers ordinary Bell/Fubini numbers, involutions, alternating
permutations, connected labelled graphs, and other gamma-block examples;
it does not name A189281 or the fixed-displacement permutation family.
Its general gamma-core and Lagrange inversion tools are reused with credit.
