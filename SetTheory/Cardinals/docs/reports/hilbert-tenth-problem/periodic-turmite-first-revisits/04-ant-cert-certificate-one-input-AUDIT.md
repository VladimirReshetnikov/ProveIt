# Two-sided U15 orientation: recovered and freshly rechecked

Primary source freshly inspected on 4 October 2026: Neary and Woods, [Four Small Universal Turing Machines](https://mural.maynoothuniversity.ie/id/eprint/12416/1/Woods_FourSmall_2009.pdf), Definition 3.1, equations (3)--(4), Table 1 (PDF page 8), and Table 16 (PDF page 17).

The published initial tape has program, padding, G=bc, then encoded data. The initial state is u1 and its scanned cell is the final c of G. Thus the split is

    ... <B> S^k b [c] D_B(w) ...

With b=1,c=0 and u1=A, the left nearest-first word is reverse(beta(<B>S^k b)); the right word is beta(D_B(w)). Valid encoded data begins cb, hence 01. Setting the right word empty is therefore not the published universal family. This does not prove that restriction non-universal; it shows the proposed shortcut lacks this source's support.

Table 16 leaves (u10,b) undefined, while (u10,c) is defined. The final halting prose says c in error. The report follows the table's J1 convention.

## Arithmetic consequence

The packet retains two positive MSB-first sentinel coordinates, sent(w)=2^n+sum w_i*2^(n-1-i). Its optional one-input certificate uses an explicitly paid positive Cantor pairing of those two coordinates. The proof and seven-gate charge are independent of any one-sided universal-machine assumption. No uncounted fixed-left program mask is introduced.

## Recovery boundary

This audit is new recovered prose; no old audit-file byte identity is claimed. The primary PDF was re-read through the web tool. The prior locally pinned PDF digest, retained historically, was 6274cb6828579c234bf9f62b8fecc64dea4bb1ae842b4e2e39b9bfc676114c1b; this recovered edition does not claim a new local PDF byte check. Frozen Report40's U15 table and simulation remain the authenticated implementation dependency.
