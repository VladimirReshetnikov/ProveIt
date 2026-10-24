# Shorter complete seed descriptions

Three further standalone pages pass complete finite checks. The771-digit seed is unchanged; its initialization tile is corrected
as explained in [INITIALIZATION_CORRECTION.md](INITIALIZATION_CORRECTION.md). No Lean was edited or invoked.

| Display | Printed seed symbols | Seed bits | Recipe nonwhite characters | Whole page nonwhite characters |
|---|---:|---:|---:|---:|
| Original decimal page | 1294 | 4298 | 2861 | 3584 |
| Frozen BFS decimal, collected selector | 771 | 2561 | 2518 | 3135 |
| New merged masks, decimal | 781 | 2594 | **2482** | **3099** |
| New merged masks, base62 | 436 | 2594 | **2297** | **2914** |
| Original tuple, base62 and collected selector | 722 | 4298 | **2424** | **3147** |

Each PDF has exactly one Letter page, uses the existing fonts, and has no
overfull boxes. The same `pdftotext -raw` convention measures every row. The
recipe includes the complete numeral, its decoder, its alphabet and every
coefficient definition. It starts at “Fixed coefficients” and ends after
the numeral. There is no external mathematical input to any printed page.

The new decimal decoder reduces the recipe by 36 characters even though its
literal integer grows by ten decimal digits. The base62 form then saves a
further 185 characters after paying for the **full printed alphabet and
explicit positional sum**. Its total recipe gain over the frozen771 page
is 221 characters, about 8.8%. This is a notation and decoder improvement,
not an information-theoretic compression claim.

The original-tuple variant is useful when preserving every coefficient is
preferred. It changes only the numeral notation and the already proved
selector display. It retains all 215492 original raw coefficient bytes.
Compared with the original page, its recipe and whole page each shrink by
437 characters. Its recipe is also 94 characters shorter than the frozen
BFS page's, although its whole page is12 characters longer because it keeps
the original title and longer proof-boundary explanation.

## Merging two bit masks and avoiding an alphabet decoder

Keep the same BFS-renamed machine, discovery bits and exceptional flag rows
as the frozen checkpoint. Let N be its 430-bit discovery mask, M its row
exception mask, and T its 216 stored targets in base216. The four leading
zero bits of N are still reserved. Put

```
L = N + 2^430*M,
E = sum_(k=0..70) f_k*16^k,
A = L + 2^636*T + 2^2311*E,
```

where f_k is the actual four-bit flag code of the kth exceptional row.
The field widths are 636,1675,283 bits. The previous scheme spent four
separate fields on N,T,M and a base12 exceptional-alphabet rank. The new
scheme places the two masks in one field and stores exceptional flags
directly. Its integer is 33 bits larger, but its printed formulas are shorter.

Write D_b(A,j)=floor(A/b^j) mod b. The complete new decoder is

```
L = A mod 2^636,
T = floor(A/2^636) mod 2^1675,
E = floor(A/2^2311),
nu_j = D_2(L,j),                sigma_j = sum_(k<j) nu_k,
m_q = D_2(L,430+q),            tau_q = sum_(k<q) m_k,
F_q = 14*(1-m_q)+m_q*D_16(E,tau_q),
u_j = nu_j*(1+sigma_j)+(1-nu_j)*D_216(T,j-sigma_j),
v_(2q+r) = D_2(F_q,2r),        d_(2q+r) = D_2(F_q,2r+1).
```

All index ranges and the literal A are printed on each page. Every one of
the 430 decoded actions equals the frozen BFS action exactly. Reconstructing
all native modes, ranks and coefficients gives the same whole BFS tuple,
including all bytes of its changed K. Thus no new state conjugacy or native
calibration premise is introduced beyond the frozen BFS checkpoint.

## Positional notation is stated completely

The base62 pages print the full alphabet

```
0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz
```

Its positions0 through61 are the digit values. For the m printed
characters, the page explicitly defines

```
A = sum_(j=0..m-1) epsilon_j*62^(m-1-j),
```

with the actual fixed limit435 or721. The digit values epsilon_j are
distinct from the transition-direction constants d_j. Every alphabet index, the complete
positional sum, and every extracted PDF character is checked. The full
alphabet plus sum adds **160 printed nonwhite characters** relative to the
decimal heading. That entire overhead is included above. Base62 does not
reduce the number of bits of the integer, and is not presented as a shorter
machine program or coefficient payload. The decimal variant remains
available for readability and for a comparison independent of notation.

## Predictors that did not pay for their decoders

Simple next-state predictors are weak on these tables. On all430 original
actions, q-1,q,q+1 match only6,21,4 targets; on the BFS table they match
8,21,23. The most frequent fixed target appears nine times. The best
read-conditioned prediction of the form a_r*q+b_r, with a_r in{0,1}, matches
28 original targets or35 BFS targets. A new430-bit exception mask costs more
than those matches save.

After the existing214 discovery targets have already been omitted, there
are216 stored BFS targets. Only21 are self-loops. Another216-bit exception
mask would need roughly28 omitted base216 digits just to pay for its bits,
before its printed decoder is charged. Splitting the predictions by flag
or flag/read adds several coefficients and cases; exact match counts and
the best small affine pieces are retained in `PREDICTOR_REVIEW.json`.
No shorter complete recipe from those cases was found.

Depth-first state renaming creates171 or169 q+1 targets, depending on the
first read branch. That is fewer than the214 implicit targets of the BFS
discovery encoding. It therefore increases the stored target stream.
Read1-first BFS gives the same781-digit merged payload and additionally needs
to translate the read order. It offers no displayed saving here.

Directly packing rotated row flags in base15 eliminates their exception
mask and prefix count, but its decimal seed grows to875 digits. Its tested
complete recipe has2542 characters, exceeding the corrected2518. A joint
base60 packing of discovery/rotated-flag row codes needs887 digits and2550
recipe characters. These probes illustrate why payload and decoder size
must be assessed together. Variable-width targets likewise save bits but
need a longer offset and halt-symbol decoder; they were not adopted.

## Artifacts and replay

The new directories under `candidates/one-page-compression/` are
`merged-mask-decimal`, `merged-mask-base62`, and `original-base62-collected`.
Each contains standalone TeX/PDF, the exact seed and normal/optimized
receipts. The original and frozen BFS directories are read only.

From this research directory:

```sh
python3 tools/research_seed_predictors54.py --render
python3 -O tools/research_seed_predictors54.py --render
```

All seed, TeX and PDF bytes agree between the two runs. The tool explicitly
checks all transitions, each complete coefficient's bytes, both selector
identities, and all alphabet/positional/PDF characters. Acceptance uses
exceptions, not removable assertions. The new pages specify coefficients;
the inherited unbounded native/Pell interpretation and its internal-ZFC
formalization remain separate proof obligations.
