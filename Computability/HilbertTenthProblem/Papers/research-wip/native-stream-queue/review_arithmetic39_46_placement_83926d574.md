# Arithmetic Reports39/41/43/45/46: scoped placement intake

At reviewed HEAD **83926d5744fdcc28139396bcd5f4a90e09861ede**, the new
arithmetic evidence is a byte-identical placement of already received files.
**The main article and README were not updated:** despite placement commit
992aaafb3's message, this revision contains no PartsVI–VIII in the article.
The established universal bound remains **84=47M+37A**,18 positive witnesses,
exact degree187. No newly proved smaller universal polynomial is identified.

This finding is pinned to this revision, not to any later manuscript edit.
No repair to another author's assembly was attempted.

## Exact provenance and absent article changes

The comparison is from `0c4b1c1e229f7ff557ac48049d4b10b4d7b2899a` to the
reviewed HEAD. Placement commit is
`992aaafb3ea431b68ff0376a6622ededee92026e`. The original five archives are
at `c5612efa171fa62470285049ee45d1d06ee25578`.

All paths below are relative to
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/fixed-universal-polynomials/`.

| Unchanged main file | Git blob at both revisions | SHA256 |
|---|---|---|
| README.md | 563aa1065464074a3ef76dcc6ea89537bc88b34f | 1dc77bd29642ffbd5c3c900ff35ae291bf30428ed7be81632db3b3000d9807f0 |
| article.tex | 21db9daca83b4523da3e8950e209b14d10913483 | c68b7a9548a7796ffb3978621616ffb3d7b90ad752280197d768de3973324cff |

README lines5–21 still describe Reports23/24/25/33/34/37 and PartsI–V.
The complete article's only five part headings are at lines260,1040,1652,
2442,3701; it has4364 lines. Thus the commit message's intended mapping is
useful provenance, but it cannot substitute for an actual article diff or
be called reviewed manuscript text.

The [inert manifest](review_arithmetic39_46_placement_83926d574.json), SHA256
`2860dd3c53f8fcff0e1ba3810c7f06a1ac35b64e3d9ff83c426cb92bef151689`,
authenticates the five original archives and all408 members against the
[earlier scoped review](review_incoming_arithmetic_reports_39_46.md)'s saved
inventory. Every one of the **235 added files /1,203,291 bytes** matches an
original member exactly. Each mapping records its immutable placed Git blob,
SHA256, size and all matching archive/member identities. There are no new
evidence bytes in those235 files. This authentication does not certify every
proof or every recorded computation.

## Intended parts and actual evidence

| Intended part in commit message | Placed prefix | Report | Files | Scientific status in the reviewed scope |
|---|---|---:|---:|---|
| VI | 16-nonredundant- |39|39|Jacobi obstruction excludes the omitted main congruence on a reduced family; no full smaller-polynomial zero follows.|
| VII | 17-index-deletion- |41|62|Full first-index-deletion counterfamily; historical81/82 candidates, already transferred to the current80 deletion.|
| VIII | 18-free83- |43|38|Structural auxiliary/divisor restrictions for the free-coefficient83 chart; its language was separately refuted.|
| VIII | 19-square-product82- |45|28|A second all-input counterfamily for the square/product82 chart, already refuted by the research tree.|
| VIII | 20-cert-height- |46|68|Height/minimum results for that counterfamily and an even-rank nonextension with outer data fixed.|

The Report46 even-rank theorem does not contradict the odd-prime free83
collapse: it prohibits changing only the auxiliary coordinates over one
specified even-rank outer tuple. The odd-prime counterfamily changes that
tuple. Its fixed-outer auxiliary minimum likewise is not a lower bound for
all zeros of the polynomial.

Two explicit historical labels survive unchanged. Source
`16-nonredundant-evidence-README.md:9` says no omitted-congruence failure has
been proved; `16-nonredundant-jacobi-README.md:3–5` explicitly supersedes that
stage. Source `17-index-deletion-evidence-README.md:3–6` names81/82 deletions
and the then85 bound. Those are dated source labels, not the current bound.
No new article write-note contextualizing them exists at the reviewed HEAD.

## The operation names must remain distinct

These counts were matched to the existing source receipts and theorem notes,
not recounted by executing any placed program:

| Actual source | Operations | Witnesses | Degree | Status |
|---|---:|---:|---:|---|
| complete84_scaled_strong_output |47M+37A=84|18|187|Established universal construction|
| complete83_independent_gamma_scout |47M+36A=83|18|187|Ordinary-input language unresolved|
| complete83_free_coefficient_scout |46M+37A=83|18|111|Inherited compiler language refuted|
| complete82_auxiliary_square_product_chart |45M+37A=82|18|185|Inherited compiler language refuted|
| complete80_first_index_deletion_collapse |45M+35A=80|17|180|Inherited compiler language refuted|

Report41's two historical deletion sources are normalized81=46M+35A,
17 witnesses, degree168, and ordinary82=45M+37A,17 witnesses, degree124.
They are not the82/degree185 square/product source. The normalized81 to
current80 transfer is the full all-value identity `F80=Delta*F81`, with
Delta positive on the retained positive interface. It is already recorded
in [the current80 theorem](complete80_first_index_deletion_collapse.md).
Neither a refuted count nor the free83 refutation resolves gamma83.

## A useful newly read component: smooth counterfamily radix

The full `17-index-deletion-smooth-SMOOTH_RADIX.md` was read here. It is
already in the arrival archive, not a newly arrived theorem. Its elementary
refinement is sound within the stated inherited counterfamily interface.
For fixed genuine `d=5^r`, `r>=1`, choose the least `k>=0` with

```
t=4400*d*2^k >=4*max(I,ceil(log2(K+1))),  I=2dx+b.
```

The odd part of t is275d. The Euler periods for `5^(r+2)` and11 divide t,
so `2^t=1` modulo that odd part. Also N=t/d remains a multiple1100; the
original CRT and55-divisibility arguments apply. The new residue exponent
satisfies `3<=e<1100d<=t/4`. Its bounds on K,W,Z give
`F<2^(t/2+2)` and `2Z+W+2dx<=2^(t/4+1)`, proving the same strict outer
slack. No later use of the original stronger K,W<=t is needed in the
reviewed source interface. The original rank/input/auxiliary construction
and deleted-index remainder25u-1 are retained.

Minimal k gives `t<=max(4400d,8*max(I,ceil(log2(K+1))))`, so q=2^t is at
most singly exponential in the **numerical ordinary input x**, for a fixed
compiler. This is a counterfamily radix-height improvement only; it neither
bounds every downstream Pell witness nor changes the paid source or count.
The accompanying endpoint erratum correctly restricts the strict Pell upper
bound to indices>=3; the counterfamily uses indices at least40 and55.

## Read boundary

The manifest lists exact line ranges and hashes. This intake fully read the
seven newly placed component READMEs, the smooth-radix proof and erratum,
Report41 source correspondence, the placed84 baseline audit and Report46
even-rank proof: **12 complete placed text files**. It additionally read
Report45 counterfamily lines1–85, the prior scoped intake in full, selected
current theorem interfaces, the main README opening, every article part
heading and the placement commit message. The main article PartsI–V were
not rereviewed; PartsVI–VIII are absent.

The prior intake's limitations remain: Report39's long analytic existence
proof, all Report43 addenda, Report45's recorded executions and Report46's
analytic logarithm/inverse expansions are not newly certified. No archived
or placed code was executed, no stored arithmetic schedule evaluated, no
historical suite rerun and no repository file changed.
