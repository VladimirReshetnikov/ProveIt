# Sources and research boundary

Checked on 29 September 2026. Repository material was retrieved through the
GitHub connector; literature was checked against publisher/author sources.

## Repository source

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pin: `9754e83603e223811b7515eb892f22c847144593`  
Article blob: `c48fb7fea57f8efd4c705d858c33e58bdbd9a867`

Directory:
`SetTheory/Cardinals/docs/reports/ordinals-and-order-types/wqo-powersets-and-statures/cofinal-strata-of-finitary-powersets/`

Inspected README and article sections include the height-two formula (Theorem
35.1), the complexity questions in Section 37, and the structural FPT question
`nh:prob:fpt`. The indexed repository search for "uniquely restricted" returned
no result. This does not establish global novelty or absence from unindexed,
binary, incoming, or later material. The pinned main commit introduced new
incoming report archives; these were not unpacked or exhaustively compared.

## Primary literature

**Golumbic, Hirst, Lewenstein (2001), Uniquely Restricted Matchings.**
Algorithmica 31, 139–154. DOI 10.1007/s00453-001-0004-z.
Publisher: https://link.springer.com/article/10.1007/s00453-001-0004-z
Author/institutional page: https://research.ibm.com/publications/uniquely-restricted-matchings

Used for the classical definition, bipartite NP-completeness, and the historical
matrix-rank motivation. The matching characterization is re-proved in the
manuscript. The source's abstract explicitly states the bipartite hardness
result; the original NP-hardness construction is not reproduced here.

**Brešar, Henning, Rall (2016), Total Dominating Sequences in Graphs.**
Discrete Mathematics 339, 1665–1676. DOI 10.1016/j.disc.2016.01.017.
https://arxiv.org/abs/1601.07525
https://arxiv.org/html/1601.07525v1

Used for the established legal covering-sequence / Grundy covering framework,
particularly its section on hypergraph edge-covering sequences. Some regenerated
HTML displays a 2026 date in the body; the submission and publication metadata
identify the work as 2016. It is not cited as a new 2026 result.

**Francis, Jacob, Jana (2018), Uniquely Restricted Matchings in Interval Graphs.**
SIAM Journal on Discrete Mathematics 32(1), 148–172.
DOI 10.1137/16M1074631.
https://epubs.siam.org/doi/10.1137/16M1074631
https://arxiv.org/abs/1604.07016

Used only for the stated linear-time maximum-UR-matching algorithm in bipartite
permutation graphs and its immediate uniform-height transfer. No weighted
algorithm is inferred from that unweighted result.

## Deliberate limits

The ordinal-height correspondence and weighted residual recurrence were checked
against the inspected repository question and the primary matching literature.
No conclusion that they are globally unprecedented follows from this targeted
search. The manuscript therefore distinguishes proved consequences from novelty
claims. All numerical assertions about the delivered software are supported by
its included executed verification record rather than by outside sources.
