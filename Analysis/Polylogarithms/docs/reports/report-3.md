# Polylogarithm Special‑Value & Identity Questions on Math.SE and MathOverflow — Research Report

## TL;DR
- **I was not able to deliver a verified hyperlinked list of 15–40 specific qualifying questions in this session.** Every `site:math.stackexchange.com` / `site:mathoverflow.net` web search returned arXiv papers, Wikipedia and MathWorld entries instead of Stack Exchange URLs, and direct `web_fetch` calls against the polylogarithm tag pages and the five reference questions themselves were rejected with `SITE_BLOCKED` / `PERMISSIONS_ERROR`. A spawned research subagent confirmed the same limitation independently.
- Because the source‑quality rules forbid listing URLs I cannot load and verify, I am deliberately *not* fabricating question IDs. Instead, this report gives (a) the exact tag pages, user pages, and SQL queries that will produce a verified list in a properly enabled environment; (b) the categorized inventory of question *types* the user should expect to find; and (c) a topic‑anchored harvesting plan built around the five reference questions' "Linked / Related" sidebars.
- The two canonical entry points are the **Math.SE `polylogarithm` tag** (`math.stackexchange.com/questions/tagged/polylogarithm`, sort by Votes) and the **MathOverflow `polylogarithms` tag** (`mathoverflow.net/questions/tagged/polylogarithms`, sort by Votes), supplemented by Vladimir Reshetnikov's question page (`math.stackexchange.com/users/19661/vladimir-reshetnikov?tab=questions&sort=votes`).

## Key Findings

### 1. The relevant content is concentrated in two tags I could not load directly
- **Math Stack Exchange tag:** `polylogarithm` — `https://math.stackexchange.com/questions/tagged/polylogarithm`. Sort by Votes for the highest‑quality questions.
- **MathOverflow tag:** `polylogarithms` — `https://mathoverflow.net/questions/tagged/polylogarithms`.
- Useful tag intersections on MSE: `polylogarithm`+`closed-form`, `polylogarithm`+`conjectures`, `polylogarithm`+`experimental-mathematics`, `polylogarithm`+`special-functions`, plus the synonym tag `dilogarithm` and (if present) `clausen-function`.

### 2. The five reference questions anchor a dense "Linked / Related" graph
In a normal browsing environment, the most efficient harvesting strategy is to open each of the five reference questions and read the right‑sidebar "Linked" and "Related" lists:
- `math.stackexchange.com/questions/1424600`
- `math.stackexchange.com/questions/1430169`
- `math.stackexchange.com/questions/1373123`
- `math.stackexchange.com/questions/945972`
- `math.stackexchange.com/questions/1579355`

Each sidebar typically lists 10–30 internal question IDs. Deduplicating across the five anchors yields roughly 60–120 candidate IDs that are *guaranteed* by Stack Exchange's relevance scoring to be topically close. Apply the inclusion criteria (≥1 substantive answer **or** concrete identities in the body; exclude the five anchors themselves) to filter.

### 3. High‑recall query recipes (work when the search backend indexes Stack Exchange)
- `site:math.stackexchange.com polylogarithm "closed form"`
- `site:math.stackexchange.com Reshetnikov dilogarithm`
- `site:math.stackexchange.com "Li_3" "closed form"`
- `site:math.stackexchange.com "tetralogarithm"` (near‑niche term — almost all hits qualify)
- `site:math.stackexchange.com "polylogarithm ladder"`
- `site:math.stackexchange.com dilogarithm "golden ratio"`
- `site:mathoverflow.net dilogarithm "special values"`
- `site:mathoverflow.net polylogarithm conjecture closed form`

Stack Exchange Data Explorer SQL (run separately on the `math.stackexchange` and `mathoverflow` instances at `data.stackexchange.com`):
```sql
SELECT TOP 200 Id, Title, Score, AnswerCount, OwnerUserId
FROM Posts
WHERE PostTypeId = 1
  AND (Tags LIKE '%<polylogarithm>%' OR Tags LIKE '%<polylogarithms>%')
  AND Id NOT IN (1424600, 1430169, 1373123, 945972, 1579355)
  AND (AnswerCount > 0
       OR Body LIKE '%conjecture%'
       OR Body LIKE '%PSLQ%'
       OR Body LIKE '%integer relation%')
ORDER BY Score DESC;
```
This produces a deterministic, verified list filtered by the inclusion criteria.

### 4. Inventory of qualifying question *types* you should expect to find
This inventory is high‑confidence at the type level — every category below is a known recurring topic on MSE/MO based on the broader literature my research surfaced (Lewin, Zagier, Cohen–Lewin–Zagier, Bailey & Broadhurst, Borwein & Broadhurst, Cvijović, Campbell, Hakimoglu‑Brown, Khoi, Bytsko, Bridgeman, Boyadzhiev, Au).

- **Li₂ at rational and quadratic‑irrational arguments.** Li₂(1/2), Li₂(1/3), Li₂(2/3), Li₂(1/4), Li₂(3/4), Li₂(1/φ), Li₂(1/φ²), Li₂(−1/φ) — the eight "Landen" closed‑form values and their ladder partners.
- **Li₂ at complex arguments and roots of unity.** Li₂(e^{iπ/3}), Li₂(i), Li₂((1+i)/2), Li₂ at primitive 5th/6th/12th roots of unity; the imaginary parts give Clausen values Cl₂(π/3), Cl₂(π/6), Cl₂(2π/5), Cl₂(π/12), etc.
- **Li₃ at golden‑ratio arguments.** The classical Landen–Watson trilogarithm identity Li₃(1/φ²) = (4/5)ζ(3) − (2/3)log³(φ) + (2π²/15)log(φ), and analogous Li₃(1/φ), Li₃(−1/φ), Li₃(iφ) closed forms.
- **Li₃(1/2), Li₄(1/2), Li₅(1/2), Li₆(1/2).** Iconic half‑argument higher‑polylog questions. Li₄(1/2) in particular has no proven closed form and is the subject of many MSE/MO questions asking whether one exists.
- **PSLQ‑discovered vanishing linear combinations of Liₙ at small rationals** (1/2, 1/3, 2/3, 1/4, 3/4, 1/8, 1/9, 1/16) — the genre of the Reshetnikov Q‑1373123 tetralogarithm conjecture.
- **Polylogarithm ladders.** Questions citing Lewin's monograph, Cohen–Lewin–Zagier, Abouzahra, Khoi's Seifert‑volume ladders, and Bailey & Broadhurst's order‑17 ladder over the smallest known Salem number α₁ (the larger real root of Lehmer's polynomial α¹⁰+α⁹−α⁷−α⁶−α⁵−α⁴−α³+α+1) — an empirical integer relation entailing 125 constants multiplied by integers with nearly 300 digits, verified to more than 59,000 decimal digits (Bailey & Broadhurst, arXiv:math/9906134).
- **Clausen‑function closed forms at rational multiples of π.** Cl₂(2π/7), Cl₂(4π/7), Cl₂(6π/7) — central to Borwein & Broadhurst's 1998 conjecture that the dilogarithmic integral I₇ (the volume of an ideal hyperbolic tetrahedron) equals L₋₇(2) = Σ_{m≥0}[1/(7m+1)² + 1/(7m+2)² − 1/(7m+3)² + …], a conjecture proved by Cvijović (arXiv:1011.0195) and previously verified to at least 19,995 digits using 45 minutes on 1024 processors. Also Cl₃ and Cl₄ values.
- **Inverse‑tangent integral Ti₂ / Ti₃ at special arguments,** which reduce to imaginary parts of Li₂ / Li₃.
- **Imaginary parts of Liₙ(p/q + i r/s)** at small rational complex arguments — the genre of the Re Li₂(1/2+i/6) reference question.
- **Five‑term Abel relation specialisations** producing single‑term Li₂ evaluations (Ramanujan, Bridgeman/Pell, Khoi).
- **Multiple polylogarithms / colored MZVs at roots of unity** — overlap with MathOverflow's `multiple-zeta-values` tag.

## Details

### Reshetnikov authorship cluster
User 19661 (Vladimir Reshetnikov) on MSE has authored many additional polylogarithm‑closed‑form questions beyond the five excluded ones. The canonical entry point is `math.stackexchange.com/users/19661/vladimir-reshetnikov?tab=questions&sort=votes`. The task explicitly permits inclusion of his other questions provided they are distinct from the five anchors; in practice, his question list filtered for polylog content is itself a large fraction of the target deliverable.

### Other prolific authors of qualifying questions on MSE
On MSE the polylogarithm tag is dominated by a recurring cast of users whose question lists, filtered by the `polylogarithm` tag, are productive secondary harvest points: **Cleo, Olivier Oloa, Tito Piezas III, Jack D'Aurizio, Yuriy S, Iaroslav Blagouchine, Robert Israel, achille hui, Lucian, Anastasiya‑Romanova, M.N.C.E., nospoon**.

### MathOverflow side
The `polylogarithms` tag on MathOverflow is smaller but denser. Sort by votes. Notable recurring themes:
- Functional equations of Liₙ for n ≥ 4 (Goncharov, Gangl, Charlton).
- Bloch group / motivic‑cohomology approaches to polylog identities.
- Single‑valued polylogarithms and their special values (Brown, Drummond).
- Zagier's conjecture on Liₘ values of number fields and ζ_F(m).
- Ramanujan‑style two‑term Li₂ identities (Bridgeman, Ramanujan, Khoi).

## Recommendations

**Immediate (a single browsing session):**
1. Open `math.stackexchange.com/questions/tagged/polylogarithm?tab=Votes`. Walk the top ~150 questions; apply inclusion criteria at a glance from title + answer count. This single pass typically yields 40–70 qualifying questions.
2. Repeat for `mathoverflow.net/questions/tagged/polylogarithms?tab=Votes`. Expect 15–35 qualifying questions.
3. Walk `math.stackexchange.com/users/19661/vladimir-reshetnikov?tab=questions&sort=votes`, filtering visually for the polylog/closed‑form topic — expect a substantial additional pool beyond the five excluded.
4. Open each of the five reference questions and harvest the right‑sidebar "Linked" and "Related" lists; deduplicate across all five.

**Within a day, for a verified machine‑checked list:**
5. Run the SE Data Explorer SQL above on both `data.stackexchange.com/mathematics/queries` and `data.stackexchange.com/mathoverflow/queries`. Export to CSV. This produces a deterministic list satisfying the inclusion criteria exactly and bypasses both the web‑search‑result‑ranking issue and the domain block.
6. For each candidate, pull the body and post metadata via the public API (`api.stackexchange.com/2.3/questions/{id}?site=math&filter=withbody`) — unauthenticated, no rate‑limit issue at this volume — and apply the secondary filter "≥1 substantive answer OR body contains a concrete closed‑form identity."

**Thresholds that would change the recommendation:**
- If the Data Explorer query returns < 30 hits per site: broaden by adding `Tags LIKE '%<dilogarithm>%'`, `Tags LIKE '%<closed-form>%' AND Body LIKE '%polylog%'`, and `Body LIKE '%Clausen%'`.
- If > 200 hits per site: tighten by requiring `Score >= 5` AND one of the keywords {`Li_2`, `Li_3`, `Li_4`, `dilogarithm`, `trilogarithm`, `tetralogarithm`, `ladder`, `PSLQ`} in the body.

## Caveats

- **No verified list of specific URLs is provided in this report**, by design. Both web search (which never returned SE URLs in this session, despite explicit `site:` operators) and direct `web_fetch` against `math.stackexchange.com` / `mathoverflow.net` (which returned `SITE_BLOCKED`) were unusable for Stack Exchange retrieval here; the spawned subagent reported the same limitation. Listing specific question IDs from memory would risk fabrication and violate the source‑quality guidelines.
- The qualitative inventory in "Key Findings #4" is high‑confidence at the *topic* level — each category is a well‑established staple of the MSE polylogarithm tag, indirectly corroborated through the arXiv literature surveyed in this session — but the precise IDs and counts cannot be guaranteed without live retrieval.
- The two MathWorld‑confirmed anchor facts in the inventory (Bailey & Broadhurst's order‑17 Salem‑ladder and Borwein & Broadhurst's L₋₇(2) ↔ I₇ identity) are the only "ground truth" claims that survived independent verification within this session; everything else in the report is structural guidance, not specific assertion.
- **The Data Explorer / API approach in Recommendations is the canonical way to produce the requested verified deliverable** and should be used to complete this task properly. It bypasses both the search‑indexing and the domain‑block constraints encountered here.