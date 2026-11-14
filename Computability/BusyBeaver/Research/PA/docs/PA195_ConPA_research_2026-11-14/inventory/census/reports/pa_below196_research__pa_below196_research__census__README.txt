CURRENT PA-CONSISTENCY TABLE CENSUS
ProveIt snapshot 3268f238cb6be4b9c68b6cddaf289f173f77566e

Run with Python 3.10 or later:

    python3 verify_census.py

The checker uses explicit exceptions and also works under python3 -O. It
verifies fifteen designated196-state tables, their hashes, all392 rows,
all196 states' rooted graph reachability, and pairwise nonisomorphism.
The fifteen include two experimental MP tables. Graph reachability is not
reachability along the unique blank-tape run. None is a new smaller machine.

The inherited U208 checker is attributed supplied code. Its complete elementary
helper checks replay eighteen local transformations, and its graph comparison
establishes that nine original U208 presentations form two rooted classes,
while eighteen additional helper variants add eighteen classes: twenty total.

CONTENTS

tables196/manifest.json gives exact original archive/member identities and
submitted proof status for each designated196-state table. Fourteen tables
are copied from the supplied selected196 census. The fifteenth is the later
twelve-rotation table in pa_consistency_research_2026-11-13 (2).zip, which
was outside the older census's pinned twenty-archive input. It is different
from every older representative. Its original dense bytes are unchanged.

twelve_rotation_replay.json records a fresh replay of that submitted verifier:
4959 arbitrary-register symbolic primitive contracts, unchanged3812-site CFG,
twelve rotations,392 rows, and the exact58294-transition blank startup pass.
This is executable symbolic evidence relative to the retained register-engine
contracts; it is not a new Lean or internal-PA endpoint. The large submitted
source verifier itself remains in the original pinned ZIP, not copied here.

archive_comparison.json covers all23 top-level incoming ZIPs at this snapshot.
archive_bytes_inventory.json pins every archive's SHA-256 and member count.
all_literal_tables_inventory.json inventories all1096 parseable .tm members
in these archives. It deliberately includes duplicates, controls, rejected
experiments, and inherited baselines. There are478 distinct literal byte
strings and473 distinct parsed tables. These are not accepted-machine counts.
The broad inventory was newly extracted and parsed; the complete original
archives are not redistributed in this compact census.

recursive_inventory.json extends that scan through every nested ZIP, to
depth seven. Deduplicating archive bytes yields36 unique archives containing
1223 .tm members,489 byte-distinct and484 parsed-distinct tables. All parse
successfully. The nested historical lineage adds no table below209 states;
the same five195 diagnostics are the only195-state files. This recursive
inventory can be rebuilt from the pinned original23 ZIPs with:

    python3 scan_original_archives.py /path/to/ProveIt/docs/incoming output.json

The historical lineage contains thirteen additional unique archive payloads,
including the Joint and PlainU209 families, selectedU212, U213, U214, U218,
U221, U222, and threeU211 packages. These are ancestor inputs, not novel
smaller constructions. The scanner never executes archived programs.

rejected195/ contains exactly the five195-state table files found in the23
archives. Native/dense rotated195 are duplicate presentations, so these are
four candidates. The manifest records the failure scope. A failed intended
source simulation is not by itself a proof about the blank-run halting set.
The current checker only recounts and hashes these diagnostics; it does not
freshly replay every reported rejection witness.

ATTRIBUTION

James Chang's PA196 and PA209 artifacts retain LICENSE.JamesChang. The
ProveIt contributions retain LICENSE.ProveIt. Original researchers are not
represented as having reviewed this new inventory. The U208 proof checker,
data, and provenance are copied unchanged from the supplied research packet,
whose README states their inherited origin. New census/checking code and this
inventory explanation may be reused under LICENSE.ProveIt.

CRITICAL PROOF LIMIT

The upstream Lean endpoint is PA |- Nonhalt(PA196) -> Con(PA). A proved
ordinary or formal internal reverse implication must be supplied separately
to meet the full requested PA biconditional. Neither a finite graph census,
symbolic instruction verification alone, nor a finite blank-tape trace fills
that arithmetic proof obligation. No verified sub196 machine is established
by this census, and no global state-count lower bound is claimed.
