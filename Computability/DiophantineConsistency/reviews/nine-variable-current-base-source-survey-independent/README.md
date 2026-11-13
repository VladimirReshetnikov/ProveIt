# Independent review: nine-variable source survey

**PASS as a read-only, source-declared inventory.** The frozen
[survey](../../research/nine-variable-current-base-source-survey/README.md)
reports 1,212 project sources: 995 shared with the recorded fresh current14
base and 217 extra. An independent lexer suppressing nested comments, line
comments and strings re-read every current source, confirmed its SHA-256 and
import list, checked the current `lakefile.toml` project-root mappings and
verified reachability from all three targets. The reported 217-module order
contains each extension module once, with every extension dependency before
its importer. The checker also rehashed the shared base's recorded output and
companion inventory and 4,163 direct-input edges covering 1,096 paths.
It independently checked current object existence, path resolution and
hashes for all recorded external-provider candidates.

[`check.py`](check.py) ran with observed exit 0; [result.json](result.json)
retains the result. A separate rerun of the original survey also exited 0,
and differed from the frozen result only in `git_head` and `free_bytes`.
The two entry-point refusal controls reproduced exit 1 with the recorded
messages. The original terminal observation records session 1592 exit 0;
we did not observe that earlier process ourselves. No Lean or build ran in
this review. The independent parser is an additional source check, not Lean's
own parser or a `lean --deps`/dynamic dependency analysis.

The result is not a build acceptance gate. Its scanner reads `lakefile.toml`
to classify project roots but the surveyed artifact does not pin that file;
the review's hash is only a point-in-time observation. The survey records
missing or differently hashed external candidates in lists rather than
refusing to print its inventory status; the frozen lists happen to be empty.
Recorded direct-input bytes are rehashed, but their original path resolution
and all transitive external dependencies are not authenticated here.
Provider companion/shadow resolution, possible Matrix incompatibility,
between-observation changes, and build memory/disk costs remain unresolved.
The historical scanner executes a read-only historical preflight when loaded;
its historical provider roots must exist, and their availability is not proof
of coherence with the current base.

Before using this inventory to build, pin the lakefile and freeze/revalidate
source bytes and imports; make missing or ambiguous externals hard errors;
authenticate selected providers, companion files, direct and transitive
resolution, and shadow paths; inspect actual Lean dependencies and Matrix
compatibility; and audit a resource-bounded runner. The survey did not compile
the 217 modules, create an endpoint or establish any equation equivalence.

Independent checker SHA-256
`41c8696a90cd55b947ac4ce6bf2b4ed0057439bbcec013f00dac36b9bca0f988`;
result SHA-256
`4938cbdb8f0ea296a78a1ba72cefb095498801f871fe8422a63507ddae380a98`.
The frozen survey source/result pins are in the checker. The observed
lakefile SHA-256 is in the result, without a claim about its value throughout
the original survey.
