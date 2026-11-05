# Nine-variable source closure on the fresh current14 base

This is a **read-only source survey, not a build or a replay**. The pinned
[`survey.py`](survey.py) uses the existing comment-aware source scanner to
traverse `IPRANineCurrent`, its `IPRANineChecks` client, and the distinct
`IPRAExplicitZFCFinal` endpoint. It records every source path, SHA-256 and
source-declared import, plus an ordered extension, in
[`result-final.json`](result-final.json). It rehashes selected base objects,
companions and recorded direct inputs. It does not invoke Lean or alter a
provider. The JSON is a source **manifest**, not a copied immutable source
tree; a later runner must freeze and revalidate source bytes again.

The final survey process, session 1592, actually exited 0. Its result has
SHA-256 `7aa788ec612ef2d1cf40e65cf16b507099532477cd581dfe2c560d7b934d31ca`;
the survey source SHA-256 is
`8889c71de40c550f369cc950b4f90d4d8ed4a3afc45bd44099a1cd54c8e2ebf6`.

The selected source-declared union contains **1,212 project modules**:
995 match the current14 fresh-base snapshot in both source hash and declared
imports, while **217** are additional, including the check client. The two
endpoints alone have a 216-module extension. The retained extension order
is topological for the scanner's project edges. Each of the 995 shared
base modules had its recorded output/companion inventory rehashed; 4,163
recorded direct-input edges, covering 1,096 distinct paths, were also
matched to source-declared imports and rehashed. The base state itself is
the separately audited single fresh build; its package-transitive, dynamic
and between-observation limits remain.

The survey found 22 declared external module names beyond the base's
declared external list. Every declared external had at least one object
candidate in the recorded package or toolchain roots, and none had
different-hash candidates in both roots. These are point-in-time candidate
hashes, not package rebuilds or selection guarantees. The known conflicting
`Foundation.Vorspiel.Matrix` and
`Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber` are not direct external
leaves in this source scan. **Matrix compatibility remains unresolved:**
package-transitive or dynamically loaded imports may still reach either or
both declarations. Future work must inspect actual `lean --deps`, providers,
companions, shadow paths and package-transitive compatibility.

The final disk observation was 11,917,246,464 bytes free (about 11.1 GiB).
The survey does not measure extension build disk growth, runtime, peak RSS,
or prove that 217 modules will compile. It retains no new `.olean` files.
The separate [`result-v2.json`](result-v2.json) survey agreed with the final
record except for HEAD and free space. The two endpoint statements and any
external equation/PDF binding retain their existing qualifications.
Separate [entry-point controls](refusal-controls.json) observed exit 1 for
optimized Python and for a non-isolated invocation; they do not exercise
source-mutation or dependency-shadow detection.

Before considering a build, freeze the 1,212 source files and imports into
an isolated snapshot; revalidate the base and select one coherent package
provider with companion and shadow guards; measure disk headroom; audit
actual dependency and Matrix compatibility; and review a fail-closed runner.
Do not overlay historical nine-variable objects solely because their source
names match. A fresh run prints JSON to stdout and includes current HEAD and
free-space observations, so its bytes may differ:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/nine-variable-current-base-source-survey/survey.py
```
