# Attribution and licensing boundaries

The new report, new Lean modules, new search and verification code, and new
notes are supplied for incorporation into ProveIt under the MIT No Attribution
terms in `LICENSE`.

Unmodified ProveIt source imports retain the ProveIt contributors' attribution
and MIT No Attribution license in `vendor/LICENSE.ProveIt`. Their exact original
paths, revision and hashes are recorded in `source_manifest.json`.

The literal public253 machine is prior work attributed to mira-emmy, derived
from Mira-Cult's machine, Jeff Ketchersid's verification and Andrew James Wade's
framework. The one-row variant does not confer authorship of the baseline on
this report's contributors.

Selected upstream busy-beaver source inputs are retained for precise research
review and reproduction. No upstream-wide license is declared in the inspected
tree. This bundle does not relicense those files. The source paths and pins are
explicit, and the upstream README and ProveIt's existing import/provenance notice
are retained. `LICENSE.wade` applies to the specified Wade generator sources;
it is not represented as a blanket license for every upstream file. No sources
from the separately licensed busycoq or undecidability libraries are included.

The archive excludes repository metadata, compiler binaries, generated Lean
object files, and irrelevant intermediate search caches.
