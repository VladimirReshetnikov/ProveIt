# Independent audit of failed conditional reference check

The post-hoc author record reports outer session **91135, exit 1**. The
retained dependency scan exited 0, but the compile exited **−6** after a
Lean `memory_exception` reporting excessive interpreter memory use. The
runner used `-M2800`; the monitor recorded **no stop reason**, so this was a
Lean resource exception, not a monitor timeout or sampled RSS-limit stop. Its
sampled peak session RSS was 2,940,055,552 bytes. The log does not establish
which declaration triggered the exception. No output object or conditional
static-reference theorem was produced, and the three requested axiom reports
were not obtained.

`check.py` verifies the exact reviewed source snapshot, runner pin, retained
state and both logs, the two direct compiled producer objects
`SharingTopology38` and `FreshModel106`, all 150 recorded pre-compile direct
guard slots and 1,066 overlay links. The unsuccessful run did not reach its
success-path post-compile guard or provider-survey checks. This review reran
the source/provider survey afterward and observed its point-in-time pass; that
is a separate later observation, not the runner's missing postflight.

The outer receipt is an author record, not a raw transcript or independently
observed historical exit. No Lean process was run by this review. Inherited
package/dynamic ancestry, between-observation changes and sampled resource
limits remain outside its scope.
