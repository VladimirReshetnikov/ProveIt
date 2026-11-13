# Resource-guarded four-helper completion retry

This packet prepares one retry of the exact source from
[the earlier four-helper attempt](../thirteen-current2011-complete-factored-attempt02/README.md),
whose Lean compilation hit its interpreter limit. Its source hash remains
`cf7dcf8e16be4772ac39c49068425668044832303e5972e501d11c7d8536dfb1`.
The theorem statements and helper providers are unchanged. The retry has now passed as recorded below.

The prepared runner uses Lean `-M4000`, one worker and low priority. Its
monitor samples the owned session every 0.1 seconds and stops on 5 GiB total
session RSS, 10 GiB available host memory, 180 seconds, an unexpected
session descendant, or monitoring errors. It opens `/proc/<pid>` first and
uses that stable process-directory handle for signals; it does not use
numeric `kill` or `killpg`. It keeps the direct leader unreaped while
observing and cleaning the session, and records the samples' peak RSS and
minimum host memory, exit, stop reason, descendants and errors. Both `--deps`
and compilation are monitored. The session sum is conservative for one
process group, but sampling can miss short spikes or transient/escaped
children. `/proc` enumeration is non-atomic; forced supervisor termination,
failed signals, host failure and uninterruptible processes can defeat cleanup.
This is not a kernel-enforced memory cgroup and does not establish complete
package-transitive or dynamic import ancestry.

[Pure synthetic controls](controls-result.json) observed normal completion,
timeout, host floor, RSS limit, unexpected descendant and an outside-session
bystander. They are not a Lean run and do not prove OS lifecycle properties.
The monitor SHA-256 is
`d6d32747a34269702abd603d600a848266720aa06c0b91653942f316cd6dc1ad`;
the runner SHA-256 is
`347a22ac96f05a51a2e1a7ef293fbbec7d40df784a818428504f5ee6f3a37b0c`.

Actual outer session 33054 exited 0 with `PASS factored carrier model and
bridge`; dependency and compile exits are both 0, and the compile log is
empty. The retained [state](attempt03/state.json) SHA-256 is
`c0963c19b50b76cc2e43655659ae259baeec6d0154ee3381e843ec317dc35466`;
the output object SHA-256 is
`197fb6ecbf39f9535ceb8ccafba506a2aa986e3db49f29ac5d8b8e1e3ba0ced9`.
Compilation ran 17.663 seconds over 168 samples, with peak sampled session
RSS 3,067,756,544 bytes and minimum sampled host available memory
18,687,082,496 bytes. No stop, sampled descendant, or monitor error was
recorded. The source checks the 13/69 completion, same-no-zero bridge,
native and standard iPRA mapped-refutation equivalence. It does not yet
check the adapted 13/70 or 13/71 forms or final axiom-report client. The
direct guards and source/provider links describe the captured same-base
ancestry; this is not an independent clean rebuild or full dynamic import
trace.
