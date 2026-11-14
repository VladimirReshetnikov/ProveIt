# PA195 entry-frame decrement contracts

`PA195Site25.lean` checks two concrete symbolic executions on the exact
unfolded 202-control parent. The start frame has source path `100000` and
corresponds in the archive to site 25, a decrement of logical register 8,
represented as physical register 1. The two targets are the zero branch
(path `1000100`) and positive branch (path `100001`, with the expected
register-file decrement and extra gap cell). Lean evaluates the symbolic
executions against the actual parent table and proves positive physical
reachability to each specified target for every valid register file and gap.

The explicit correspondence between these frame paths and the archive's
`source.json` is documented here; a kernel-checked binding to the whole
3,700-site source graph remains to be developed. No source-to-machine theorem
for all sites, PRA/iPRA result, or consistency equivalence is claimed.

Run from the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa195-site25/check.sh
```

The script checks the upstream source hashes, rebuilds all imported M6
modules and the parent table in a private `/dev/shm` directory, then checks
the two symbolic executions and semantic consequences.
