# Audit of the eight negation peepholes

The negation197 source makes eight copies of the same local change. The
change is correct when source register 7 is zero on entry; it is **not** an
identity on arbitrary source states. The [parent experiment](../README.md)
separately tracks the entry invariant and the MP-success rewrite. This note
checks the peephole against the original PA196 source, independently of the
binary machine and without asserting the full PA consistency equivalence.

Write `T = r1`, `W = r2`, `S = r6`, and `R = r7`. The original and replacement
blocks have 47 and 20 source sites, respectively. Their first three sites are
identical: drain `T` into `S`, arriving with `T=0`, `S=s`, `W=w`. Assume
`R=0` at entry, so it remains zero. The following describes the removed
27-site detour:

1. Drain `W` into `T`. The original pairing loop starts with
   `(T,S,R)=(w,s,0)` and preserves `R + triangle(T+S) + T`. In its ordinary
   iteration, `T` decreases by one and both `S` and `R` increase by one.
   When `T=0` and `S>0`, it increments `R`, decrements `S`, and drains the
   remainder of `S` into `T`; the same invariant is preserved. The loop
   terminates as the diagonal sum decreases at each reset. It leaves `R =
   triangle(s+w)+w = pair(s,w)`, `T=S=0`; the next transfer moves that code
   into `W`, and `T` is incremented to 1.
2. The following loop consumes `W` one unit at a time, updating `(S,R)` by
   `(a,b) -> (a-1,b+1)` if `a>0`, and `(0,b) -> (b+1,0)` otherwise. This is
   exactly the Cantor decoder's successor operation, starting at `(0,0)`.
   After `pair(s,w)` iterations, `(S,R)=(s,w)` by `decode(pair(s,w))=(s,w)`.
   Draining `R` into `W` leaves `(T,W,S,R)=(1,w,s,0)`.

The replacement skips pairing and decoding and directly increments `T`,
reaching the same `(1,w,s,0)` state. All other registers are untouched. The
remaining 16 source instructions and their local control flow are identical,
so both blocks terminate with the same complete register file and continue at
the corresponding outer site. In fact the shared suffix pairs `s` with 1 and
moves four copies into `T`: it returns `T = 4 * pair(s,1)`, `W = w`, and
`S = R = 0`. When the incoming `S` is zero, this is the numeric negation
constructor applied to the incoming `T`. This is an ordinary mathematical argument;
it has not been arithmetized as a PA theorem or connected to a literal tape
run here.

The zero-scratch premise matters. For the first copy, entering with all
registers zero except `r7=1`, the original exits after 67 steps with `r1=16`;
the replacement exits after 32 steps with `r1=12`. Thus treating the change
as an unconditional local identity would be incorrect.

## Reproduction

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search/negation-mp197/local-audit/replay.py > /tmp/negation-local-audit.json
```

The output matches [receipt.json](receipt.json). The script pins the original
PA196 source and incoming archive, reconstructs both source graphs using two
independent resolvers, and verifies all eight local CFG shapes, their lack of
external interior entries, their exits, and the identical suffix. It checks
all 3,436 outside old sites against the relocated new graph, then runs 512
finite zero-scratch controls and the nonzero-scratch counterexample. The finite
controls are checks on the proof's interpretation; they do not replace the
arbitrary-value argument above. The code uses explicit checks and can also run
under `python3 -O`.
