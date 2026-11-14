# Return from marking into the PA194 controller

`PA194ControllerReturn.modelReturnToControl18` proves a concrete segment of
the literal PA194 table in every candidate classical-PRA model. Starting in
either marking-exit state, dense 15 or 17, it crosses an arbitrary model-length
run of ones followed by two zero cells, and reaches dense state 18 after
`n + 3` physical steps. Both tape halves and `n` may be nonstandard. The
input shape `ones(n, 4*l)` explicitly supplies the two zero cells following
the run; `2*t+1` supplies the one currently under the head. The theorem
preserves their exact encoded effect on both tape halves.

`PA194ControllerReturnSentence.nativeIPRA` internalizes this equation as a
universally closed native-iPRA sentence for either exit control, via the
existing equality transfer. The table row is checked against the pinned
dense machine; native names and source-program correctness are not assumed.

This is one controller segment after marking. It does not identify the
source program frame, prove all intervening controller paths, reach the
increment entry, or establish either consistency implication.

Run `check-controller-return.sh` with the same pinned iPRA and Foundation
overlays as `check-mark-all.sh`. It freshly rebuilds those prerequisites in
a private temporary overlay, checks the new files, and rejects `sorryAx` in
printed theorem dependencies. For example:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-controller-return.sh
```
