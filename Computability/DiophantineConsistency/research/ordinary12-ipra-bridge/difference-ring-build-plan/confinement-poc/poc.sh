#!/bin/sh
# Tiny namespace/Lean confinement experiment; not a real rebuild sandbox.
set -eu
if [ "${1-}" != --inner ]; then
  exec unshare -Urnm "$0" --inner
fi
scratch=$(mktemp -d /tmp/ipra-confined-poc.XXXXXX)
cleanup() {
  rm -rf "$scratch/out" "$scratch/temp" "$scratch/src"
  umount "$scratch" 2>/dev/null || :
  rmdir "$scratch" 2>/dev/null || :
}
trap cleanup EXIT HUP INT TERM
mount -t tmpfs -o size=16m,nodev,nosuid tmpfs "$scratch"
mkdir "$scratch/out" "$scratch/temp" "$scratch/src"
printf 'theorem toy : (1 : Nat) = 1 := rfl\n' > "$scratch/src/Toy.lean"
bwrap --clearenv --ro-bind / / \
  --dev-bind /dev/null /dev/null --dev-bind /dev/zero /dev/zero \
  --dev-bind /dev/urandom /dev/urandom --dev-bind /dev/random /dev/random \
  --bind "$scratch" "$scratch" --setenv PATH /usr/bin:/bin \
  --setenv SCRATCH "$scratch" --setenv TMPDIR "$scratch/temp" -- /bin/sh -c '
    set -eu
    /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
      --root="$SCRATCH/src" "$SCRATCH/src/Toy.lean" -o "$SCRATCH/out/Toy.olean"
    test -s "$SCRATCH/out/Toy.olean"
    printf tmp > "$TMPDIR/probe"
    if touch /tmp/ipra-confined-poc-escape 2>/dev/null; then exit 4; fi
    if touch /dev/ipra-confined-poc-escape 2>/dev/null; then exit 5; fi
    sha256sum "$SCRATCH/out/Toy.olean"
    if err=$(dd if=/dev/zero of="$SCRATCH/out/overflow" bs=1048576 count=20 2>&1); then exit 6; fi
    case "$err" in *"No space left on device"*) ;; *) printf "%s\n" "$err"; exit 7 ;; esac
    df -B1 "$SCRATCH" | tail -1
    printf "PASS_CONFINED_LEAN_TOY output TMPDIR outside-tmp-dev-denied ENOSPC\n"
  '
