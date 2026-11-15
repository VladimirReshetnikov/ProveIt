#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
"${GAMMA_LEAN_BIN:-lean}" GammaIPRA.lean
