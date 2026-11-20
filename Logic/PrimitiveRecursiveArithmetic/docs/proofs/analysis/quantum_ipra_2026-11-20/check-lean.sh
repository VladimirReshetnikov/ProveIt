#!/bin/sh
set -eu
if [ "$#" -ne 1 ]; then
    echo 'Usage: sh check-lean.sh /path/to/ProveIt' >&2
    exit 2
fi
packet_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd -- "$1"
lake build +IPRADerivations.Core.BoundedSums +IPRADerivations.Core.Powers
for module in BornStability QuantumIdentities QuantumNames ResolventTail; do
    lake env lean "$packet_dir/lean/$module.lean"
done
