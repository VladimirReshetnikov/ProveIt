#!/usr/bin/env bash
set -euo pipefail

here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
out=$(cd -- "${1:?provider overlay required}" && pwd)

# Old replay objects still define the syntax. Preserve those owners and add
# the imports expected by current bridge sources and objects.
if ! lean -j1 --run "$here/BridgeSyntaxProviders.lean" >"$out/syntax-providers.txt" 2>"$out/syntax-providers.log"; then
  cat "$out/syntax-providers.log" "$out/syntax-providers.txt"
  exit 1
fi
while read -r syntax provider; do
  shim="$out/compatibility/DiophantineConsistency/$syntax.lean"
  mkdir -p "$(dirname -- "$shim")"
  printf 'import DiophantineConsistency.%s\n' "$provider" >"$shim"
  artifact="$out/DiophantineConsistency/$syntax.olean"
  rm -f -- "$artifact" "$artifact.private" "$artifact.server"
  if ! lean -j1 -R "$out/compatibility" -o "$artifact" "$shim" >>"$out/syntax-providers.log" 2>&1; then
    cat "$out/syntax-providers.log"
    exit 1
  fi
done <"$out/syntax-providers.txt"
