#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
unzip -tq dependency/ProveIt_A007716_Asymptotics_and_Inverses.zip
for check in check_graphs check_kernel_and_giant check_cycles; do
 cp "code/$check.json" "/tmp/$check.expected.$$.json"
 python3 "code/$check.py"
 cmp "code/$check.json" "/tmp/$check.expected.$$.json"
 rm "/tmp/$check.expected.$$.json"
done
bash build_local.sh
if grep -Eq 'Overfull|Underfull|undefined references' build/pass-2.stdout; then
 echo 'Unexpected LaTeX layout/reference warning' >&2
 exit 1
fi
printf '\nPASS: exact outputs reproduced and PDF rebuilt\n'
