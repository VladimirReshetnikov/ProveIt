#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "$script_dir/../.." && pwd)"
foundation_root="$repo_root/lib/FormalizedFormalLogic-Foundation"
mapping_file="$script_dir/ported.tsv"

if [[ ! -d "$foundation_root/Foundation" ]]; then
  echo "Foundation submodule is not initialized: $foundation_root" >&2
  exit 1
fi

declare -A mapped_status=()
declare -A mapped_artifact=()
declare -A mapped_notes=()

while IFS=$'\t' read -r source status artifact notes; do
  [[ "$source" == "source" ]] && continue
  [[ -z "$source" ]] && continue
  case "$status" in
    ported|partial) ;;
    *) echo "Invalid mapped status '$status' for $source" >&2; exit 1 ;;
  esac
  if [[ -n "${mapped_status[$source]+present}" ]]; then
    echo "Duplicate coverage mapping: $source" >&2
    exit 1
  fi
  if [[ ! -f "$foundation_root/$source" ]]; then
    echo "Mapped Foundation source does not exist: $source" >&2
    exit 1
  fi
  IFS=';' read -r -a artifact_paths <<< "$artifact"
  if [[ ${#artifact_paths[@]} -eq 0 ]]; then
    echo "Coverage mapping has no Coq artifact: $source" >&2
    exit 1
  fi
  for artifact_path in "${artifact_paths[@]}"; do
    if [[ -z "$artifact_path" || ! -f "$repo_root/$artifact_path" ]]; then
      echo "Mapped Coq artifact does not exist: $artifact_path" >&2
      exit 1
    fi
  done
  mapped_status["$source"]="$status"
  mapped_artifact["$source"]="$artifact"
  mapped_notes["$source"]="$notes"
done < "$mapping_file"

mapfile -t sources < <(
  find "$foundation_root/Foundation" -type f -name '*.lean' -printf 'Foundation/%P\n' |
    LC_ALL=C sort
)

declare -A counts=([ported]=0 [partial]=0 [unported]=0)
printf 'source\tstatus\tcoq_artifact\tnotes\n'
for source in "${sources[@]}"; do
  status="${mapped_status[$source]:-unported}"
  artifact="${mapped_artifact[$source]:-}"
  notes="${mapped_notes[$source]:-}"
  counts["$status"]=$((counts["$status"] + 1))
  printf '%s\t%s\t%s\t%s\n' "$source" "$status" "$artifact" "$notes"
done

printf 'summary\tmodules=%d\tported=%d\tpartial=%d\tunported=%d\n' \
  "${#sources[@]}" "${counts[ported]}" "${counts[partial]}" \
  "${counts[unported]}" >&2
