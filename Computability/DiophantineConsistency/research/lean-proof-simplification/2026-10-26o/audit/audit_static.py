#!/usr/bin/env python3
"""Portable static patch/source audit. No Lean compiler is invoked.

Run with --baseline /path/to/pinned/ProveIt-or-snapshot. Exact source SHA-256
values are always checked; Git HEAD is additionally checked when .git exists.
Inputs are read-only; patch
application occurs in a disposable temporary directory. JSON goes to stdout
unless --output explicitly requests a receipt. Checks remain active with -O.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

PIN = 'b310142330df89e48413c8fce62e7de223e1c7d5'
REL = Path('Computability/DiophantineConsistency/Lean/DiophantineConsistency')
# Frozen from the three source blobs reviewed at PIN, independent of a caller's
# snapshot manifest. A no-Git snapshot must match these exact source bytes.
SOURCE_SHA256 = {
    'CurrentCellCycle2011.lean': '874a68dc11255170f19dc1a5345e195f36379711f8af630b16dd6eb9fe77081d',
    'CurrentSouthShift2011.lean': '256403c28ff13e2fb8585597a1931c1be8703f6726daaf3c5509cfbff5f8cf8d',
    'WangTiles942Boundary.lean': 'efda0078ffa174d2d9905cbd3431479a94679479742bbf9ff5856d132b06313c',
}
CHOICES = (
    ('CurrentCellCycle2011.lean', 'cyclic/candidates/CurrentCellCycle2011.lean',
     'cyclic/patches/CurrentCellCycle2011.lean.patch'),
    ('CurrentSouthShift2011.lean', 'cyclic/candidates/CurrentSouthShift2011.lean',
     'cyclic/patches/CurrentSouthShift2011.lean.patch'),
    ('WangTiles942Boundary.lean', 'wang/proposals/WangTiles942Boundary.proposed.lean',
     'wang/proposals/boundary_fibers.patch'),
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def run(*args, cwd=None):
    return subprocess.run(args, cwd=cwd, capture_output=True, check=False)


def signatures(source):
    # A deliberately limited TEXTUAL check for these files, not a Lean parser.
    # The inspected declaration headers contain no := default arguments.
    pattern = (r'^(?:@\[[^\n]*\]\s*)?(?:(?:private|noncomputable)\s+)?'
               r'(?:theorem|def|abbrev|instance)\s+([^\s(:]+)')
    result = {}
    for match in re.finditer(pattern, source, re.M):
        end = source.find(':=', match.end())
        require(end >= 0, 'Declaration terminator missing in textual scan')
        require(match.group(1) not in result, 'Duplicate textual declaration name')
        result[match.group(1)] = source[match.start():end].strip()
    return result


def apply_patch(stage, patch, label):
    result = run('git', '--no-optional-locks', 'apply', str(patch), cwd=stage)
    require(result.returncode == 0, 'Patch application failed: ' + label)
    return {'returncode': result.returncode, 'temporary_staging': True}


def audit(baseline, packet):
    # A packet deliberately need not include Git metadata or the full checkout.
    # Detect metadata at this baseline root, not in an unrelated ancestor.
    git_baseline = (baseline / '.git').exists()
    if git_baseline:
        head = run('git', '--no-optional-locks', 'rev-parse', 'HEAD', cwd=baseline)
        require(head.returncode == 0, 'Baseline .git is not a readable checkout')
        require(head.stdout.decode().strip() == PIN, 'Baseline HEAD does not equal required pin')
    records = []
    with tempfile.TemporaryDirectory(prefix='lean-static-audit-') as directory:
        stage = Path(directory)
        (stage / REL).mkdir(parents=True)
        for name, candidate_name, patch_name in CHOICES:
            source = baseline / REL / name
            candidate, patch = packet / candidate_name, packet / patch_name
            old_bytes, new_bytes = source.read_bytes(), candidate.read_bytes()
            require(sha(old_bytes) == SOURCE_SHA256[name],
                    'Baseline file differs from pinned source SHA-256: ' + name)
            if git_baseline:
                committed = run('git', '--no-optional-locks', 'show',
                                'HEAD:' + (REL / name).as_posix(), cwd=baseline)
                require(committed.returncode == 0 and committed.stdout == old_bytes,
                        'Baseline file differs from pinned Git blob: ' + name)
            old, new = old_bytes.decode(), new_bytes.decode()
            before, after = signatures(old), signatures(new)
            unchanged = all(after.get(n) == signature for n, signature in before.items())
            require(unchanged, 'Original declaration signature changed: ' + name)
            no_placeholders = not bool(re.search(r'\b(sorry|admit|axiom)\b', new))
            require(no_placeholders, 'Placeholder or axiom token found: ' + name)
            (stage / REL / name).write_bytes(old_bytes)
            application = apply_patch(stage, patch, patch_name)
            require((stage / REL / name).read_bytes() == new_bytes,
                    'Applied patch differs from candidate: ' + name)
            whitespace = run('git', '--no-optional-locks', 'diff', '--no-index', '--check',
                             str(source), str(candidate))
            require(whitespace.returncode in (0, 1) and not whitespace.stdout
                    and not whitespace.stderr, 'Whitespace check failed: ' + name)
            records.append({
                'file': (REL / name).as_posix(),
                'candidate': candidate_name, 'patch': patch_name,
                'source_sha256': sha(old_bytes), 'candidate_sha256': sha(new_bytes),
                'patch_sha256': sha(patch.read_bytes()), 'source_matches_pinned_sha256': True,
                'source_git_blob_checked': git_baseline,
                'all_original_declaration_signatures_identical': unchanged,
                'added_declarations': sorted(set(after) - set(before)),
                'removed_declarations': sorted(set(before) - set(after)),
                'patch_applies_to_exact_candidate': True, 'patch_application': application,
                'whitespace_check_passed': True,
                'source_nonblank_lines': sum(bool(line.strip()) for line in old.splitlines()),
                'candidate_nonblank_lines': sum(bool(line.strip()) for line in new.splitlines()),
                'source_physical_lines': len(old.splitlines()),
                'candidate_physical_lines': len(new.splitlines()),
                'source_bytes': len(old_bytes), 'candidate_bytes': len(new_bytes),
                'no_sorry_admit_axiom_tokens': no_placeholders,
            })
        optional_patch_name = 'occupation/patches/selector-binding-coherence.patch'
        optional_patch = packet / optional_patch_name
        optional_application = apply_patch(stage, optional_patch, optional_patch_name)
        implementation = (packet / 'occupation/candidate/SelectorBindingCoherence.lean').read_bytes()
        tests = (packet / 'occupation/tests/SelectorBindingCoherenceChecks.lean').read_bytes()
        expected_tests = tests.replace(b'import SelectorBindingCoherence\n',
                                      b'import DiophantineConsistency.SelectorBindingCoherence\n', 1)
        require((stage / REL / 'SelectorBindingCoherence.lean').read_bytes() == implementation,
                'Optional applied implementation differs from candidate')
        require((stage / REL / 'SelectorBindingCoherenceChecks.lean').read_bytes() == expected_tests,
                'Optional applied checks differ beyond intended import qualification')
        optional = {
            'patch': optional_patch_name, 'patch_sha256': sha(optional_patch.read_bytes()),
            'patch_application': optional_application,
            'candidate_sha256': sha(implementation), 'standalone_checks_sha256': sha(tests),
            'patched_checks_sha256': sha(expected_tests), 'patched_candidate_identical': True,
            'checks_difference': 'Only first-line import is qualified for repository placement.',
            'existing_declarations_changed': 0, 'current_source_saving_claimed': False,
        }
    return {
        'pin': PIN,
        'baseline_verification': {
            'exact_pinned_source_sha256_always_checked': True,
            'source_files_checked': len(SOURCE_SHA256),
            'git_metadata_present': git_baseline,
            'git_head_checked': git_baseline,
            'snapshot_scope': 'Only the three edited source files are authenticated here; this is not a full repository inventory check.',
        },
        'status': 'STATIC SOURCE AND PATCH CHECKS ONLY; NO LEAN ELABORATION OR KERNEL CHECK',
        'signature_check_scope': 'Textual scan of inspected declaration forms; not a Lean parser.',
        'input_files_modified': False, 'temporary_staging_cleaned': True,
        'records': records, 'optional_selector_binding_patch': optional,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', required=True, type=Path,
                        help='Pinned source snapshot, or checkout with matching HEAD; exact source hashes are always required')
    parser.add_argument('--packet-root', type=Path, default=Path(__file__).resolve().parents[1],
                        help='Directory containing cyclic/, wang/ and occupation/')
    parser.add_argument('--output', type=Path, help='Explicit receipt path; default is stdout only')
    args = parser.parse_args()
    try:
        result = audit(args.baseline.resolve(), args.packet_root.resolve())
        encoded = json.dumps(result, indent=2) + '\n'
        if args.output is not None:
            args.output.write_text(encoded)
        else:
            print(encoded, end='')
    except (OSError, ValueError) as error:
        # Paths are intentionally omitted from successful receipts.
        parser.exit(1, 'Static audit failed: ' + str(error) + '\n')


if __name__ == '__main__':
    main()
