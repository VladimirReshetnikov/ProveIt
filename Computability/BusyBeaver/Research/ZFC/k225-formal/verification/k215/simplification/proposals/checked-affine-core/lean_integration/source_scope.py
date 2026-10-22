"""Bind a completed Lean closure to pinned sources and explicit proof-only edits."""
from pathlib import Path
import hashlib
import json
import re


def apply_single_file_patch(original, patch):
    """Apply this packet's ordinary unified single-file patch, checking context."""
    old = original.splitlines(keepends=True)
    diff = patch.splitlines(keepends=True)
    assert len(diff) >= 3 and diff[0].startswith('--- a/') and diff[1].startswith('+++ b/')
    assert diff[0][6:].strip() == diff[1][6:].strip()
    result, position, i = [], 0, 2
    while i < len(diff):
        match = re.fullmatch(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@.*\n?', diff[i])
        assert match, ('Unexpected patch line', diff[i])
        start, count, new_start, new_count = [int(x) if x is not None else 1 for x in match.groups()]
        assert position <= start - 1 <= len(old)
        result.extend(old[position:start - 1]); position = start - 1
        assert len(result) == new_start - 1
        consumed = produced = 0; i += 1
        while i < len(diff) and not diff[i].startswith('@@ '):
            line = diff[i]; assert line and line[0] in ' +-'
            if line[0] in ' -':
                assert position < len(old) and old[position] == line[1:]
                position += 1; consumed += 1
            if line[0] in ' +':
                result.append(line[1:]); produced += 1
            i += 1
        assert consumed == count and produced == new_count
    result.extend(old[position:])
    return ''.join(result)


def check_calculus_overlay(packet_dir, source_repo):
    packet_dir, source_repo = Path(packet_dir), Path(source_repo)
    relative = 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSeedModel222.lean'
    original = source_repo / relative
    patch = packet_dir / 'calculus/REMOVE_THREE_INDUCTIONS.patch'
    overlay = packet_dir / 'calculus/BusyBeaver/ZFC/KSeedModel222.lean'
    sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
    expected = next(row['sha256'] for row in json.loads((packet_dir / 'base_sources.json').read_text())
                    if row['path'] == relative)
    assert sha(original) == expected
    assert apply_single_file_patch(original.read_text(), patch.read_text()).encode() == overlay.read_bytes()
    return {'original_sha256': sha(original), 'patch_sha256': sha(patch),
            'overlay_sha256': sha(overlay)}


def check_source_scope(base_build, packet_dir):
    base_build, packet_dir = Path(base_build), Path(packet_dir)
    original = json.loads((packet_dir / 'base_sources.json').read_text())
    changes = json.loads((packet_dir / 'batching/sources.json').read_text())
    by_module = {row['module']: row for row in changes}
    assert len(changes) == len(by_module) == 4
    inventory = json.loads((base_build / 'inventory.json').read_text())['modules']
    assert len(inventory) == 184
    unchanged = 0
    seen = set()
    for row in inventory:
        matches = [x for x in original
                   if row['source'].endswith('/' + x['path'])]
        assert len(matches) == 1, row['module']
        pinned = matches[0]
        if row['module'] in by_module:
            change = by_module[row['module']]
            assert pinned['path'] == change['repository_path']
            assert pinned['sha256'] == change['original_sha256']
            assert row['source_sha256'] == change['batched_sha256']
            assert row['imports'] == change['imports']
            seen.add(row['module'])
        else:
            assert row['source_sha256'] == pinned['sha256'], row['module']
            unchanged += 1
    assert seen == set(by_module) and unchanged == 180
    completed = json.loads((base_build / 'completed.json').read_text())
    audit_bindings = {}
    for name in ('EndpointAudit215', 'K215Audit'):
        row = completed[name]
        matches = [x for x in original
                   if row['source'].endswith('/' + x['path'])]
        assert len(matches) == 1, name
        assert row['source_sha256'] == matches[0]['sha256'], name
        audit_bindings[name] = row['source_sha256']
    return {
        'source_pin': '56e487ce8fa4cf63ad169ffe0cd2944e9fc62dd3',
        'project_modules': 184,
        'byte_identical_project_modules': unchanged,
        'proof_only_batched_modules': len(changes),
        'byte_identical_typed_audits': audit_bindings,
        'changes': changes,
        'scope': ('The exact current machine, program, certificate data, imports, '
                  'and public endpoint statements are retained. Four proof bodies '
                  'use the existing quarter-batching technique; this is not a '
                  'byte-identical replay of all 184 original modules.'),
    }
