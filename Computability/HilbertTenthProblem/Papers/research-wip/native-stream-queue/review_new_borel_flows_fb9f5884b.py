#!/usr/bin/env python3
"""Fresh metadata-only intake checker; never loads or runs archive programs.

Read claims in this receipt describe the accompanying human review. The
checker authenticates the bytes/spans, not the infinite mathematical proofs.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import zipfile

COMMIT = 'fb9f5884b0a53eb2a950bc564b9a0aa9bed65df8'
ARCHIVE = 'docs/incoming/Borel_Flows_Glazer_ProveIt.zip'
ARCHIVE_SHA = '78af94354498216718974f9c4974c0efeffda16aef19e9d49896459db429f135'
PREFIX = 'Borel_Flows_Glazer_ProveIt/'
PREVIOUS_COMMIT = '62846e17a78ee588f0d3686c966c1cde9a0f1bb9'
PREVIOUS_ARCHIVE = 'docs/incoming/Borel_Conjugacy_Divisibility_Threshold.zip'
BCH_COMMIT = 'c39974f12a45c8795575ab222f3b84b2901c394f'
BCH_PATH = 'Algebra/BakerCampbellHausdorff/Lean/BCH/Formal/Trunc.lean'
HOST = 'Algebra/SurrealNumbers/docs/foundations-and-computation/polish-models-of-omnific-arithmetic/'
EXPECTED = {
    'CLAIM_LEDGER.md': (5284, 63, 'c76dc4f65481048a76c31e98f5e2765e55f861046dc235c9afa685d9e289d524'),
    'README.md': (4130, 86, '6981fb4c0606ca1391c927fa75bab7a4db7eb242762cb1f3a3662f880497a333'),
    'SHA256SUMS': (642, 8, '754644fc5181765139955836ede3fe357d617db18b491caf638b99b344dc5c5e'),
    'SOURCES.md': (3993, 87, '11a466af495501f9515d82e2c713d41f1804eb339de716679a8ab8d14d30e53d'),
    'borel_flows.pdf': (328335, None, '00b34374245781b4d8cd629e982b1e1a9c26a149378d4af5e16c557f6ae2162f'),
    'borel_flows.tex': (80386, 1724, '7cbb441d8c505aca0f707a77588c31b2066db93412667347ff9ccb0d6a8a4c86'),
    'build.sh': (363, 11, '45e849b541f093e5835054963849dc862a4d643d4037e2cc48bd2e27a1e6edca'),
    'verification_results.json': (1041, 63, '44deb683c665143ba7f8740d210e27b7d2b8d1bb348fa00683345b417cbbbc9c'),
    'verify.py': (8648, 270, '0da89dccd8578f85c9fff37e98d6e0d85a73e2a9db912e672d04c8f2ad69f678'),
}

def need(condition, message):
    if not condition:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args])

def span(data, start, end):
    lines = data.splitlines(keepends=True)
    need(1 <= start <= end <= len(lines), 'read span outside file')
    return {'start_line': start, 'end_line': end,
            'sha256': sha(b''.join(lines[start-1:end])),
            'convention': 'original bytes, splitlines(keepends=True), inclusive'}

def git_read(root, commit, path, spans):
    data = git(root, 'show', commit + ':' + path)
    return {'commit': commit, 'path': path,
            'blob': git(root, 'rev-parse', commit + ':' + path).decode().strip(),
            'bytes': len(data), 'sha256': sha(data),
            'line_count': len(data.splitlines()),
            'reads': [span(data, a, b) for a, b in spans]}

def make(root):
    need(git(root, 'rev-parse', COMMIT).decode().strip() == COMMIT, 'commit')
    raw = git(root, 'show', COMMIT + ':' + ARCHIVE)
    need(len(raw) == 362023 and sha(raw) == ARCHIVE_SHA, 'archive pin')
    with zipfile.ZipFile(io.BytesIO(raw)) as z:
        infos = [i for i in z.infolist() if not i.is_dir()]
        need(len(infos) == len(EXPECTED), 'member count')
        need({i.filename for i in infos} == {PREFIX + n for n in EXPECTED}, 'paths')
        contents = {i.filename: z.read(i.filename) for i in infos}
        members = []
        for i in sorted(infos, key=lambda item: item.filename):
            name = i.filename[len(PREFIX):]
            data = contents[i.filename]
            size, line_count, digest = EXPECTED[name]
            need(len(data) == size and sha(data) == digest, 'member pin ' + name)
            entry = {'path': i.filename, 'bytes': size, 'sha256': digest,
                     'compressed_bytes': i.compress_size, 'compression_method': i.compress_type,
                     'crc32': f'{i.CRC:08x}', 'external_attributes': i.external_attr,
                     'coverage': 'hash only; PDF not rendered/read' if line_count is None
                                 else 'complete text read; supplied code inert only'}
            if line_count is not None:
                need(len(data.splitlines()) == line_count, 'line count ' + name)
                entry.update(line_count=line_count, reads=[span(data, 1, line_count)])
            members.append(entry)
        manifest = []
        for line in contents[PREFIX + 'SHA256SUMS'].decode().splitlines():
            digest, name = line.split(None, 1)
            need(sha(contents[PREFIX + name]) == digest, 'shipped checksum ' + name)
            manifest.append(name)
        need(set(manifest) == set(EXPECTED) - {'SHA256SUMS'}, 'manifest coverage')
    tex = contents[PREFIX + 'borel_flows.tex']
    labels = re.findall(rb'\\label(?:\[[^\]]*\])?\{([^}]+)\}', tex)
    references = re.findall(rb'\\(?:[cC]ref|eqref|ref|autoref)\{([^}]+)\}', tex)
    reference_labels = {v.strip() for group in references for v in group.split(b',')}
    need(len(set(labels)) == len(labels), 'duplicate labels')
    need(reference_labels <= set(labels), 'unresolved simple reference')
    need(b'Theorem~\nef{thm:timeoneexact}' in tex, 'retained malformed reference')
    need(b'\\label{thm:timeoneexact}' in tex, 'proper later theorem label')
    saved = json.loads(contents[PREFIX + 'verification_results.json'])
    need(sum(saved['stage_checks'].values()) == saved['checks'] == 5372, 'saved totals')
    need(saved['time_one_pivot_indices'] == [0] + list(range(1, 80, 2)), 'saved pivots')
    old_raw = git(root, 'show', PREVIOUS_COMMIT + ':' + PREVIOUS_ARCHIVE)
    with zipfile.ZipFile(io.BytesIO(old_raw)) as z:
        old_hashes = {sha(z.read(i.filename)) for i in z.infolist() if not i.is_dir()}
    common_bytes = [n for n, data in contents.items() if sha(data) in old_hashes]
    contexts = [
        git_read(root, COMMIT, 'docs/incoming/README.md', [(426, 438)]),
        git_read(root, COMMIT, 'Algebra/SurrealNumbers/AGENTS.md', [(1, 182)]),
        git_read(root, COMMIT, HOST + 'README.md', [(18, 60)]),
        git_read(root, COMMIT, HOST + 'article.tex', [(36434, 36476)]),
    ]
    bch_data = git(root, 'show', BCH_COMMIT + ':' + BCH_PATH)
    bch = git_read(root, BCH_COMMIT, BCH_PATH, [(1, len(bch_data.splitlines()))])
    need(bch['blob'] == '5f238ed2f05b54e940e51f974465768c0dc23ba7', 'BCH blob')
    need(git(root, 'rev-parse', BCH_COMMIT + '^{tree}').decode().strip() ==
         'dbbe29a67da59205e50a264c58a9bc3731d761ec', 'BCH tree')
    contexts.append(bch)
    return {
        'status': 'PASS: byte/provenance checks only; proof review is in companion MD',
        'reviewer_source_sha256': sha(Path(__file__).read_bytes()),
        'archive': {'commit': COMMIT,
                    'parent': git(root, 'rev-parse', COMMIT + '^').decode().strip(),
                    'path': ARCHIVE,
                    'blob': git(root, 'rev-parse', COMMIT + ':' + ARCHIVE).decode().strip(),
                    'bytes': len(raw), 'sha256': sha(raw), 'regular_members': members,
                    'verified_manifest_entries': len(manifest)},
        'source_label_census': {'labels': len(labels), 'unique_labels': len(set(labels)),
                               'simple_reference_commands': len(references),
                               'distinct_referenced_labels': len(reference_labels),
                               'unresolved_simple_labels': [],
                               'finding': {'kind': 'malformed literal cross-reference',
                                           'span': span(tex, 167, 168),
                                           'correct_label': 'thm:timeoneexact',
                                           'correct_label_line': 1127}},
        'saved_evidence': {'status_reported_by_author': saved['status'],
                           'reported_checks': saved['checks'],
                           'reported_stage_checks': saved['stage_checks'],
                           'replayed': False,
                           'scope': 'Only saved count/pivot internal consistency checked.'},
        'comparison': {'prior_archive_commit': PREVIOUS_COMMIT,
                       'prior_archive_path': PREVIOUS_ARCHIVE,
                       'prior_archive_sha256': sha(old_raw),
                       'byte_identical_regular_members': common_bytes,
                       'mathematical_overlap': 'Rank-one divisible setting overlaps; domains differ.'},
        'context_reads': contexts,
        'scope_exclusions': ['No supplied/archived/frozen program executed or imported.',
                             'No PDF rendering, LaTeX/Lean build, external-source or priority audit.',
                             'No mathematical proof follows from the saved finite tests.',
                             'No paid ordinary-integer compiler or operation bound is supplied.'],
    }

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--output', type=Path)
    mode.add_argument('--expect', type=Path)
    args = parser.parse_args()
    result = make(args.root)
    encoded = (json.dumps(result, indent=2, sort_keys=True) + '\n').encode()
    if args.output:
        with args.output.open('xb') as handle:
            handle.write(encoded)
    else:
        need(args.expect.read_bytes() == encoded, 'receipt replay differs')
    print('PASS: 9 archive members, 8 manifest checks; supplied programs inert.')

if __name__ == '__main__':
    main()
