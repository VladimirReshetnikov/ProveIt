#!/usr/bin/env python3
"""Restore a fixed set of authenticated historical ZIPs into an external cache.
No archive is extracted or executed. Repository contents are never written.
"""
import argparse
import hashlib
import json
import subprocess
from pathlib import Path
REVISION = '55d248dc504cff215684773123b3b03a8b8ebbe3'
PLACEMENT_COMMITS = ['49dfa8fd6c7d178f4b4537e1c87a57831c3a5201',
 '2f58ab4e92dea865e0b25a43925970cf92e9e324']
PLACEMENT_COMMITS += ['bca6383e99506fb6cfba6da55a78e6b3c7211274',
 '7d2b1b2459cd9500a159ca36b4eadf7a183aae78']
PLACEMENT_MERGE = 'da879508944d2c170378200bac0e7c6e5d51e2be'
LATER_PLACEMENT_HEAD = '9cad538807bf89c6693a9555f671a1f80c21cd31'
INVENTORY = [{'path': 'docs/incoming/Two_Parallel_Conservative_Involutions_Package.zip', 'report': '26', 'reviewed_intake': True, 'bytes': 442422, 'sha256': '20a23b1ee22aed461942da4def6bade2bd55d777fce1fe49b6ff83248b7442e4', 'git_blob_sha1': '9d99d6ef9eeb30616e19a8dade96955868edcd18', 'relocated_by_cited_placements': True, 'permanent_reference': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/README.md', 'placement_note': 'Later batch82M2 placement; source prefix 26-parallel-involutions-'}, {'path': 'docs/incoming/Sparse_Parallel_Particle_Evaluation_Package.zip', 'report': '27', 'reviewed_intake': True, 'bytes': 2101210, 'sha256': '05c1cc14cc6005540e3de9749e0d8c0d5ab0f9225f80b0852a6149674d211df3', 'git_blob_sha1': 'be14011c780af17037b1abd598ec063dad1104fe', 'relocated_by_cited_placements': True, 'permanent_reference': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/README.md', 'placement_note': 'Later batch82M2 placement; source prefix 27-sparse-parallel-'}, {'path': 'docs/incoming/Canonical_Parallel_Quartic_Certificates_Package.zip', 'report': '28', 'reviewed_intake': True, 'bytes': 738326, 'sha256': 'bc78252b9d0e0a7d122be2c9adccfef8c0a810e20cbd06606a709a78846dc5de', 'git_blob_sha1': '8b402c6cdd1b1ebfc416ed72554765063aa3d9aa', 'relocated_by_cited_placements': True, 'permanent_reference': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/README.md', 'placement_note': 'Later batch82M2 placement; source prefix 28-parallel-quartic-'}, {'path': 'docs/incoming/Canonical_Histories_and_Infinite_Fibers_Package.zip', 'report': '22', 'reviewed_intake': True, 'bytes': 848126, 'sha256': '6abeadd97bb910dfc7330932d52fefd1dc14ef530489a7e11721dcf4381f8e5f', 'git_blob_sha1': 'cf48b5a6e1b3c56549f59c1e09db7ebcc0436c54', 'relocated_by_cited_placements': True, 'permanent_reference': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/README.md', 'placement_note': 'Later batch82M2 placement; source prefix 23-canonical-fibers-'}, {'path': 'docs/incoming/Entire_Native_Witness_Fiber_Package.zip', 'report': '25', 'reviewed_intake': True, 'bytes': 531631, 'sha256': 'c8821ab95a5c94730ee6634924e00d11ad9650ec76af89d7f73a48d3653fe3d6', 'git_blob_sha1': '35c5a9418e4209c2266d2c37cacdf8581aa9960a', 'relocated_by_cited_placements': True, 'permanent_reference': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/fixed-universal-polynomials/07-native-fiber-proofs-entire-fiber-THEOREM.md', 'placement_note': 'Part III, source07.'}, {'path': 'docs/incoming/Failure_of_Positive_Index_Restoration_Package.zip', 'report': '33', 'reviewed_intake': True, 'bytes': 703207, 'sha256': '78dfb46d6e5a620dc818a0cf9da497930c45c80e092d8054bb98508bc050a456', 'git_blob_sha1': 'a991587050054a28d7b722a6049b47760512f937', 'relocated_by_cited_placements': True, 'permanent_reference': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/fixed-universal-polynomials/10-index-restore-repro-evidence-FULL-SIGNED-COUNTEREXAMPLE.md', 'placement_note': 'Part IV, source10.'}, {'path': 'docs/incoming/Fixed_Universal_Grill_Polynomial_Package.zip', 'report': '23 original', 'reviewed_intake': True, 'bytes': 15390453, 'sha256': '467e2b4795fd484b73d94c6a006a84652fea772f1b0f870cac1a1f5d1445bf9b', 'git_blob_sha1': 'ac0fe4f8991ae474bc8ce6e265e1d39a6df6e517', 'relocated_by_cited_placements': True, 'permanent_reference': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/fixed-universal-polynomials/11-grill-poly-REVISION.md', 'placement_note': 'Superseded original ZIP was not placed; revision1 is the permanent base.'}, {'path': 'docs/incoming/Fixed_Universal_Grill_Polynomial_Package (1).zip', 'report': '23 revision1', 'reviewed_intake': True, 'bytes': 15508226, 'sha256': 'e7baac1f3cf2c519d40ffc336424ba28c4d44d81a0ec9ed8f0b1812a8ed00405', 'git_blob_sha1': 'c2f8001e9e74fea3da71baebda08501935a4e037', 'relocated_by_cited_placements': True, 'permanent_reference': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/fixed-universal-polynomials/11-grill-poly-README.md', 'placement_note': 'Part I, source11. Large generated files were not placed; the exact ZIP remains replay input.'}, {'path': 'docs/incoming/Native_Grill_Exact_Degree_Laws_Package.zip', 'report': '24', 'reviewed_intake': True, 'bytes': 552226, 'sha256': 'fd63543ab48425175fc36d145193686b347d2160fd735283cd92a22371354876', 'git_blob_sha1': '7b81c5d2cd72064f98cfc0908dfb61249f3c4dc8', 'relocated_by_cited_placements': True, 'permanent_reference': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/fixed-universal-polynomials/14-degree-laws-research-GENERAL_DEGREE_THEOREM.md', 'placement_note': 'Part II, source14.'}, {'path': 'docs/incoming/Universal_Matrix_Semigroup_and_Diophantine_Certificates_Package.zip', 'report': '32', 'reviewed_intake': True, 'bytes': 771940, 'sha256': 'b494c2b8e516d811cbecf305a748197af2a565882319a86586fec316c5ba8c47', 'git_blob_sha1': '4c7bf35a02277faf01c97211e12552127ea96aa6', 'relocated_by_cited_placements': True, 'permanent_reference': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/group-theoretic-substrates/08-matrix-semigroup-core-PROOF.md', 'placement_note': 'Part V, source08.'}, {'path': 'docs/incoming/Binary_Planar_Four_Particle_Shuttle_Package.zip', 'report': '31', 'reviewed_intake': True, 'bytes': 498429, 'sha256': '08020df876af26b1c8cfbf42aa2a79386375254f573f2e5079c07263689d7d98', 'git_blob_sha1': '9a821f5c3b8d6abc4bf97461b50bae2461f7a1ac', 'relocated_by_cited_placements': True, 'permanent_reference': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/21-planar-shuttle-PROOF.md', 'placement_note': 'Part VII, source21.'}, {'path': 'docs/incoming/Counterexample_Height_Expansions_and_Rotation_Discrepancy_Package.zip', 'report': '34', 'reviewed_intake': True, 'bytes': 591664, 'sha256': '7d108e8a2d8f77160b31e99758697d15d0eaf70d7ca6242d726d0d2fff24adee', 'git_blob_sha1': '02fe0b5d7c211d4d40286099365b6659e748137f', 'relocated_by_cited_placements': True, 'permanent_reference': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/fixed-universal-polynomials/05-signed19-heights-evidence-PROOF-PACKET.md', 'placement_note': 'Part IV, source05.'}, {'path': 'docs/incoming/Timed_Four_Mass_Quartic_Certificates.zip', 'report': 'timed-quartic addendum', 'reviewed_intake': False, 'bytes': 386033, 'sha256': '533b2d4b27b8a97492cd96926f185940c4fd5b9349de7683be2eaaadf8fbfc69', 'git_blob_sha1': 'e33b6f97c31101831ec724e0d4660cbbd953efe7', 'relocated_by_cited_placements': True, 'permanent_reference': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/18-timed-quartics-independent-audit.md', 'placement_note': 'Part VI, source18; additional relocated package, no scientific review claimed by this helper.'}, {'path': 'docs/incoming/Dimension_Independent_Particle_Thresholds_Package.zip', 'report': '29', 'reviewed_intake': False, 'bytes': 464972, 'sha256': '79bc1ff412c823bc58def8b1b6e1a9957abc2a2e2811c95d9b9f6299ae8b0e37', 'git_blob_sha1': 'b330960a51bf71eb0b187d6d84ae578d28c0f6aa', 'relocated_by_cited_placements': True, 'permanent_reference': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/19-mass-four-zd-PROOF.md', 'placement_note': 'Part VII, source19; additional relocated package, no scientific review claimed by this helper.'}, {'path': 'docs/incoming/Sparse_Orbit_Geometry_and_Exact_Counting_Package.zip', 'report': '30', 'reviewed_intake': False, 'bytes': 519064, 'sha256': '48640b94c33253e074ed113d2f8464495a41f5f6f5eedd0fef7165d0a873513d', 'git_blob_sha1': 'c7d3122b4cb5357a48423ff2fd2deabc1dcf6a5f', 'relocated_by_cited_placements': True, 'permanent_reference': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/20-orbit-geometry-geometry-PROOF.md', 'placement_note': 'Part VII, source20; additional relocated package, no scientific review claimed by this helper.'}, {'path': 'docs/incoming/five-particle-binary-portable.zip', 'report': '14', 'reviewed_intake': False, 'bytes': 1325129, 'sha256': '23b560ec94f483e287daa535fcc2c59dd8f900e4effa42f052f6079aa81f3709', 'git_blob_sha1': '25e615b9a651305f8805ea40fdea84b306056ba4', 'relocated_by_cited_placements': True, 'permanent_reference': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/README.md', 'placement_note': 'Additional relocated package; source prefix 14-. No scientific review claimed by this helper.'}, {'path': 'docs/incoming/Reversible_Binary_Five_Particle_Package.zip', 'report': '15', 'reviewed_intake': False, 'bytes': 1029207, 'sha256': '8b9de168c3e4dc2e310f07cf7dfdaf217e343fa3c9c7a17d001b6b951a089505', 'git_blob_sha1': '1dc0cc2cbb49ae090e4f72e91b15690ef2ef3427', 'relocated_by_cited_placements': True, 'permanent_reference': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/README.md', 'placement_note': 'Additional relocated package; source prefix 15- (base article). No scientific review claimed by this helper.'}, {'path': 'docs/incoming/Literal_Universal_Reversible_Source_Package.zip', 'report': '16', 'reviewed_intake': False, 'bytes': 4929954, 'sha256': '20e6ee57b305ce7648fffa9c590c02807fecfb3fff8fc77885e0fdbab342be5d', 'git_blob_sha1': 'e1aa124cdf41e899ac4a956d24173df055fb7f0e', 'relocated_by_cited_placements': True, 'permanent_reference': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/README.md', 'placement_note': 'Additional relocated package; source prefix 16-. No scientific review claimed by this helper.'}, {'path': 'docs/incoming/Reversible_Startup_Optimization_Package.zip', 'report': '17', 'reviewed_intake': False, 'bytes': 3906157, 'sha256': '895c7dd7e59bed95796ce7d4cb97cdeec63a7ae0a0a19bf8f4b1c00cabcdb264', 'git_blob_sha1': '9a024790d4e0881c8b0af77d5f52e905507c09b7', 'relocated_by_cited_placements': True, 'permanent_reference': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/README.md', 'placement_note': 'Additional relocated package; source prefix 17-. No scientific review claimed by this helper.'}, {'path': 'docs/incoming/Cellular_Clock_Domination_Package.zip', 'report': '18', 'reviewed_intake': False, 'bytes': 3981536, 'sha256': '105704f39d75e27ea1046ac495e0d0eb6bb268c9c7a5cabf0904b4c577c1b7f5', 'git_blob_sha1': '659da895332e7753dfb0c1f70aca2e66d617742c', 'relocated_by_cited_placements': True, 'permanent_reference': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/README.md', 'placement_note': 'Additional relocated package; source prefix 18-. No scientific review claimed by this helper.'}, {'path': 'docs/incoming/Exact_Lazy_Reversible_CA_Evaluator_Package.zip', 'report': '19', 'reviewed_intake': False, 'bytes': 2390628, 'sha256': '159dcde2a8366d15cba6b5fc3fb49776712717fa7d5818423eac4dc592293a50', 'git_blob_sha1': '8c13789e0531a3be9edab8eaafddd4d5c2de1265', 'relocated_by_cited_placements': True, 'permanent_reference': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/README.md', 'placement_note': 'Additional relocated package; source prefix 19-. No scientific review claimed by this helper.'}, {'path': 'docs/incoming/Event_Budgeted_Quartic_Certificates_Package.zip', 'report': '20', 'reviewed_intake': False, 'bytes': 1601106, 'sha256': 'dbec7568abb81cf75b346f5e7321c58e1fe6a813f508f36e2e2a6dbe26f4fb01', 'git_blob_sha1': '224d4c7051c4da7584c623226dad874b4f41c126', 'relocated_by_cited_placements': True, 'permanent_reference': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/README.md', 'placement_note': 'Additional relocated package; source prefix 20-event-budget-. No scientific review claimed by this helper.'}, {'path': 'docs/incoming/Unbounded_Compact_Clean_Clocks_Package.zip', 'report': '21', 'reviewed_intake': False, 'bytes': 899295, 'sha256': '4c3006f933dde566d6cbe20195236b09a27925c4e14cc79ff853f3202dc17822', 'git_blob_sha1': '9e352eed9d22cede1dd0d68f5b5a37ac1b27aff9', 'relocated_by_cited_placements': True, 'permanent_reference': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/README.md', 'placement_note': 'Additional relocated package; source prefix 22-clean-clocks-. No scientific review claimed by this helper.'}]

def need(ok, message):
    if not ok:
        raise ValueError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def same(a, b):
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(same(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(same(x, y) for x, y in zip(a, b))
    return a == b

def git(repo, *args):
    result = subprocess.run(['git', '--no-pager', '-C', str(repo), *args],
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    need(result.returncode == 0, 'git read failed: ' + result.stderr.decode(errors='replace').strip())
    return result.stdout

def inside(path, parent):
    return path == parent or parent in path.parents

def external(path, repo, message):
    need(not inside(path.resolve(), repo), message)

def no_symlink_components(path):
    raw = path.absolute()
    for part in (raw, *raw.parents):
        need(not part.is_symlink(), 'refuse symlink in write path: ' + str(part))

def preflight_file(path, expected_bytes, repo, cache=None):
    no_symlink_components(path)
    external(path, repo, 'output would write inside the repository')
    if cache is not None:
        need(inside(path.resolve(), cache), 'archive path escapes the output cache')
    need(not path.is_symlink(), 'refuse archive/receipt symlink: ' + str(path))
    if path.exists():
        need(path.is_file(), 'existing output is not a regular file: ' + str(path))
        need(path.read_bytes() == expected_bytes, 'refuse differing existing output: ' + str(path))

def write_new_or_same(path, data, repo, cache=None):
    preflight_file(path, data, repo, cache)
    path.parent.mkdir(parents=True, exist_ok=True)
    # Recheck resolved parents after creation; never replace an existing file.
    preflight_file(path, data, repo, cache)
    if not path.exists():
        try:
            with path.open('xb') as stream:
                stream.write(data)
        except FileExistsError:
            preflight_file(path, data, repo, cache)
    need(path.read_bytes() == data, 'post-write byte mismatch: ' + str(path))

def prepare(repo_root, output_root):
    repo = repo_root.resolve(strict=True)
    need(repo.is_dir(), 'repository root must be a directory')
    actual = Path(git(repo, 'rev-parse', '--show-toplevel').decode().strip()).resolve()
    need(repo == actual, '--repo-root must be the actual Git worktree root')
    revision = git(repo, 'rev-parse', '--verify', REVISION + '^{commit}').decode().strip()
    need(revision == REVISION, 'exact historical commit unavailable')
    no_symlink_components(output_root)
    cache = output_root.resolve()
    external(cache, repo, 'output cache must lie outside the repository')
    need(not inside(repo, cache), 'output cache must not contain the repository')
    need(not cache.exists() or cache.is_dir(), 'output root is not a directory')
    arcdir = cache/'docs/incoming'
    need(inside(arcdir.resolve(), cache), 'docs/incoming escapes the output cache')
    external(arcdir, repo, 'docs/incoming resolves inside repository')
    target = (repo/'Computability').resolve(strict=True)
    need(target.is_dir() and inside(target, repo), 'current source bridge target must be the repository Computability directory')
    bridge = cache/'Computability'
    if bridge.is_symlink():
        need(bridge.resolve(strict=True) == target, 'different existing source bridge')
    else:
        need(not bridge.exists(), 'refuse existing nonsymlink source bridge')
    paths = [r['path'] for r in INVENTORY]
    listed = git(repo, 'ls-tree', '-r', '--name-only', REVISION, 'docs/incoming').decode().splitlines()
    need(set(paths) == {p for p in listed if p.endswith('.zip')}, 'complete historical computational ZIP inventory')
    need(len(INVENTORY) == len(set(paths)) == 23, 'exact twenty-three-archive inventory')
    need(sum(r['reviewed_intake'] for r in INVENTORY) == 12, 'twelve reviewed and eleven additional archives')
    data = []
    for record in INVENTORY:
        relative = Path(record['path'])
        need(relative.parts[:2] == ('docs', 'incoming') and len(relative.parts) == 3
             and relative.suffix == '.zip', 'fixed safe archive pathname')
        blob = git(repo, 'show', REVISION + ':' + record['path'])
        need(len(blob) == record['bytes'] and digest(blob) == record['sha256'],
             'historical archive size/SHA256: ' + record['path'])
        git_oid = hashlib.sha1(b'blob ' + str(len(blob)).encode() + b'\0' + blob).hexdigest()
        need(git_oid == record['git_blob_sha1'], 'historical Git blob identity: ' + record['path'])
        dest = cache/relative
        preflight_file(dest, blob, repo, cache)
        data.append((dest, blob))
    receipt = dict(status='PASS', source_sha256=digest(Path(__file__).read_bytes()),
                   historical_revision=REVISION, placement_commits=PLACEMENT_COMMITS[:],
                   placement_merge=PLACEMENT_MERGE, later_placement_head=LATER_PLACEMENT_HEAD, archives=INVENTORY,
                   archive_count=23, reviewed_archive_count=12, additional_relocated_count=11,
                   archive_bytes=sum(r['bytes'] for r in INVENTORY),
                   source_bridge=dict(path='Computability', target='supplied repository/Computability',
                                      validated_current_directory=True, replaces_frozen_source_pins=False),
                   verification=dict(exact_historical_blobs=True, sha256_and_git_blob_checks=23,
                                     byte_identical_cache_files=23, overwrite_differing=False,
                                     repository_writes=False, archive_extraction=False,
                                     archive_execution=False, scientific_review_rerun=False),
                   scope='Byte-level historical replay compatibility and relocation inventory only. '
                         'The current-source bridge is an explicitly checked symlink; individual frozen '
                         'reviewers still authenticate their own current source and archive/member pins. '
                         'No scientific assertion is independently established by archive copying.')
    return repo, cache, bridge, target, data, receipt

def materialize(repo, cache, bridge, target, data):
    cache.mkdir(parents=True, exist_ok=True)
    external(cache, repo, 'output cache changed to repository path')
    for path, blob in data:
        write_new_or_same(path, blob, repo, cache)
    if bridge.is_symlink():
        need(bridge.resolve(strict=True) == target, 'source bridge changed')
    else:
        need(not bridge.exists(), 'refuse source bridge overwrite')
        bridge.symlink_to(target, target_is_directory=True)
    need(bridge.is_symlink() and bridge.resolve(strict=True) == target, 'source bridge verification')

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo-root', type=Path, required=True)
    parser.add_argument('--output-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, help='optional stable receipt file, outside the repository')
    parser.add_argument('--expect', type=Path, help='type-exact saved receipt to check before writing cache')
    args = parser.parse_args()
    repo, cache, bridge, target, data, receipt = prepare(args.repo_root, args.output_root)
    if args.expect:
        need(same(receipt, json.loads(args.expect.read_text())), 'type-exact saved receipt')
    encoded = (json.dumps(receipt, sort_keys=True, indent=2) + '\n').encode()
    if args.output:
        preflight_file(args.output, encoded, repo)
    materialize(repo, cache, bridge, target, data)
    if args.output:
        write_new_or_same(args.output, encoded, repo)
    print(json.dumps(dict(status='PASS', revision=REVISION, archives=23,
                          archive_bytes=receipt['archive_bytes'], source_bridge=True)))

if __name__ == '__main__':
    main()
