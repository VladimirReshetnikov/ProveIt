#!/usr/bin/env python3
"""Pinned publication-delta audit; no author suites or repository writes."""
import argparse,ast,hashlib,json,re,subprocess,tempfile
from collections import Counter
from pathlib import Path
BASE_COMMIT = '3aa123856b850f016cfa100b4684fa7902d2cecd'

COMMIT = '86267b8a30bcf1e15e9254f4f4aa595d55481b2a'

PLACEMENT = '8a4e647326e8c92f53e222c10e9107b40918a1ff'

OLD_PLACEMENT = 'a7ae02511c5584086ef9152f92d59ba77efa6148'

BASE_PATH = 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/'

WIP = 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/'

REPORTS = ['canonical-diophantine-certificates',
 'quadratic-orthant-certificates',
 'signal-machine-collision-certificates']

PINS = {'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/README.md': {'after': '0ce45e3e6ca12dad0846957b51491ff792aadd54349a8246d4c613e6a2ccb306',
                                                                                                         'before': '8df1c7b5cade5b59a37082d8933da72c9af07654f507da94d0cdea64d9e90707'},
 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/article.pdf': {'after': '5150a5e57d015650c90e30e3bea22a7af2936059df9346c39f73d6f9f285e8e5',
                                                                                                           'before': '050f896b175322cce0d1662827ac0e6f4f207e60d54b2c8a3a1ff9c6ef2cdb11'},
 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/article.tex': {'after': 'e7047ec1f4708fd6497607b41c7b8e37da230ca77398933820c63ebc5a28a3ce',
                                                                                                           'before': '2bc70d847ea296d59d0686edb42500cdc14ebe39c238ef07960b78534c839069'},
 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/quadratic-orthant-certificates/README.md': {'after': 'd9a65acacfaf51fcf62a8392c0836f572fd93177a55e3934e0c1a923922212ae',
                                                                                                     'before': '548929d87a89e02a6b97520df68eb17025764caa34353692818b616f6a9a85f1'},
 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/quadratic-orthant-certificates/article.pdf': {'after': '09ee8b56560ef9d3667cf169136f3aa5161022a136be40f9e90b941e67c2bfab',
                                                                                                       'before': 'c2bea56002fb0cf717f986764142ad2b077ae835bf17d15491d245d43560eabc'},
 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/quadratic-orthant-certificates/article.tex': {'after': '6e3a2f3936b3ec9f16e725964f4366b17e0a89a9e45e1870758bc5b710cb84d2',
                                                                                                       'before': '36cd72be5fb0cf5fe2c06c79af530e2285830bb78c2ce613044b78ae623ddaf3'},
 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/README.md': {'after': '75a120a08d92bab1b5477492cab50fd93a3f6154ef787bc5cf30e3d99a76e505',
                                                                                                            'before': 'dc3a5253f2b377eac2d2219229661b389d8cf1498ec6d567bcaa95bcdb7f8f99'},
 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/article.pdf': {'after': '6f5f5aae58a4ceb6914bd98701e75f1554096072d84983d2f6492977becbc53f',
                                                                                                              'before': 'aa54fea4b203cb6ecb15a76e55dffccec2be928b417e83387b3b1cd80b4df166'},
 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/article.tex': {'after': '6108d3228e19510ad3fcaea2dbeaec65a5f6dbf3c97530470834ce511035fe93',
                                                                                                              'before': '2e1e73628bf21158f4fe63beaf2fd5e13c08259dfea666929081a8f98d1f581a'}}

DEPENDENCIES = {'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/eager_tree_exact_application_inputs.patch': 'bb669fe7b71621d6fbe968ce8ed5833092dee996e262a78a6471f0aeb9bccdfe',
 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/placement_a7ae02511_inventory.json': 'cec197a4c1367d9dcd671ba85fa242fbdaba5445251794535f0333c2228687cf',
 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/replay_placed_substrates_a7ae02511.py': '1230f838cefd03663e42a3c7e45ce056cab502ef2e405879827dd4280490ad3c',
 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/reset_net_exact_domains.patch': 'bc3d28a42f97b60e5d5e17075d3383c298038bff01e1296a792af2aff3929720',
 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_batch80_corrected.json': '3d9a17728d96b6fd72ac972c3e0e38c35ac968855a10514e534d6c9fe67ee8c8',
 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_batch80_corrected.md': '04ac1741c5eb07379e23a88096cc0b49ce65458f54cf1e9d9c672369d047f031',
 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_batch80_corrected.py': 'a3afcb8ef13977398e8c38a54e28a87d66c423158c9ff912ea5d6d530b881d86',
 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/sparse_mass_exact_polynomials.patch': 'b35dbe66ef29003111e3839ecb6a87bff6e5bf438360df4f31eb0ee855a8c4f2'}

REPAIRS = {'canonical-diophantine-certificates': [('the batch-80K1 placement, so since batch 80 the stager '
                                         'authenticates only a\n'
                                         'checkout of `a7ae02511` (`git worktree add <dir> a7ae02511`), '
                                         'where it\n'
                                         'restores the original edition; on a current checkout it stops with '
                                         '"Placed\n'
                                         'source differs". For the corrected layout extract the batch-80 '
                                         'archive.',
                                         'the batch-80K1 placement. For an original-edition restoration, '
                                         'pass an\n'
                                         'unchanged historical checkout (for example, a worktree at '
                                         '`a7ae02511`) as\n'
                                         '`--repo`. Invoke the helper from a recent checkout, with its '
                                         'sibling\n'
                                         '`placement_a7ae02511_inventory.json` beside it: neither file '
                                         'exists at\n'
                                         '`a7ae02511`. A current corrected checkout passed as `--repo` stops '
                                         'with\n'
                                         '"Placed source differs". For the corrected layout extract the '
                                         'batch-80 archive.')],
 'quadratic-orthant-certificates': [('batch-80K1 placement. Since batch 80 the stager authenticates only a\n'
                                     '  checkout of `a7ae02511` (`git worktree add <dir> a7ae02511`), where '
                                     'it\n'
                                     '  restores the original editions; on a current checkout it stops with\n'
                                     '  "Placed source differs". For the corrected layout of source 17 '
                                     'extract\n'
                                     '  the batch-80 archive.',
                                     'batch-80K1 placement. For original-edition restoration, pass an '
                                     'unchanged\n'
                                     '  historical checkout (for example, a worktree at `a7ae02511`) as '
                                     '`--repo`,\n'
                                     '  while invoking the later helper from a recent checkout with its '
                                     'required\n'
                                     '  sibling `placement_a7ae02511_inventory.json`. Neither helper nor '
                                     'inventory\n'
                                     '  exists at `a7ae02511`. A current corrected checkout passed as '
                                     '`--repo`\n'
                                     '  stops with "Placed source differs". For the corrected layout of '
                                     'source 17\n'
                                     '  extract the batch-80 archive.'),
                                    ("2. run the research programme's stager,\n"
                                     '   `py '
                                     'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/replay_placed_substrates_a7ae02511.py '
                                     '--repo . --destination <new directory>`\n'
                                     '   from the repository root (it authenticates the placed files and '
                                     'restores\n'
                                     '   the complete layouts from Git). Since batch 80 run it only from a\n'
                                     '   checkout of `a7ae02511` (`git worktree add <dir> a7ae02511`); it '
                                     'then\n'
                                     "   restores source 17's original edition, and on a current checkout "
                                     'it\n'
                                     '   stops at the replaced files; or',
                                     '2. create an unchanged historical checkout, for example with\n'
                                     '   `git worktree add <historical-checkout> a7ae02511`, then run\n'
                                     '   `py '
                                     'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/replay_placed_substrates_a7ae02511.py '
                                     '--repo <historical-checkout> --destination <new-directory>`\n'
                                     '   from a recent repository root where the helper and its required '
                                     'sibling\n'
                                     '   `placement_a7ae02511_inventory.json` exist. Neither file exists in '
                                     'the\n'
                                     '   `a7ae02511` checkout. This restores the original editions from the\n'
                                     '   historical placed bytes; passing the current corrected checkout as\n'
                                     '   `--repo` stops at the replaced files; or')],
 'signal-machine-collision-certificates': [("# (b) from the shipped files, with the research tree's "
                                            'placement stager\n'
                                            '#     (authenticates the shipped bytes, restores the omitted '
                                            'members from Git;\n'
                                            '#      the destination must not exist)\n'
                                            'py '
                                            'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/replay_placed_substrates_a7ae02511.py '
                                            '\\\n'
                                            '   --repo . --destination ../placed-a7ae02511',
                                            '# (b) original editions: run the later helper from this recent '
                                            'checkout,\n'
                                            '#     with its sibling placement_a7ae02511_inventory.json '
                                            'present.\n'
                                            '#     The historical checkout and destination below must not '
                                            'exist yet.\n'
                                            'git worktree add ../source-a7ae02511 a7ae02511\n'
                                            'py '
                                            'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/replay_placed_substrates_a7ae02511.py '
                                            '\\\n'
                                            '   --repo ../source-a7ae02511 --destination '
                                            '../placed-a7ae02511'),
                                           ('program, not part of this report. Since batch 80 it '
                                            'authenticates only a\n'
                                            'checkout of `a7ae02511` (`git worktree add <dir> a7ae02511`), '
                                            'where it\n'
                                            "restores source 13's original edition; on a current checkout it "
                                            'stops\n'
                                            'earlier, with "Placed source differs" at the five replaced '
                                            'files. For the\n'
                                            'corrected layout use way (a).',
                                            'program, not part of this report. Since batch 80, use an '
                                            'unchanged\n'
                                            'historical checkout as its `--repo` argument to restore the '
                                            'original edition.\n'
                                            'Invoke the helper from a recent checkout with its required '
                                            'sibling inventory:\n'
                                            'neither helper nor inventory exists at `a7ae02511`. Passing a '
                                            'current\n'
                                            'corrected checkout as `--repo` stops earlier, with "Placed '
                                            'source differs"\n'
                                            'at replaced files. For the corrected layout use way (a).')]}

PATCH_SHA = '8751b2451db35ab5c00d357b3f3c26abc5d3103ae81e45935c776caacd4fc846'

def need(value, message):
    if not value:
        raise ValueError(message)


def sha(value):
    return hashlib.sha256(value).hexdigest()


def exact(a, b):
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return a.keys() == b.keys() and all(exact(a[k], b[k]) for k in a)
    if type(a) in (list, tuple):
        return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b


def git(repo, *args):
    return subprocess.check_output(['git', *args], cwd=repo, timeout=120)


def blob(repo, commit, path):
    return git(repo, 'show', commit + ':' + path)


def paths(repo, commit, prefix=''):
    return git(repo, 'ls-tree', '-r', '--name-only', commit, '--', prefix or '.').decode().splitlines()


def blocks(text, names):
    # Each literal occurrence is retained in source order, including duplicates.
    # These environments do not nest another copy of themselves in the audited text.
    pattern = r'\\begin\{(' + '|'.join(re.escape(n) for n in names) + r')\}.*?\\end\{\1\}'
    result = [(m.group(1), m.group(0)) for m in re.finditer(pattern, text, re.S)]
    for name in names:
        need(text.count(r'\begin{' + name + '}') == text.count(r'\end{' + name + '}') == sum(n == name for n, _ in result),
             'Environment census did not consume every occurrence: ' + name)
    return result


def formal_census(before, after):
    declared = re.findall(r'\\newtheorem\*?\{([^}]+)\}', before)
    formal_names = sorted(set(declared + ['proof']))
    display_names = ['equation', 'equation*', 'align', 'align*', 'gather', 'gather*',
                     'multline', 'multline*', 'displaymath', 'eqnarray', 'eqnarray*']
    a, b = blocks(before, formal_names), blocks(after, formal_names)
    need(a == b, 'A formal statement/proof occurrence changed')
    c, d = blocks(before, display_names), blocks(after, display_names)
    need(c == d, 'A mathematical display occurrence changed')
    raw_a = re.findall(r'(?<!\\)\\\[.*?(?<!\\)\\\]', before, re.S)
    raw_b = re.findall(r'(?<!\\)\\\[.*?(?<!\\)\\\]', after, re.S)
    need(raw_a == raw_b, 'A bracketed display occurrence changed')
    label_a = re.findall(r'\\label\{[^}]+\}', before)
    label_b = re.findall(r'\\label\{[^}]+\}', after)
    need(label_a == label_b, 'Label occurrences changed')
    macros_a = [line for line in before.splitlines() if re.match(r'\\(?:newcommand|renewcommand|providecommand|DeclareMathOperator|newtheorem)', line)]
    macros_b = [line for line in after.splitlines() if re.match(r'\\(?:newcommand|renewcommand|providecommand|DeclareMathOperator|newtheorem)', line)]
    need(macros_a == macros_b, 'Mathematical macro definition lines changed')
    return dict(formal_occurrences=len(a), formal_by_environment=dict(sorted(Counter(n for n, _ in a).items())),
                display_environment_occurrences=len(c), bracket_display_occurrences=len(raw_a),
                labels=len(label_a), macro_definition_lines=len(macros_a),
                ordered_occurrence_bytes_sha256=sha(json.dumps([a, c, raw_a, label_a, macros_a], ensure_ascii=False, separators=(',', ':')).encode()))


def apply_patch(directory, patch_bytes):
    patch_file = directory / 'repair.patch'
    patch_file.write_bytes(patch_bytes)
    return subprocess.run(['patch', '--batch', '--forward', '-p1', '-i', str(patch_file)],
                          cwd=directory, capture_output=True, timeout=120)


def corrected_patch_status(repo, dependencies):
    # Only text patching and AST reading in fresh temporary directories; no imported code.
    configs = [
        ('tree', 'canonical-diophantine-certificates', 'eager_tree_exact_application_inputs.patch',
         {'code/tree_kernel.py': 'code/21-eager-tree-tree_kernel.py'}),
        ('reset', 'quadratic-orthant-certificates', 'reset_net_exact_domains.patch',
         {'build_net.py': 'code/17-reset-net-build_net.py', 'peak_quadratic.py': 'code/17-reset-net-peak_quadratic.py'}),
        ('sparse', 'signal-machine-collision-certificates', 'sparse_mass_exact_polynomials.patch',
         {'replay/core/sparse_mass.py': 'code/13-sparse-lattice-sparse_mass.py'})]
    out = []
    for name, report, patch_name, mapping in configs:
        with tempfile.TemporaryDirectory(prefix='publication-old-patch-') as tmp:
            directory = Path(tmp)
            source_pins = {}
            for target, source in mapping.items():
                data = blob(repo, COMMIT, BASE_PATH + report + '/' + source)
                need(data == blob(repo, PLACEMENT, BASE_PATH + report + '/' + source), 'Placed repaired source changed after placement')
                path = directory / target
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
                source_pins[source] = sha(data)
            result = apply_patch(directory, dependencies[WIP + patch_name])
            row = dict(package=name, corrected_source_pins=source_pins, patch_exit=result.returncode)
            if name in ('tree', 'reset'):
                need(result.returncode == 1 and b'FAILED' in result.stdout, 'Previously applied guard patch unexpectedly applicable')
                row['result'] = 'Guard patch fails on already repaired source'
            else:
                need(result.returncode == 0, 'Expected sparse duplicate-guard patch application')
                tree = ast.parse((directory / 'replay/core/sparse_mass.py').read_text())
                cls = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == 'Poly')
                count = sum(isinstance(n, ast.FunctionDef) and n.name == '__post_init__' for n in cls.body)
                need(count == 2, 'Sparse old patch did not duplicate constructor method')
                row.update(result='Old patch adds a second __post_init__ method', resulting_constructor_count=count)
            out.append(row)
    return out


def separated_historical_stage(repo, dependencies):
    inventory = json.loads(dependencies[WIP + 'placement_a7ae02511_inventory.json'])
    old_paths = set(paths(repo, OLD_PLACEMENT))
    driver_names = ['replay_placed_substrates_a7ae02511.py', 'placement_a7ae02511_inventory.json']
    need(all(WIP + n not in old_paths for n in driver_names), 'Historical driver unexpectedly exists')
    helper = dependencies[WIP + driver_names[0]].decode()
    tree = ast.parse(helper)
    stage = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'stage')
    stage_text = ast.get_source_segment(helper, stage)
    need("(repo/path).read_bytes()" in stage_text, 'Stage no longer reads the supplied root')
    need("Path(__file__).with_name('placement_a7ae02511_inventory.json')" in helper,
         'Default inventory no longer comes from helper sibling')
    need("p.add_argument('--repo',type=Path,required=True)" in helper,
         'Explicit historical root argument unavailable')
    return dict(helper_and_inventory_absent_at_historical_commit=True,
                later_helper_and_inventory_pins_authenticated=True,
                explicit_repo_reads_placed_files=True, default_inventory_is_helper_sibling=True,
                historical_manifest_placed_files=len(inventory['matched_files']),
                scope='Read-only Git absence/presence and authenticated helper AST/interface inspection; no full stager or author suite rerun')


def verify(repo, patch_path):
    repo = Path(repo).resolve()
    need(git(repo, 'rev-parse', BASE_COMMIT).decode().strip() == BASE_COMMIT, 'Missing base commit')
    need(git(repo, 'rev-parse', COMMIT).decode().strip() == COMMIT, 'Missing publication commit')
    delta = git(repo, 'diff', '--name-only', BASE_COMMIT, COMMIT).decode().splitlines()
    need(set(delta) == set(PINS) and len(delta) == 9, 'Publication delta is not exactly the nine audited paths')
    sources = {}
    for path, pin in PINS.items():
        before, after = blob(repo, BASE_COMMIT, path), blob(repo, COMMIT, path)
        need(sha(before) == pin['before'] and sha(after) == pin['after'], 'Publication source pin differs: ' + path)
        sources[path] = (before, after)
    dependencies = {path: blob(repo, COMMIT, path) for path in DEPENDENCIES}
    need(all(sha(value) == DEPENDENCIES[path] for path, value in dependencies.items()), 'Prior review or patch dependency pin differs')
    patch_bytes = Path(patch_path).read_bytes()
    need(sha(patch_bytes) == PATCH_SHA, 'README repair patch pin differs')
    formal, pdfs, repairs, file_counts = {}, {}, {}, {}
    with tempfile.TemporaryDirectory(prefix='publication-delta-') as tmp:
        directory = Path(tmp)
        for report in REPORTS:
            prefix = BASE_PATH + report + '/'
            before, after = sources[prefix + 'article.tex']
            formal[report] = formal_census(before.decode(), after.decode())
            pdf = directory / (report + '.pdf'); pdf.write_bytes(sources[prefix + 'article.pdf'][1])
            info = subprocess.check_output(['pdfinfo', str(pdf)], timeout=120).decode()
            pages = int(re.search(r'^Pages:\s+(\d+)', info, re.M).group(1))
            expected_pages = dict(zip(REPORTS, [608, 169, 120]))[report]
            need(pages == expected_pages, 'Published PDF page count differs')
            txt = subprocess.check_output(['pdftotext', str(pdf), '-'], timeout=120).decode()
            normalized = re.sub(r'\s+', ' ', txt).lower()
            need('corrected code edition' in normalized, 'New corrected-code note not found in PDF extraction')
            pdfs[report] = dict(pages=pages, corrected_code_edition_text_present=True,
                               scope='Basic pinned PDF page/text check; no rebuild or visual-layout validation')
            files = paths(repo, COMMIT, prefix)
            groups = Counter('code' if '/code/' in p else 'data' if '/data/' in p else 'root' for p in files)
            package_prefix, package_total = dict(zip(REPORTS, [('21-eager-tree-', 53), ('17-reset-net-', 54), ('13-sparse-lattice-', 38)]))[report]
            package_files = [p for p in files if Path(p).name.startswith(package_prefix)]
            need(len(package_files) == package_total, 'Corrected package placement count differs')
            file_counts[report] = dict(total=len(files), by_directory=dict(sorted(groups.items())),
                                       corrected_package_prefix=package_prefix, corrected_package_files=len(package_files))
            old_readme = sources[prefix + 'README.md'][1].decode()
            expected = old_readme
            lines = []
            for old, new in REPAIRS[report]:
                need(expected.count(old) == 1, 'Repair anchor is not unique')
                lines.append(old_readme[:old_readme.index(old)].count('\n') + 1)
                expected = expected.replace(old, new, 1)
            target = directory / prefix / 'README.md'
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(old_readme)
            repairs[report] = dict(source_lines=lines, replacements=len(lines),
                                   before_sha256=sha(old_readme.encode()), expected_after_sha256=sha(expected.encode()))
        result = apply_patch(directory, patch_bytes)
        need(result.returncode == 0, 'Private README repair failed')
        for report, row in repairs.items():
            got = (directory / BASE_PATH / report / 'README.md').read_bytes()
            need(sha(got) == row['expected_after_sha256'], 'README repaired bytes differ')
    return dict(status='PASS_BOUNDED_PUBLICATION_AUDIT_WITH_ONE_REPAIR', base_commit=BASE_COMMIT,
                publication_commit=COMMIT, corrected_placement_commit=PLACEMENT, source_pins=PINS,
                dependency_pins=DEPENDENCIES, exactly_nine_changed_paths=True,
                no_code_or_data_changes_in_publication_range=True, formal_occurrence_census=formal,
                pdf_basic_checks=pdfs, report_file_counts=file_counts,
                old_review_patch_status=corrected_patch_status(repo, dependencies),
                historical_replay_recipe=separated_historical_stage(repo, dependencies),
                repair=dict(patch_sha256=PATCH_SHA, private_application='PASS', readme_files=repairs),
                finding='P3: historical checkout lacks later replay helper and its inventory; use the later helper with --repo naming the historical snapshot.',
                scope='All six textual publication diffs read; unchanged formal occurrence bytes checked with multiplicity. Prior corrected API review and placement pins reused, no historical author suites or new theorem audit. Earlier editorial patches remain outside this delta review.')


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--repo', type=Path, required=True)
    p.add_argument('--patch', type=Path, default=Path(__file__).with_name('batch80_historical_stager_launch.patch'))
    p.add_argument('--output', type=Path)
    p.add_argument('--expect', type=Path)
    a = p.parse_args()
    result = verify(a.repo, a.patch)
    if a.expect:
        need(exact(result, json.loads(a.expect.read_text())), 'Saved audit receipt differs')
    if a.output:
        a.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True))
