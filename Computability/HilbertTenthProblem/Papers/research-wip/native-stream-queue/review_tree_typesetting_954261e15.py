#!/usr/bin/env python3
"""Pinned, ordered Tree Calculus typesetting transfer and private editorial patch.

Python standard library only; read-only Git and the standard patch command are
used. No author code is imported or executed; no repository file is written.
"""
import argparse
from collections import Counter
import difflib
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import tempfile
import zipfile

COMMIT = '954261e15e38d84bdb2e1a97d93097a6b5551d5a'
PARENT = '525b7795b0718a5506d2eccd243cd3f012791a8a'
ARRIVAL = 'aebfa386e44f232be06b546be9fc2f6138ad34f2'
PLACEMENT = 'a7ae02511c5584086ef9152f92d59ba77efa6148'
REPORT = 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates'
WIP = 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'
ARCHIVE = 'docs/incoming/Eager_Tree_Calculus_Research_Package.zip'
ARCHIVE_SHA = '5c6c100296a58df366939febf2f7b6ca57616f17f77a71520f6f3a5e20204ab4'
ROOT = 'eager-tree-certificates/'
PATCH_NAME = 'review_tree_typesetting_954261e15.patch'
PINS = {
    'article.tex': '594e3da5caf4aac5228e594ed30feb506746c51d8d7896157934ed2566a38bb7',
    'README.md': '6c5a1a81931914f9caaff22c3a02dcd2a5c45d28f279718d8e96b358ffb3df8d',
    'article.pdf': '4ff74ee98f97c8a05046b8201e9bc2d6901d4798ad42985c15d8cca80fe18630',
}
BASIS = {
    'review_eager_tree_aebfa.md': 'a8a5ff72f4e90ccb461ec77339653c4613d65dc7fc40ff98445370ee13e4ff6d',
    'placement_a7ae02511_inventory.json': 'cec197a4c1367d9dcd671ba85fa242fbdaba5445251794535f0333c2228687cf',
}
# Embedded independently of the placement inventory; filled from authenticated
# original bytes once, then checked on every replay.
MEMBERS = {'MANIFEST.sha256': '8d332462fa6259862d0908984b31131ebdc2f1b728d8a50f81491c1cb4c94c88', 'README.md': 'a987fb2ec540488ecfcd1b241a98605e85e12cfe13ebcf7f589b79030171db9f', 'VERIFICATION.md': '63a5d5da9669786b84ada4e1e96c36bd7ce92a99406cb11b613763c657f99e32', 'build_pdf.py': '4d569c117355863b72c11292a695c13aef339fd39d9144fa462b55fd5e10a294', 'code/analyze_growth.py': '564ddcf01d0b979bcd684b514538568c90267a13f93c28a62aee01d19f30be94', 'code/audit_exact_count.py': '1a40fa46fc1f949a8dfacc606d4c5173b967439ab7e0e62f9a55b7b0dfda6c9b', 'code/audit_exact_count_receipt.json': 'd1d8996a31f07cdf52e907775862f38c71add9eee2890717ff98adc7a0845004', 'code/canonical.py': '42e4abaeb77da1842e70e2e9245584f18dd6fdfbf9094b0a62f4ea5b8a9b41bd', 'code/canonical_identity.json': '19c30d63c48ed4126091f73478a72ef4a39d257a5e61b15b696a8318aaf64721', 'code/canonical_overlay_audit.py': '661666842650cf2703253bedf9b58ed15f07042dc77db1d7aadc1b247af3ca81', 'code/canonical_overlay_receipt.json': '2b725672ec92082f5c93d1a8cbdd7bf8815834e1affa1747e79b8fe9d470a9a1', 'code/canonical_projected.py': '17ec7345bce074233b4fbbf295a9630233af9e6788f790a1f23201100fa2fa19', 'code/canonical_projected_audit.py': 'c23980869fd66f26bb162b39f7e9910bb52c7359ffb0c40a938654f94d05acb7', 'code/canonical_projected_audit_receipt.json': '52a0c98f3817e5ac290e0c34a8c10b29603c0aee77917dd05cac20cee7b82b7b', 'code/canonical_projected_identity.json': '2255d1f3649db71fc71fa920199c4d3adff38631690b0840efb383f149412f18', 'code/canonical_projected_receipt.json': 'f1f66a6c593e16d107a897124f557e9bf387d1e0db7f793c685d16235a604923', 'code/canonical_receipt.json': '6aacfbedbcd57e0c33cb9dc3b7476f8b3596245fab8e6a7eb876303c6519ca1a', 'code/constant_bit_bound.json': 'b7ff2d6b73bb61b9c92e5bd41cc65799d0a0b4b330774d4f35030f658e31e692', 'code/constant_bit_bound.py': '748e916caa6d4ddeca6ae44d9ff9e96fffda0d84d6803fee3f6a602bcd6d2b16', 'code/counter_source.py': '637f135a0c2152a0bd319c2eb376fe8c7b295f0a31b1a2c408aebfbd227d040d', 'code/counter_source_receipt.json': 'd196967b246dd54176c24a3061687a4dead0b0f2b593f549fb3cef0abaad11ef', 'code/cyclic_counterfeit.json': 'c9d1f38be4c64f8f29033f40afdd6bdc20d807560538be8c8c87d24be3e728cf', 'code/eager_compiler.py': '156624d1288c9167f8bfc6b1ed91564f10d5199f2d07c0fd4759ffed2f90c164', 'code/eager_compiler_receipt.json': 'b5f762a3d999314994e39650bad3c4a1619a878f2df952f079141ede8b591ff9', 'code/exact_growth_receipt.json': '778bd44c495474a94d6c4a57ad7895d2c4dce689ce4cf3dc7260148f0bd75712', 'code/export_shared_macro.py': 'f65a03c41e50e7b4ec6f3ca5c4a2c856ff3546539e683fdf9a86e82d3d9db58c', 'code/identity_certificate.json': 'bf243cebec4fd892960448702b1d76f241492b8358ecba2e89feba151d6d37a4', 'code/independent_audit.py': 'c3c34619e96ae499ba904282b453509994f5fad0adfaa99d32e45a57e74d3c75', 'code/independent_compiler_audit.py': '8eaae0232b1cf2a5ec42299b7e33d44f40f1d637b4ff0061034e55337e4575fb', 'code/independent_compiler_receipt.json': 'a1cbe11a17bbb7e3fcc1b897c826acb05d074bc7c491ba219ac9cc1bbbc8da86', 'code/independent_growth_audit.py': '21575c28e160a530cec9db648e4f4ba9a3065872051ae935452eb001bc74f288', 'code/independent_growth_receipt.json': '29294112cf84c1ce1754ec7bbb3d835ce006278f87387f9858a4e99858d8f239', 'code/independent_receipt.json': 'aea2b75bfe0f018e4f643af867211f95220c13b6673fd97224600e19449e6d46', 'code/independent_shared_audit.py': '4f7dc4bd64b38d0022f4b4470ff5bd1d4adb39ee42b2812aba40e903a8c726bd', 'code/independent_shared_receipt.json': '240dbadaca3126f585080757bbf6b06964366773686ff58f2d397f0846b521a2', 'code/literal_universal_tree.json': 'c6b647090cfc99e32f6a097e89dee8bab68f2be9a2ab3cbd5da222f6d0f70823', 'code/literal_universal_tree.sexpr': '6c8a9e8d33c76c72f106479bb37d18867e586cb8171aa4b91f136b8da6b34d69', 'code/packet_assumptions_receipt.json': '4c22cdd7ce4c29ccf63557323121154ad9e3a3f9076670f364a303ae50782b0a', 'code/receipt.json': 'cf25eb544bdf0a372e612dd034284664d43f59478e06b28bb07fd47b6d0fb73d', 'code/shared_compression.py': '37f6d785a212f5bad2f76dc8bddc640bb42e329e3f37f01d1e7ad13dbe4a81e8', 'code/shared_compression_program.json': 'f136280be791e6199064c960b5cc5f9ea6b8634392b36cacfae8d40a10a6bc74', 'code/shared_compression_receipt.json': '16e4c9888abf074c68d6498f4cf5698b02599678cb08e12151db64def2d10f85', 'code/shared_symbolic_proofs.json': '0341fdacffda5964705b1a0aadd7b84693b66328009198c65c882952c253e2c1', 'code/symbolic_audit.py': '79564e510bbb2a722ad7fa3c6a8a36fdaa6b29143bf77cc3618cd2b228204050', 'code/symbolic_receipt.json': '1ca2782bdeae292388a1a683425ea419fc39e019d42ae5833039ec032956b3d9', 'code/tree_kernel.py': 'f7a6433758b1d7167f1a7ff6f52f12b7348b60c714069884090b11187f2a8dcb', 'code/universal_code_circuit.json': '3528ad35d5d1ea99ac92c3d8af0f23f9ca3f2c129b0ad281fa2056f468e3e3b1', 'code/universal_lambda_source.json': 'a9aa268fe9052ebef2cbf368450d26be2b3d629fa34a05123f005d2cbad0e316', 'code/verify_packet_assumptions.py': '09fbcc859f0c561d6103ae6a81c63503116c5422ecda3a3740362906a1d648d0', 'code/verify_shared_macro.py': 'ea7188b2e29ebfe10d34481d6d438584951882d89d471feaf93dfeedc7267bae', 'eager-tree-certificates.pdf': '0e4c72feddf5b0187b6d055db273355e57012a5552bfe919ace18207577ca19f', 'eager-tree-certificates.tex': '196e6fbebcdeceaa81c3356682ef5325b0a4faae093167414465f30371e92c31', 'reproduce.py': '21104c49f48a7c818da2f9b9ea0b48879f736397ecef334f9e4fda1b86bbdcce', 'requirements-optional.txt': '5c17f2bd0ca0626fc3633b97c10741b33c018ca229c4c073ca1d7a94e5a9b909', 'sources.json': '7bcf24542682be538f27df8cba77ceae7982863d830ae27abd64b1eec45b5a3a', 'verify_manifest.py': '84d491ac994b82b6f07ae25c407877c9eb685423a015395d1776b08c5792f110'}
COMPATIBILITY = {'commit': 'bbc67d225e96a80a94b7d7a3c9a42f4c93e23cca', 'sha256': {'article.tex': '2bc70d847ea296d59d0686edb42500cdc14ebe39c238ef07960b78534c839069', 'README.md': '8df1c7b5cade5b59a37082d8933da72c9af07654f507da94d0cdea64d9e90707', 'article.pdf': '050f896b175322cce0d1662827ac0e6f4f207e60d54b2c8a3a1ff9c6ef2cdb11'}}
EXPECTED = {'formal': 42, 'display': 83, 'tables': 12, 'inline': 806}
EXCLUDED = {
    'README.md': 'original package guide; not placed separately',
    'eager-tree-certificates.tex': 'integrated into article.tex, not placed separately',
    'eager-tree-certificates.pdf': 'original PDF not placed separately',
    'MANIFEST.sha256': 'delivery checksum ledger retired after placement',
    'verify_manifest.py': 'delivery manifest checker not placed separately',
}


def need(value, message):
    if not value:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def exact(a, b):
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return a.keys() == b.keys() and all(exact(a[k], b[k]) for k in a)
    if type(a) in (list, tuple):
        return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b


def git(repo, *args):
    return subprocess.run(['git', '-C', str(repo), *args], check=True,
                          capture_output=True, timeout=90).stdout


def authenticated_blob(repo, ref, relative, digest):
    """Prefer matching working bytes; otherwise retrieve the exact pinned blob."""
    path = Path(repo) / relative
    data = path.read_bytes() if path.is_file() else None
    if data is None or sha(data) != digest:
        data = git(repo, 'show', ref + ':' + relative)
    need(sha(data) == digest, 'source pin mismatch: ' + relative)
    return data


def escaped(text, index):
    j = index - 1
    while j >= 0 and text[j] == '\\':
        j -= 1
    return (index - 1 - j) % 2 == 1


def comments(text):
    # Keep newlines for source locations; this is a pinned-source scanner, not
    # a general TeX interpreter. No audited formula uses a verbatim percent.
    out = []
    for line in text.splitlines(True):
        cut = next((i for i, c in enumerate(line) if c == '%' and not escaped(line, i)), None)
        out.append(line if cut is None else line[:cut] + ('\n' if line.endswith('\n') else ''))
    return ''.join(out)


def braced_end(text, start):
    need(start < len(text) and text[start] == '{', 'brace expected')
    depth = 1
    i = start + 1
    while i < len(text) and depth:
        if not escaped(text, i):
            depth += (text[i] == '{') - (text[i] == '}')
        i += 1
    need(depth == 0, 'unclosed brace')
    return i


def remove_command(text, name):
    rx = re.compile(r'\\' + name + r'\{')
    out, cursor = [], 0
    while True:
        match = rx.search(text, cursor)
        if match is None:
            return ''.join(out) + text[cursor:]
        out.append(text[cursor:match.start()])
        cursor = braced_end(text, match.end() - 1)


def normalize(text, source):
    """Only documented textual renames; no algebraic/formula normalization."""
    text = comments(text)
    for name in ('srcnote', 'label', 'srctag'):
        text = remove_command(text, name)
    # Strip the namespace only inside reference command arguments.
    text = re.sub(r'\\(ref|eqref|cref|Cref)\{([^}]+)\}',
                  lambda m: '\\' + m[1] + '{' + ','.join(
                      v.removeprefix('cdc:et:') for v in m[2].split(',')) + '}', text)
    aliases = ({'code': 'MATHCODE', 'file': 'FILECODE', 'cl': 'CLOSURE'} if source
               else {'tcode': 'MATHCODE', 'code': 'FILECODE', 'clos': 'CLOSURE'})
    text = re.sub(r'\\([A-Za-z]+)', lambda m: '\\' + aliases.get(m[1], m[1]), text)
    # The manuscript eqtag macro prints upright kernel-rule names; the merge
    # spells these out using textup. Normalize that one documented rewrite.
    text = re.sub(r'\\eqtag\{([^}]+)\}', r'\\textup{\1}', text)
    text = text.replace(r'Appendix~A (\cref{app:literal})', 'Appendix~A')
    return re.sub(r'\s+', '', text)


PATTERNS = {
    'formal': r'\\begin\{(theorem|lemma|proposition|corollary|definition|proof)\}[\s\S]*?\\end\{\1\}',
    'display': r'(?<!\\)\\\[[\s\S]*?(?<!\\)\\\]|\\begin\{(equation\*?|align\*?|gather\*?|multline\*?)\}[\s\S]*?\\end\{\1\}',
    'tables': r'\\begin\{(tabular|longtable|lstlisting)\}[\s\S]*?\\end\{\1\}',
    'inline': r'(?<!\\)\$(?!\$)[\s\S]*?(?<!\\)\$',
}


def blocks(text, kind, ranges):
    out = []
    for left, right in ranges:
        for m in re.finditer(PATTERNS[kind], text[left:right]):
            out.append({'start': left + m.start(), 'end': left + m.end(),
                        'body': m.group(),
                        'environment': m[1] if m.lastindex and m[1] else kind})
    return out


def ordered_match(source, target):
    """A single increasing cursor for the complete category, not per formula."""
    cursor, result = 0, []
    for i, item in enumerate(source):
        found = next((j for j in range(cursor, len(target)) if target[j] == item), None)
        need(found is not None, 'missing ordered occurrence ' + str(i))
        result.append(found)
        cursor = found + 1
    need(all(x < y for x, y in zip(result, result[1:])), 'nonincreasing match')
    return result


def selected_ranges(article):
    intro = article.index(r'\subsection{Manuscript 21:')
    next_part = re.search(r'^\\part\{', article[intro:], re.M)
    need(next_part is not None, 'no end of manuscript21 introduction')
    start = article.index(r'\part{Eager Tree Calculus:')
    end = re.search(r'^\\appendix\s*$', article[start:], re.M)
    need(end is not None, 'no actual appendix command')
    ranges = [(intro, intro + next_part.start()), (start, start + end.start())]
    need(ranges[0][0] < ranges[0][1] <= ranges[1][0] < ranges[1][1], 'overlapping ranges')
    return ranges


def transfer(source, article):
    source_range = [(source.index(r'\begin{document}'), source.index(r'\begin{thebibliography}'))]
    target_ranges = selected_ranges(article)
    result = {}
    for kind, count in EXPECTED.items():
        src = blocks(source, kind, source_range)
        dst = blocks(article, kind, target_ranges)
        needles = [normalize(v['body'], True) for v in src]
        targets = [normalize(v['body'], False) for v in dst]
        matches = ordered_match(needles, targets)
        need(len(src) == count, 'source census mismatch: ' + kind)
        result[kind] = {
            'source_count': len(src), 'target_count_in_reviewed_ranges': len(dst),
            'matched_distinct_ordered_occurrences': len(matches),
            'source_environment_counts': dict(sorted(Counter(v['environment'] for v in src).items())),
            'occurrences': [
                {'source_occurrence': i, 'target_occurrence': j,
                 'source_line': source.count('\n', 0, src[i]['start']) + 1,
                 'target_line': article.count('\n', 0, dst[j]['start']) + 1,
                 'normalized_sha256': sha(needles[i].encode())}
                for i, j in enumerate(matches)],
        }
    return {'ranges': [{'first_line': article.count('\n', 0, a) + 1,
                        'last_line_exclusive': article.count('\n', 0, b) + 1}
                       for a, b in target_ranges], 'categories': result}


def safe_archive(data):
    need(sha(data) == ARCHIVE_SHA, 'archive pin mismatch')
    result = {}
    with zipfile.ZipFile(io.BytesIO(data)) as archive:
        for info in archive.infolist():
            p = PurePosixPath(info.filename)
            need(not p.is_absolute() and '..' not in p.parts and '\\' not in info.filename
                 and not stat.S_ISLNK(info.external_attr >> 16), 'unsafe ZIP member')
            if info.is_dir():
                continue
            need(info.filename.startswith(ROOT) and info.filename not in result, 'ZIP root or duplicate member')
            result[info.filename.removeprefix(ROOT)] = archive.read(info)
    need({n: sha(b) for n, b in result.items()} == MEMBERS, 'full archive member pins differ')
    ledger = {}
    for line in result['MANIFEST.sha256'].decode().splitlines():
        m = re.fullmatch(r'([0-9a-f]{64})  (.+)', line)
        need(m is not None and m[2] not in ledger, 'bad manifest entry')
        ledger[m[2]] = m[1]
    need(ledger == {n: sha(b) for n, b in result.items() if n != 'MANIFEST.sha256'}, 'manifest ledger mismatch')
    need(len(result) == 56 and len(ledger) == 55, 'member/ledger size mismatch')
    return result


def target_for(member):
    if member in EXCLUDED:
        return None
    if member == 'VERIFICATION.md':
        return REPORT + '/21-eager-tree-' + member
    if member in ('build_pdf.py', 'reproduce.py'):
        return REPORT + '/code/21-eager-tree-' + member
    if member in ('sources.json', 'requirements-optional.txt'):
        return REPORT + '/data/21-eager-tree-' + member
    need(member.startswith('code/'), 'unclassified retained member')
    name = member.removeprefix('code/')
    need('/' not in name, 'unexpected nested member')
    destination = 'code' if name.endswith('.py') else 'data'
    return REPORT + '/' + destination + '/21-eager-tree-' + name


def macro_definition(text, name):
    rx = re.compile(r'\\newcommand\{\\' + name + r'\}(\[\d+\])?\{')
    matches = list(rx.finditer(comments(text)))
    need(len(matches) == 1, 'macro definition not unique: ' + name)
    clean = comments(text)
    m = matches[0]
    body = clean[m.end():braced_end(clean, m.end() - 1)-1]
    return (m[1] or '', re.sub(r'\s+', '', body))


def label_macro_audit(source, article):
    labels = re.findall(r'\\label\{([^}]+)\}', comments(source))
    all_labels = re.findall(r'\\label(?:\[[^]]*\])?\{([^}]+)\}', comments(article))
    need(len(labels) == len(set(labels)) == 74, 'original label census')
    mapped = ['cdc:et:' + v for v in labels]
    need(all(all_labels.count(v) == 1 for v in mapped), 'source label not preserved exactly once')
    need(len(all_labels) == len(set(all_labels)), 'merged duplicate label')
    preserved_macros = []
    for old, new in [('Leaf','Leaf'),('Stem','Stem'),('Fork','Fork'),('Apply','Apply'),
                     ('code','tcode'),('FV','FV'),('cl','clos'),('ev','ev'),('file','code'),
                     ('N','N'),('Z','Z'),('bits','bits')]:
        need(macro_definition(source, old) == macro_definition(article, new), 'macro changed: ' + old)
        preserved_macros.append({'source': old, 'target': new})
    return {'source_labels': 74, 'preserved_labels': mapped,
            'added_tree_namespace_labels': sorted(set(x for x in all_labels if x.startswith('cdc:et:')) - set(mapped)),
            'all_merged_labels_unique': len(all_labels), 'exact_macro_definitions': preserved_macros,
            'eqtag': 'source upright text macro is written out as textup; checked in occurrence census'}


def once(text, old, new):
    need(text.count(old) == 1, 'patch context not unique: ' + old[:100])
    return text.replace(old, new)


def repaired_sources(data):
    article, readme = data['article.tex'].decode(), data['README.md'].decode()
    readme = once(readme,
        'Tree Calculus, represented by its memoized proof DAG, for an externally\nfixed bound on the number of distinct calls.',
        'Tree Calculus, represented by its memoized proof DAG. Its one-witness\nstatement uses the canonical refinement at the exact number of distinct\ncalls; the base family for an externally fixed upper bound has nonunique\nwitnesses.')
    article = once(article,
        'and exact canonical DAG size $64n+113$ (\\cref{cdc:et:thm:binarysharing,cdc:et:thm:exactgrowth})',
        'and exact canonical DAG size $64n+113$ for $n\\geq2$, with $D_0=44$ and $D_1=179$ (\\cref{cdc:et:thm:binarysharing,cdc:et:thm:exactgrowth})')
    article = once(article,
        'a fixed-arity single-fold representation for the universal tree would settle the open single-fold problem.',
        'a fixed-arity single-fold representation for the universal tree, together with a fully charged single-fold input translation from universal halting, would settle the open single-fold problem.')
    article = once(article, 'This report was built from twenty manuscripts.', 'This report was built from twenty-one manuscripts.')
    article = once(article, 'One bibliography for the twenty manuscripts.', 'One bibliography for the twenty-one manuscripts.')
    return {'article.tex': article.encode(), 'README.md': readme.encode(), 'article.pdf': data['article.pdf']}


def patch_bytes(source, repaired):
    return ''.join(''.join(difflib.unified_diff(source[n].decode().splitlines(True),
                      repaired[n].decode().splitlines(True), fromfile='a/'+REPORT+'/'+n,
                      tofile='b/'+REPORT+'/'+n)) for n in ['README.md','article.tex']).encode()


def private_patch(source, patch, expected):
    with tempfile.TemporaryDirectory(prefix='tree-transfer-patch-') as temp:
        destination = Path(temp) / REPORT
        destination.mkdir(parents=True)
        for name, data in source.items():
            (destination/name).write_bytes(data)
        patchpath = Path(temp)/'review.patch'
        patchpath.write_bytes(patch)
        completed = subprocess.run(['patch', '--batch', '--forward', '--fuzz=0', '--no-backup-if-mismatch', '-p1', '-i', str(patchpath)],
                                   cwd=temp, capture_output=True, check=True, timeout=60)
        need('fuzz' not in completed.stdout.decode().lower(), 'patch used fuzz')
        for name in source:
            need((destination/name).read_bytes() == expected[name], 'private patched bytes differ: '+name)
        need(sorted(p.name for p in destination.iterdir()) == sorted(source), 'patch left unexpected file')
    return {'application': 'PASS --batch --forward --fuzz=0 -p1',
            'before_sha256': {n: sha(b) for n,b in source.items()},
            'after_sha256': {n: sha(b) for n,b in expected.items()},
            'pdf_unchanged': source['article.pdf'] == expected['article.pdf'],
            'pdf_rebuild_required_on_application': True}


def regressions():
    rejected = 0
    for a,b in [(['x','x'],['x']), (['x','y'],['y','x']),
                (['x','y','x'],['x','x','y']), (['x'],[])]:
        try:
            ordered_match(a,b)
        except ValueError:
            rejected += 1
        else:
            raise ValueError('order/multiplicity mutation accepted')
    need(ordered_match(['x','x'],['x','y','x']) == [0,2], 'duplicate positive control')
    need(normalize(r'\code(x)+\file{f}+\cl{a}{b}',True) == normalize(r'\tcode(x)+\code{f}+\clos{a}{b}',False), 'source-aware rename positive control')
    need(normalize(r'\code(x)',True) != normalize(r'\code(x)',False), 'source-aware rename negative control')
    need(normalize(r'\ref{lemma}',True) == normalize(r'\ref{cdc:et:lemma}',False), 'namespace positive control')
    need(normalize(r'cdc:et:literal',True) != normalize(r'literal',False), 'namespace stripped outside reference')
    need(normalize('$a+b$',True) != normalize('$b+a$',False), 'algebraic order normalized')
    need(normalize('$a+a$',True) != normalize('$2a$',False), 'algebraic rewrite normalized')
    need(not exact({'x':1},{'x':True}) and not exact({'x':1},{'x':1.0}), 'receipt numeric types conflated')
    fixture = (r'\subsection{Manuscript 21: X}' + '\n% \\appendix in a comment\n'
               + r'\part{Old}' + '\n' + r'\part{Eager Tree Calculus: X}'
               + '\n% \\appendix in another comment\nbody\n' + r'\appendix' + '\n')
    need(selected_ranges(fixture)[1][1] == fixture.rindex(r'\appendix'), 'appendix comment used as boundary')
    return {'ordered_rejections': rejected, 'duplicate_positive_control': True,
            'anchored_actual_appendix_control': True,
            'source_aware_macro_namespace_controls': 4, 'no_algebra_normalization_controls': 2,
            'exact_numeric_type_controls': 2}


def verify(repo, patch=None, archive=None):
    repo = Path(repo).resolve()
    need(git(repo,'rev-parse',COMMIT).decode().strip() == COMMIT, 'reviewed commit mismatch')
    need(git(repo,'rev-parse',COMMIT+'^').decode().strip() == PARENT, 'reviewed parent mismatch')
    source = {n: authenticated_blob(repo,COMMIT,REPORT+'/'+n,h) for n,h in PINS.items()}
    basis = {n: authenticated_blob(repo,COMMIT,WIP+'/'+n,h) for n,h in BASIS.items()}
    data = Path(archive).read_bytes() if archive is not None else authenticated_blob(repo,ARRIVAL,ARCHIVE,ARCHIVE_SHA)
    files = safe_archive(data)
    inventory = json.loads(basis['placement_a7ae02511_inventory.json'])
    old_inventory = next(a for a in inventory['archives'] if a['path'] == ARCHIVE)
    need({x['member'].removeprefix(ROOT):x['sha256'] for x in old_inventory['members']} == MEMBERS, 'placement member inventory mismatch')
    placements, excluded = [], []
    for member, contents in sorted(files.items()):
        target = target_for(member)
        recorded = next(x['placed_paths'] for x in old_inventory['members'] if x['member'] == ROOT+member)
        need(recorded == ([] if target is None else [target]), 'derived placement differs from pinned inventory')
        if target is None:
            excluded.append({'member':ROOT+member,'reason':EXCLUDED[member],'sha256':sha(contents)})
            continue
        need(git(repo,'show',PLACEMENT+':'+target) == contents, 'original placement differs')
        need(authenticated_blob(repo,COMMIT,target,sha(contents)) == contents, 'current companion differs')
        placements.append({'member':ROOT+member,'target':target,'sha256':sha(contents),'bytes':len(contents)})
    need(len(placements) == 51 and len(excluded) == 5, 'retained/excluded census')
    need(git(repo,'diff',PLACEMENT,COMMIT,'--',*[p['target'] for p in placements]) == b'', 'companion changed between placement and assembly')
    old = files['eager-tree-certificates.tex'].decode()
    article = source['article.tex'].decode()
    preservation = transfer(old, article)
    labels = label_macro_audit(old, article)
    changed = git(repo,'diff-tree','--no-commit-id','--name-status','-r',COMMIT).decode().splitlines()
    need(changed == [f'M\t{REPORT}/README.md',f'M\t{REPORT}/article.pdf',f'M\t{REPORT}/article.tex'], 'unexpected integration files')
    repaired = repaired_sources(source)
    expected_patch = patch_bytes(source,repaired)
    if patch is not None:
        need(Path(patch).read_bytes() == expected_patch, 'patch bytes differ')
    patch_record = private_patch(source,expected_patch,repaired)
    # Every original occurrence must still survive the editorial-only patch.
    repaired_transfer = transfer(old,repaired['article.tex'].decode())
    need({k:v['source_count'] for k,v in repaired_transfer['categories'].items()} == EXPECTED, 'postpatch preservation differs')
    compatibility = {}
    if COMPATIBILITY:
        ref = COMPATIBILITY['commit']
        newer = {n: authenticated_blob(repo,ref,REPORT+'/'+n,h) for n,h in COMPATIBILITY['sha256'].items()}
        compatibility = dict(commit=ref, scope='patch applicability only; not a transfer/proof audit of later text',
                             **private_patch(newer,expected_patch,repaired_sources(newer)))
    return {
        'status':'PASS_ORDERED_TRANSFER_WITH_FIVE_PRIVATE_EDITORIAL_FIXES',
        'helper_sha256':sha(Path(__file__).read_bytes()),'commit':COMMIT,'parent':PARENT,'placement':PLACEMENT,
        'typeset_sha256':PINS,'basis_sha256':BASIS,
        'archive':{'path':ARCHIVE,'arrival':ARRIVAL,'sha256':ARCHIVE_SHA,'member_count':56,'manifest_entries':55,'members_sha256':MEMBERS},
        'retained_companions':placements,'excluded_members':excluded,
        'preservation':preservation,'label_macro_audit':labels,'regressions':regressions(),
        'normalization':['strip TeX comments and whitespace', 'remove balanced srcnote, label and srctag commands',
                         'normalize only ref/eqref/cref/Cref arguments from cdc:et:namespace',
                         'source code/file/cl versus target tcode/code/clos mapped to distinct common names',
                         'source eqtag{rule} to written-out textup{rule}',
                         'remove the added AppendixA literal-table crossreference in its exact textual form'],
        'matching':'One strictly increasing occurrence cursor per category across the Manuscript21 introduction followed by PartXIX; duplicate values consume distinct occurrences. No formula algebra or deduplication.',
        'changed_files':changed,
        'editorial_fixes':['README exact-DAG-size canonical uniqueness', 'PartXIX preface n>=2 and D0=44,D1=179',
                           'single-fold implication retains fully charged single-fold input translation',
                           'provenance twenty-one manuscripts', 'bibliography twenty-one manuscripts'],
        'patch':{'name':PATCH_NAME,'sha256':sha(expected_patch),'rechecked_original_occurrences_after_patch':EXPECTED,**patch_record},
        'later_commit_patch_compatibility':compatibility,
        'scope':'Pinned source-preservation and editorial audit only. Original full theorem/source review reused; no unchanged author modules/suites, no formal build, no PDF build/layout review, no operation-record claim. Python standard library plus Git and patch commands; temporary copies only.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo',type=Path,default=Path.cwd())
    parser.add_argument('--archive',type=Path,help='optional original ZIP; otherwise pinned Git fallback')
    parser.add_argument('--patch',type=Path,default=Path(__file__).with_name(PATCH_NAME))
    parser.add_argument('--expect',type=Path)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    result = verify(args.repo,args.patch,args.archive)
    if args.expect:
        need(exact(result,json.loads(args.expect.read_text())), 'saved receipt differs (including types)')
    if args.output:
        args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':result['status'],'retained':len(result['retained_companions']),
                      'ordered_source_counts':EXPECTED,'private_patch':result['patch']['application']},sort_keys=True))


if __name__ == '__main__':
    main()
