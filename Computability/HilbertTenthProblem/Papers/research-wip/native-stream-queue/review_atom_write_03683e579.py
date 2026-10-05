#!/usr/bin/env python3
"""Fresh read-only metadata audit. Never executes any delivered program."""
import argparse
import hashlib
import io
import json
import posixpath
import re
import subprocess
import zipfile
from pathlib import Path

COMMIT = '03683e579fd54a681ad649bd659cc51b1f450829'
ARRIVAL = '26e036956381b07bb43de0187965f8dcdf9194fb'
PLACEMENT = '27f2003053ae8f4f6bbccdc70b9e2dcb70b40238'
SOURCE_PIN = '715a716a3002b1e9f28daa2d81c009a392851b94'
HOST = 'SetTheory/Cardinals/docs/reports/ordinals-and-order-types/naming-elementary-embeddings/'
WIP = 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/'
ARCHIVES = [
    ('atom_actions_research.zip', 'atom_actions', 'nee:aa:',
     'c7f96e8905fb0da490c3960b0afdb6bde92fcb96673782ebfc1a2c1a160ce264'),
    ('commuting_injections_research.zip', 'commuting_injections', 'nee:ci:',
     '15d35b3a01bddc25a3fc47f4f39b262789d5f91928a91a566987f198371b0433'),
]
PLACED = [
    ('code/03-atom-actions-make_figure.py', 'atom_actions/figures/make_figure.py'),
    ('code/03-atom-actions-verify_presentations.py', 'atom_actions/verify_presentations.py'),
    ('code/04-commuting-injections-verify_results.py', 'commuting_injections/verify_results.py'),
    ('data/03-atom-actions-verification_results.json', 'atom_actions/verification_results.json'),
    ('data/04-commuting-injections-verification.json', 'commuting_injections/verification.json'),
    ('figures/03-atom-actions-antichain_upsets.pdf', 'atom_actions/figures/antichain_upsets.pdf'),
    ('figures/03-atom-actions-antichain_upsets.png', 'atom_actions/figures/antichain_upsets.png'),
]
REVIEWS = {
    'review_new_actions_26e036956.md': '55d864059205571c3eeab0d7522c72eaf7ea064c692fa9672dd10a7adc8b0a37',
    'review_new_actions_26e036956.json': '9958f93dc6e3a807adc09829cee77b804d08818441ddd0f0abe50ea0a707f91c',
    'review_new_actions_26e036956.py': '6156d71193d185cfcc285dec4227139e49ed7d5a9a53d5bc11609599f8b4c562',
    'review_atom_injection_placement_27f200305.py': '7572470f16f175dee5ea94940fd3d50bbaf6d4a2ff237af2481b117a70bde3dc',
    'review_atom_injection_placement_27f200305.json': 'c530042f0b8ea4a27e1409f80526921af19d7b0382595df3c984650009597a5a',
    'review_atom_injection_placement_27f200305.md': None,
}


def ck(test, message):
    if not test:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def size_hash(data):
    return {'bytes': len(data), 'sha256': digest(data)}


def lines(data):
    return data.splitlines(keepends=True)


def span(data, start, end, description):
    ls = lines(data)
    ck(1 <= start <= end <= len(ls), 'invalid read span')
    return dict(start=start, end=end, coverage=description,
                **size_hash(b''.join(ls[start - 1:end])))


def tokens(text, pattern):
    return [{'value': m.group(1), 'line': text.count('\n', 0, m.start()) + 1}
            for m in re.finditer(pattern, text)]


def collect(root):
    def git(*args):
        return subprocess.check_output(['git', '-C', str(root), *args])

    def rev(name):
        return git('rev-parse', name).decode().strip()

    def blob(commit, path):
        data = git('show', commit + ':' + path)
        return data, dict(commit=commit, path=path, blob=rev(commit + ':' + path), **size_hash(data))

    parent = rev(COMMIT + '^')
    placement_parent = rev(PLACEMENT + '^')
    status = git('diff-tree', '--no-commit-id', '--name-status', '-r', COMMIT).decode().splitlines()
    ck(status == ['M\t' + HOST + x for x in ['README.md', 'article.pdf', 'article.tex']], 'change set')
    result = dict(schema=1, source_sha256=digest(Path(__file__).read_bytes()),
                  commit=COMMIT, parent=parent, arrival=ARRIVAL, placement=PLACEMENT,
                  placement_parent=placement_parent, manuscript_source_pin=SOURCE_PIN,
                  status=status, changed_files=[], archives=[], placements=[],
                  inherited_reviews=[], human_read_scope=[], source_routes=[])
    data_by_name = {}
    diff_by_name = {}
    for name in ['README.md', 'article.tex', 'article.pdf']:
        old, oldrec = blob(parent, HOST + name)
        new, newrec = blob(COMMIT, HOST + name)
        data_by_name[name] = (old, new)
        rec = dict(before=oldrec, after=newrec)
        ck(old == blob(SOURCE_PIN, HOST + name)[0] == blob(PLACEMENT, HOST + name)[0], 'old host binding')
        if name != 'article.pdf':
            df = git('diff', '--no-ext-diff', '--no-color', parent, COMMIT, '--', HOST + name)
            diff_by_name[name] = df
            rec['diff'] = dict(command='git diff --no-ext-diff --no-color PARENT COMMIT -- PATH',
                               lines=len(lines(df)), **size_hash(df))
            rec['hunks'] = re.findall(r'^@@ .*?@@.*$', df.decode(), re.M)
        else:
            rec['coverage'] = 'Bytes only; not rendered, read, rebuilt, or page-counted.'
        result['changed_files'].append(rec)

    members = {}
    source_tex = {}
    for archive, directory, prefix, expected in ARCHIVES:
        path = 'docs/incoming/' + archive
        raw, record = blob(ARRIVAL, path)
        ck(digest(raw) == expected, 'archive pin')
        ck(raw == blob(placement_parent, path)[0], 'archive parent preservation')
        record.update(prefix=prefix, regular_members=[], manifest_checks=[])
        z = zipfile.ZipFile(io.BytesIO(raw))
        for member in z.infolist():
            if member.is_dir():
                continue
            b = z.read(member)
            ck(member.filename not in members, 'duplicate archive member')
            members[member.filename] = b
            record['regular_members'].append(dict(path=member.filename, **size_hash(b),
                coverage='Byte authentication; no new scientific program execution.'))
        mp = directory + '/SHA256SUMS.txt'
        if mp in members:
            for row in members[mp].decode().splitlines():
                h, local = row.split(None, 1)
                member = directory + '/' + local.lstrip('*')
                ck(digest(members[member]) == h, 'ZIP manifest')
                record['manifest_checks'].append({'member': member, 'sha256': h})
        texname = directory + '/' + directory + '.tex'
        source_tex[prefix] = members[texname].decode()
        record['main_tex'] = dict(path=texname, lines=len(lines(members[texname])),
            labels=tokens(source_tex[prefix], r'\\label\{([^{}]+)\}'))
        result['archives'].append(record)
    ck(len(members) == 14, 'ZIP inventory')

    for target, member in PLACED:
        data, record = blob(COMMIT, HOST + target)
        ck(data == members[member], 'placement equality')
        ck(data == blob(PLACEMENT, HOST + target)[0] == blob(parent, HOST + target)[0], 'placement continuity')
        record['archive_member'] = member
        record['equal_at'] = [PLACEMENT, parent, COMMIT]
        result['placements'].append(record)
    ck(sum(r['bytes'] for r in result['placements']) == 228956, 'placement size')

    for name, h in REVIEWS.items():
        data, record = blob(COMMIT, WIP + name)
        if h is not None:
            ck(digest(data) == h, 'prior review pin')
        record['coverage'] = 'Full prose read' if name.endswith('.md') else 'Inert bytes only; never executed/imported'
        if name.endswith('.md'):
            record['read_spans'] = [span(data, 1, len(lines(data)), 'complete earlier bounded review')]
        result['inherited_reviews'].append(record)

    oldtex = data_by_name['article.tex'][0].decode()
    newtex = data_by_name['article.tex'][1].decode()
    oldlabels = tokens(oldtex, r'\\label\{([^{}]+)\}')
    labels = tokens(newtex, r'\\label\{([^{}]+)\}')
    labelmap = {r['value']: r['line'] for r in labels}
    ck(len(labelmap) == len(labels) == 284, 'label uniqueness/count')
    ck(len(oldlabels) == 146 and all(r['value'] in labelmap for r in oldlabels), 'old labels retained')
    ck(sum(r['value'].startswith('nee:aa:') for r in labels) == 73, 'aa labels')
    ck(sum(r['value'].startswith('nee:ci:') for r in labels) == 65, 'ci labels')
    for prefix, text in source_tex.items():
        for r in tokens(text, r'\\label\{([^{}]+)\}'):
            target = prefix + r['value']
            if prefix == 'nee:ci:' and r['value'] in ('eq:necklace', 'eq:infinitecount'):
                target = 'nee:aa:' + r['value']
            ck(target in labelmap, 'missing manuscript route ' + target)
            result['source_routes'].append(dict(source_prefix=prefix, source_label=r['value'],
                source_line=r['line'], target_label=target, target_line=labelmap[target],
                scope='Locator existence only; not a full clause-by-clause merge certification.'))
    ck(len(result['source_routes']) == 96, 'source locator count')

    refs = tokens(newtex, r'\\(?:[Cc]ref|ref|eqref|pageref|autoref)\*?\{([^{}]+)\}')
    for r in refs:
        ck(all(x.strip() in labelmap for x in r['value'].split(',')), 'unresolved local ref: ' + r['value'])
    bibs = tokens(newtex, r'\\bibitem(?:\[[^\]]*\])?\{([^{}]+)\}')
    bibmap = {r['value']: r['line'] for r in bibs}
    ck(len(bibmap) == len(bibs), 'bibliography uniqueness')
    citations = tokens(newtex, r'\\cite(?:\[[^\]]*\])*\{([^{}]+)\}')
    for r in citations:
        ck(all(x.strip() in bibmap for x in r['value'].split(',')), 'unresolved citation')
    result['locators'] = dict(old_labels=oldlabels, labels=labels, references=refs,
        bibliography=bibs, citations=citations,
        source_credit_lines=[dict(line=i, text=row, sha256=digest(row.encode()))
                            for i, row in enumerate(newtex.splitlines(), 1) if row.startswith('\\srcs{')],
        part_commands=tokens(newtex, r'\\part\{([^{}]+)\}'))
    ck(len(result['locators']['part_commands']) == 3, 'actual Parts')

    readme = data_by_name['README.md'][1].decode()
    tree = set(git('ls-tree', '-r', '--name-only', COMMIT).decode().splitlines())
    markdown_links = []
    for m in re.finditer(r'\[[^\]\n]+\]\(([^)\n]+)\)', readme):
        target = m.group(1)
        if re.match(r'[a-zA-Z]+:', target) or target.startswith('#'):
            status = 'external or anchor; not fetched'
            resolved = None
        else:
            path = target.split('#', 1)[0].strip('<>')
            resolved = posixpath.normpath(HOST + path)
            ck(resolved in tree, 'broken local README link ' + target)
            status = 'target file present at immutable commit; anchor not rendered'
        markdown_links.append(dict(line=readme.count('\n', 0, m.start()) + 1,
                                   target=target, resolved=resolved, status=status))
    result['markdown_links'] = markdown_links

    result['human_read_scope'].append(dict(kind='git textual diff', path=HOST + 'README.md',
        read_spans=[span(diff_by_name['README.md'], 1, len(lines(diff_by_name['README.md'])), 'complete guide diff')]))
    result['human_read_scope'].append(dict(kind='git textual diff', path=HOST + 'article.tex',
        read_spans=[span(diff_by_name['article.tex'], 1, 127, 'preamble/earlier-Part editorial changes and Part III opening')],
        remainder='Hashed; selected new-source spans below, not a full diff read.'))
    selections = [(217,253), (2409,2810), (2874,3265), (3919,4087),
                  (4628,4940), (5162,5384), (5623,5674)]
    result['human_read_scope'].append(dict(kind='immutable source', path=HOST+'article.tex',
        read_spans=[span(data_by_name['article.tex'][1], a, b, 'selected proof/interface/provenance read')
                    for a, b in selections]))
    message = git('show', '-s', '--format=%B', COMMIT)
    result['commit_message'] = dict(**size_hash(message),
        read_spans=[span(message, 1, len(lines(message)), 'complete author commit message; runs/builds are attributed only')])
    rule, ruler = blob(COMMIT, 'docs/incoming/README.md')
    ruler['read_spans'] = [span(rule, 414, 440, 'incoming retention rule; stronger task restrictions bar supplied execution')]
    result['standing_rule'] = ruler
    agent_paths = ['AGENTS.md', 'SetTheory/AGENTS.md', 'SetTheory/Cardinals/AGENTS.md',
                   'SetTheory/Cardinals/docs/AGENTS.md', 'SetTheory/Cardinals/docs/reports/AGENTS.md',
                   'SetTheory/Cardinals/docs/reports/ordinals-and-order-types/AGENTS.md', HOST+'AGENTS.md']
    result['applicable_agents_at_commit'] = [p for p in agent_paths if p in tree]
    ck(not result['applicable_agents_at_commit'], 'new applicable instructions require manual read')
    original = "No review of Part II's or Part III's manuscripts exists there."
    ck(original in readme.replace('\n', ' '), 'recorded incorrect phrase')
    result['finding'] = dict(id='R1', severity='provenance correction',
        path=HOST+'README.md', span=span(data_by_name['README.md'][1], 438, 439, 'incorrect provenance clause'),
        original=original, counterexample=WIP+'review_new_actions_26e036956.md',
        explanation='The named intake exists at this commit: full commuting proof read, selected atom interfaces; not full atom certification.',
        article_analogue='No equivalent no-review statement found; line 237 identifies older Part I review only.')
    result['scope_limits'] = [
        'Not a full mathematical certification of every new source proof or clause-preserving union.',
        'No archived/placed/prior/frozen scripts were executed or imported; no builds.',
        'Article PDFs and figures hash-only; external literature and priority not checked.',
        'Source routes establish label presence, not all source-to-merged-body equivalences.',
        'Finite presentation effectivity does not give a paid fixed-arity ordinary-integer compiler.',
    ]
    result['totals'] = dict(changed_paths=3, archives=2, members=14, manifest_entries=8,
        unchanged_placements=7, placement_bytes=228956, old_labels=146, current_labels=284,
        added_labels=138, source_label_routes=96, reference_commands=len(refs),
        reference_targets=sum(len(r['value'].split(',')) for r in refs),
        citation_commands=len(citations), citation_targets=sum(len(r['value'].split(',')) for r in citations),
        bibliography_entries=len(bibs), source_credit_lines=len(result['locators']['source_credit_lines']),
        guide_diff_lines=len(lines(diff_by_name['README.md'])),
        article_selected_lines=sum(b-a+1 for a,b in selections))
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', required=True)
    group = ap.add_mutually_exclusive_group(required=True)
    group.add_argument('--write')
    group.add_argument('--expect')
    args = ap.parse_args()
    receipt = collect(Path(args.root))
    if args.write:
        Path(args.write).write_text(json.dumps(receipt, indent=2, ensure_ascii=False) + '\n')
    else:
        ck(receipt == json.loads(Path(args.expect).read_text()), 'receipt mismatch')
    print(json.dumps({'status': 'PASS', 'totals': receipt['totals']}, sort_keys=True))


if __name__ == '__main__':
    main()
