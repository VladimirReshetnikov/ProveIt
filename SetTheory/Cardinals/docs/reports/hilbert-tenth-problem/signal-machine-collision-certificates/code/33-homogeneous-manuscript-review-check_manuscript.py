#!/usr/bin/env python3
"""Fresh, read-only source/PDF binding and literal transcription checker.

No scientific source is imported or executed. No arithmetic DAG is evaluated.
The program reads source text/JSON as inert data and writes only this dossier.
"""
from pathlib import Path
from collections import Counter
import hashlib
import json
import re
import stat

R = Path('/workspace/shared/report63-homogeneous-realization-release-20261004')
B = Path('/workspace/shared/report63-build-d-20261004')
O = Path('/workspace/shared/report63-manuscript-independent-review-20261004')

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def snapshot():
    paths = []
    for name in ('science', 'audits', 'dependencies', 'manuscript'):
        root = R / name
        paths += [root, *root.rglob('*')]
    paths += [R / name for name in ('Report63.tex', 'Report63.pdf', 'INPUT_PINS.json')]
    result = {}
    for path in sorted(paths):
        s = path.lstat()
        assert not path.is_symlink(), path
        item = dict(mode=stat.S_IMODE(s.st_mode), mtime_ns=s.st_mtime_ns,
                    ctime_ns=s.st_ctime_ns, type='dir' if path.is_dir() else 'file')
        if path.is_file():
            item.update(size=s.st_size, sha256=sha(path))
        result[str(path.relative_to(R))] = item
    return result

before = snapshot()
checks = []
def check(name, truth):
    checks.append({'name': name, 'pass': bool(truth)})
    if not truth:
        raise AssertionError(name)

pins = json.loads((R / 'manuscript/MANUSCRIPT_PINS.json').read_text())
check('ten modular TeX files', len(pins) == 10)
check('trusted manuscript pin map', sha(R / 'manuscript/MANUSCRIPT_PINS.json') ==
      '8dbeb0e7bdcbf949ebba9a699ab262dbb84b0111d9bb60d85c4c2a69aa10cbf1')
for name, digest in pins.items():
    check('modular pin ' + name, sha(R / 'manuscript' / name) == digest)
standalone = (R / 'Report63.tex').read_text()
check('trusted standalone pin', sha(R / 'Report63.tex') ==
      '232bac78b073aa9b3896aa1dade2a5f6372a000240ec67e9923dc6287555eb65')
main = (R / 'manuscript/Report63.tex').read_text()
flat = re.sub(r'\\input\{([^{}]+)\}\n',
              lambda m: (R / 'manuscript' / m.group(1)).read_text(), main)
check('independent modular flattening is byte-identical text', flat == standalone)
check('standalone has no external input', r'\input{' not in standalone)

expected_pdf = 'eb8d4d7c0cc0c98a7b706efe5e262d6b17699e21be7976957725f836420ad3ed'
check('trusted d PDF pin', sha(B / 'Report63.pdf') == expected_pdf)
check('release PDF is exact d PDF', sha(R / 'Report63.pdf') == expected_pdf)
receipt = json.loads((B / 'BUILD_RECEIPT.json').read_text())
check('d receipt matches manuscript pins', receipt['manuscript_pins'] == pins)
check('d receipt binds exact standalone', receipt['standalone_sha256'] == sha(R / 'Report63.tex'))
check('d receipt binds exact PDF', receipt['pdf_sha256'] == expected_pdf)
check('d receipt states 18 pages', receipt['page_count'] == 18)

dagtext = (R / 'manuscript/dag.tex').read_text()
signed = json.loads((R / 'science/frozen-proof/CERTIFICATE_DAG_SIGNED.json').read_text())
positive = json.loads((R / 'science/frozen-proof/CERTIFICATE_DAG_POSITIVE.json').read_text())

def normalize(token):
    token = re.sub(r'_\{([0-9]+)\}', r'\1', str(token).strip())
    if re.fullmatch(r'v[0-9]+', token):
        return 'v' + str(int(token[1:]))
    if re.fullmatch(r'[0-9]+', token):
        return int(token)
    return token

tabletext = dagtext.split(r'\begin{tabular}',1)[1].split(r'\end{tabular}',1)[0]
cell_matches = re.findall(r'\$v_\{([0-9]+)\}=([^$]+)\$', tabletext)
check('exactly 48 printed node definitions', len(cell_matches) == 48)
printed_order = [int(number) for number, expression in cell_matches]
check('left column 1 to 24 then right column 25 to 48',
      printed_order == [value for n in range(1,25) for value in (n,n+24)])
parsed = {}
for number, expression in cell_matches:
    pieces = re.split(r'(\\cdot|\+|-)', expression)
    check('binary printed expression ' + number, len(pieces) == 3)
    left, operation, right = pieces
    parsed['v' + str(int(number))] = dict(
        id='v' + str(int(number)), op={r'\cdot':'mul','+':'add','-':'sub'}[operation],
        left=normalize(left), right=normalize(right))
check('printed node identifiers unique', len(parsed) == 48)
for node in signed['nodes']:
    normalized = {key: normalize(value) if key != 'op' else value for key,value in node.items()}
    check('signed literal node ' + node['id'], parsed[normalize(node['id'])] == normalized)
check('signed output declared in Appendix A', '$v_{48}=F$' in dagtext and signed['output'] == 'v48')

difference_matches = re.findall(r'k_\{([123][123])\}=a_\{([123][123])\}-c_\{([123][123])\}', dagtext)
check('exactly nine printed positive-input differences', len(difference_matches) == 9)
for index, (k,a,c) in enumerate(difference_matches):
    wanted = {'id':'k'+k, 'op':'sub', 'left':'a'+a, 'right':'c'+c}
    check('positive literal difference ' + str(index+1), positive['nodes'][index] == wanted and k==a==c)

def shifted(token):
    if isinstance(token, str) and re.fullmatch(r'v[0-9]+', token):
        return 'v' + str(int(token[1:]) + 9)
    return token

for index, node in enumerate(signed['nodes']):
    wanted = {key: shifted(value) if key != 'op' else value for key,value in node.items()}
    check('positive node-renamed suffix ' + str(index+1), positive['nodes'][index+9] == wanted)
check('positive output is renamed signed output', positive['output'] == shifted(signed['output']))
for name, dag, expected in [('signed',signed,{'mul':26,'add':11,'sub':11}),
                             ('positive',positive,{'mul':26,'add':11,'sub':20})]:
    check(name + ' literal operation multiset', dict(Counter(n['op'] for n in dag['nodes'])) == expected)
    check(name + ' total and declared map', sum(expected.values()) == dag['total_operations'] and dag['operations'] == expected)
    check(name + ' eight positive witnesses', dag['positive_witnesses'] == ['g1','g2','g3','h1','h2','h3','b','d'])

labels = re.findall(r'\\label\{([^}]+)\}', standalone)
refs = re.findall(r'\\(?:eqref|ref)\{([^}]+)\}', standalone)
check('no duplicate TeX labels', len(labels) == len(set(labels)))
check('all TeX references resolve in source', set(refs).issubset(set(labels)))
check('no layout warnings in final TeX log', not re.search(r'Overfull|Underfull|undefined|multiply defined', (B/'Report63.log').read_text()))
text = (O/'Report63.txt').read_text()
pages = text.split('\f')
check('independent extracted text has 18 pages', len(pages) == 19 and pages[-1] == '')
for index, page in enumerate(pages[:-1], 1):
    check('page footer ' + str(index), page.strip().splitlines()[-1].strip() == str(index))
check('no unresolved reference marks in extracted text', '??' not in text)
rasters = sorted((O/'pages').glob('page-*.png'))
check('18 independently rendered PNG pages', len(rasters) == 18)
for line in (O/'SOURCE_PRESERVATION_BEFORE.sha256').read_text().splitlines():
    digest, name = line.split('  ', 1)
    check('initial source byte preservation ' + name, sha(R/name) == digest)
after = snapshot()
check('source and final PDF metadata preserved during checker', before == after)
report = dict(status='PASS', scope='Literal manuscript transcription and artifact binding; no mathematical proof or simulation',
              source_sha256=sha(R/'Report63.tex'), manuscript_pinmap_sha256=sha(R/'manuscript/MANUSCRIPT_PINS.json'),
              pdf_sha256=expected_pdf, signed_nodes=48, positive_prefix_nodes=9, positive_suffix_nodes=48,
              assertion_count=len(checks), assertions=checks,
              raster_pins={p.name:sha(p) for p in rasters}, page_count=18,
              limitations=['Read-only textual comparison, not proof-assistant formalization',
                           'No author or upstream mathematical program, simulator, saved physical schedule, or Lean executed',
                           'No claim that automated text checks establish visual quality',
                           'Access time is excluded from preservation comparison'])
(O/'PRESERVATION_BEFORE.json').write_text(json.dumps(before,indent=2,sort_keys=True)+'\n')
(O/'PRESERVATION_AFTER.json').write_text(json.dumps(after,indent=2,sort_keys=True)+'\n')
(O/'STATIC_REPORT.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print(json.dumps({key:report[key] for key in ('status','assertion_count','signed_nodes','positive_prefix_nodes','positive_suffix_nodes','page_count','pdf_sha256')}))
