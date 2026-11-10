"""Read-only inventory and whole-module metrics for the pinned draft ZIPs.

No code from the inspected files is executed. A checker candidacy heuristic
is used only for inventory; the minimum candidates were manually reviewed.
"""
from pathlib import Path
import ast
import csv
import gzip
import hashlib
import io
import json
import platform
import sys
import tokenize
import zipfile

ROOT = Path(__file__).resolve().parent.parent
OUT = Path(__file__).resolve().parent
IGNORED = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
           tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}

class StripDocstrings(ast.NodeTransformer):
    def clean(self, node):
        self.generic_visit(node)
        if (node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            node.body = node.body[1:]
        return node
    visit_Module = clean
    visit_FunctionDef = clean
    visit_AsyncFunctionDef = clean
    visit_ClassDef = clean

def tokens(source):
    return sum(t.type not in IGNORED
               for t in tokenize.generate_tokens(io.StringIO(source).readline))

def measure(raw):
    source = raw.decode('utf-8')
    tree = ast.fix_missing_locations(StripDocstrings().visit(ast.parse(source)))
    normal = (ast.unparse(tree) + '\n').encode('utf-8')
    return {'raw_bytes': len(raw), 'normalized_bytes': len(normal),
            'normalized_tokens': tokens(normal.decode('utf-8')),
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'gzip9_raw_bytes': len(gzip.compress(raw, compresslevel=9, mtime=0)),
            'gzip9_normalized_bytes': len(gzip.compress(normal, compresslevel=9, mtime=0)),
            'sha256': hashlib.sha256(raw).hexdigest()}

archives = []
sources = []
seen_archives = set()

def visit(raw, location, depth=0):
    digest = hashlib.sha256(raw).hexdigest()
    if digest in seen_archives:
        archives.append({'location': location, 'sha256': digest,
                         'size': len(raw), 'duplicate': True, 'depth': depth})
        return
    seen_archives.add(digest)
    archives.append({'location': location, 'sha256': digest,
                     'size': len(raw), 'duplicate': False, 'depth': depth})
    with zipfile.ZipFile(io.BytesIO(raw)) as z:
        for entry in z.infolist():
            loc = location + '!' + entry.filename
            if entry.filename.endswith('.zip'):
                visit(z.read(entry), loc, depth + 1)
            elif entry.filename.endswith('.py'):
                data = z.read(entry)
                try:
                    metrics = measure(data)
                except (UnicodeError, SyntaxError):
                    continue
                s = data.decode('utf-8')
                driver = 'ACCEPT' in s and ('open(0)' in s or 'stdin' in s)
                sources.append({'location': loc,
                                'archive_depth': depth,
                                'checker_driver_candidate': driver,
                                **metrics})

for archive in sorted((ROOT/'ProveIt/docs/drafts').glob('*.zip')):
    visit(archive.read_bytes(), archive.name)

candidates = [r for r in sources if r['checker_driver_candidate']]
unique = {}
for row in candidates:
    unique.setdefault(row['sha256'], row)
measures = ('normalized_bytes', 'normalized_tokens', 'ast_nodes',
            'raw_bytes', 'gzip9_raw_bytes', 'gzip9_normalized_bytes')
minimum = {key: min(r[key] for r in candidates) for key in measures}
attainers = {key: [r for r in unique.values() if r[key] == minimum[key]]
             for key in measures}
result = {'commit': '0300a290bedee5019c974291850b798378438b2e',
          'python': platform.python_version(), 'implementation': platform.python_implementation(),
          'top_level_archive_count': sum(x['depth'] == 0 for x in archives),
          'distinct_archive_count_including_embedded': len(seen_archives),
          'python_source_occurrences_in_distinct_archives': len(sources),
          'distinct_python_source_hashes': len({r['sha256'] for r in sources}),
          'checker_candidate_occurrences': len(candidates),
          'distinct_checker_candidate_hashes': len(unique),
          'coordinatewise_minimum': minimum,
          'minimum_attainers': attainers,
          'qualification': 'Checkers are driver-filtered candidates, not automatically certified. '
                           'Minimum-attaining candidates were manually inspected. Different programs attain minima. '
                           'AST winner and gzip winner use permissive openers relying on runtime exceptions.',
          'archives': archives, 'sources': sources}
(OUT/'frontier_metrics.json').write_text(json.dumps(result, indent=2)+'\n')
with (OUT/'checker_metrics.csv').open('w', newline='') as f:
    writer=csv.DictWriter(f, fieldnames=list(candidates[0]))
    writer.writeheader(); writer.writerows(candidates)
print(json.dumps({k:v for k,v in result.items() if k not in ('archives','sources','minimum_attainers')},indent=2))
for key, rows in attainers.items():
    print(key, [(r[key],r['location']) for r in rows])
