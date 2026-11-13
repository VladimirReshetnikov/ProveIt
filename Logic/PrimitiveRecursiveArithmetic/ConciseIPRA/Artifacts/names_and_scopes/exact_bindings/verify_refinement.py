"""Check the new child-depth selector against the inherited exact interface."""
import ast
import concurrent.futures
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

HERE = Path(__file__).resolve().parent
BASE = HERE
CONFIGS = [('proper_bytes.py', 'proper_bytes'), ('proper_tokens.py', 'proper_tokens'), ('proper_nodes.py', 'proper_nodes'), ('proper_bytes_tuple.py', 'proper_bytes'), ('proper_expression.py', 'proper_bytes')]
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}

def measure(path):
    source = ast.unparse(ast.parse(path.read_text())) + '\n'
    return {'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(source).readline)), 'ast_nodes': len(list(ast.walk(ast.parse(source)))), 'normalized_bytes': len(source.encode()), 'sha256': hashlib.sha256(source.encode()).hexdigest()}

def run(job):
    profile, case, optimized = job
    p = subprocess.run([sys.executable, *(['-O'] if optimized else []), str(HERE / profile)], input=json.dumps(case['certificate']), text=True, capture_output=True, timeout=15)
    accepted = p.returncode == 0 and p.stdout == 'ACCEPT\n'
    return {'profile': profile, 'name': case['name'], 'optimized': optimized, 'expected': case['expected'], 'accepted': accepted}

def main():
    jobs = [(profile, case, opt) for profile, fixture in CONFIGS for case in json.loads((BASE / 'fixtures' / (fixture + '.json')).read_text())['cases'] for opt in (False, True)]
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        rows = list(pool.map(run, jobs))
    failures = [row for row in rows if row['expected'] != row['accepted']]
    receipt = {'python': sys.version, 'source': str(BASE), 'metrics': {p: measure(HERE / p) for p, _ in CONFIGS}, 'process_runs': len(rows), 'failures': failures, 'results': rows}
    (HERE / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'results'}, indent=2))
    if failures:
        raise SystemExit(1)

if __name__ == '__main__':
    main()
