#!/usr/bin/env python3
"""External graph/tuple audit, independent degree certificate and isolated rebuild."""
import gzip
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

if sys.flags.optimize or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('isolated non-optimized Python required')
D = Path(__file__).resolve().parents[2]
REPO = D.parents[1]
candidate = D / 'research/ten-positive-80-original-kernel-variant'
source = D / 'research/ten-positive-unshift-t-finite/data/equation_qcube_V2.json'
original = D / 'candidates/free-j-polarized-positive/source/positive/coefficients/payloads'
prior_checker = D / 'reviews/compact44-symbolic-k-byte-independent-review/audit.py'
h = lambda b: hashlib.sha256(b).hexdigest()

def need(test, message):
    if not test:
        raise RuntimeError(message)

variant_path = candidate / 'equation.json'
build_path = candidate / 'build.py'
degree_script = candidate / 'verify_degree.py'
variant = json.loads(variant_path.read_bytes())
parent = json.loads(source.read_bytes())
need(h(source.read_bytes()) == 'fcc5e40f5d22320541ec2af5857725ceafaa69d0df36708ec60d6b9a40a71f01', 'parent hash')
need(variant['parent_source_sha256'] == h(source.read_bytes()), 'parent binding')
for key in ('source','witnesses','fixed_numerals','output','domain'):
    need(variant[key] == parent[key], 'parent field ' + key)
need(variant['domain'] == 'strictly positive integers' and len(variant['witnesses']) == 10 and len(set(variant['witnesses'])) == 10, 'domain/witness count')
need(variant['fixed_numerals'] == ['beta','K0','MC','MF'], 'fixed port order')
need(len(variant['source']) == variant['operations'] == 80, 'row count')

files = [source, variant_path, build_path, degree_script, prior_checker]
coefficient_data = {}
for name, expected in variant['coefficient_binding']['ports'].items():
    new = candidate / 'coefficients' / expected['file']
    old = original / expected['file']
    files += [new, old]
    new_compressed, old_compressed = new.read_bytes(), old.read_bytes()
    new_raw, old_raw = gzip.decompress(new_compressed), gzip.decompress(old_compressed)
    need(new_compressed == old_compressed and new_raw == old_raw, 'payload differs from original ' + name)
    need(new_raw and new_raw[-1] != 0, 'nonminimal encoding ' + name)
    need(h(new_compressed) == expected['gzip_sha256'] and h(new_raw) == expected['raw_sha256'], 'payload hashes ' + name)
    value = int.from_bytes(new_raw, 'little')
    need(value.bit_length() == expected['bits'] and value > 0, 'bit count ' + name)
    coefficient_data[name] = {'file':expected['file'], 'raw_sha256':h(new_raw), 'bytes':len(new_raw), 'bits':value.bit_length()}
need(set(coefficient_data) == {'beta','K0','MC','MF'}, 'port set')
need(coefficient_data['K0']['raw_sha256'] == 'c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e', 'original K')
before = {str(p):h(p.read_bytes()) for p in files}

# Independent straight-line census plus a modular degree certificate. Substitute
# every variable by the same indeterminate t and work over F_p. Nonzero leading
# coefficients at every row prove its degree exactly in F_p[t], while structural
# degrees give an integer multivariate upper bound. A nonzero degree-750 output
# after specialization proves the original integer polynomial has degree 750.
prime = 1000000007
known = {v:(1,1) for v in variant['witnesses']}
for name, details in variant['coefficient_binding']['ports'].items():
    raw = gzip.decompress((candidate / 'coefficients' / details['file']).read_bytes())
    known[name] = (0, int.from_bytes(raw, 'little') % prime)
    need(known[name][1] != 0, 'zero modular constant ' + name)
counts = {'+':0, '-':0, '*':0}
parents = {}
def operand(x):
    if type(x) is int:
        need(x % prime != 0, 'unsupported zero constant in degree certificate')
        return (0, x % prime)
    need(isinstance(x, str) and x in known, 'undefined operand')
    return known[x]
for row in variant['source']:
    need(isinstance(row,list) and len(row) == 4, 'bad row')
    name, op, left, right = row
    need(isinstance(name,str) and name not in known and op in counts, 'bad graph name/operator')
    a, b = operand(left), operand(right)
    if op == '*': degree, lc = a[0]+b[0], a[1]*b[1] % prime
    elif a[0] > b[0]: degree, lc = a
    elif a[0] < b[0]: degree, lc = b[0], (b[1] if op == '+' else -b[1]) % prime
    else: degree, lc = a[0], (a[1] + (b[1] if op == '+' else -b[1])) % prime
    need(lc != 0, 'leading cancellation at ' + name)
    known[name] = degree, lc
    parents[name] = [x for x in (left,right) if isinstance(x,str)]
    counts[op] += 1
need(counts == variant['operation_breakdown'] == {'+':18, '-':14, '*':48}, 'operation counts')
need(variant['output'] in parents and known[variant['output']] == (750,12396338), 'degree certificate')
need(variant['inherited_exact_degree'] == 750, 'degree metadata')
reachable, stack = set(), [variant['output']]
while stack:
    node = stack.pop()
    if node in parents and node not in reachable:
        reachable.add(node)
        stack.extend(parents[node])
need(len(reachable) == 80, 'dead operation rows')

degree_run = subprocess.run([sys.executable,'-I','-S','-B',str(degree_script)], cwd=REPO,
                            capture_output=True, text=True, timeout=120, check=True)
degree_report = json.loads(degree_run.stdout)
need(not degree_run.stderr and degree_report['status'] == 'PASS_MODULAR_DEGREE_WITNESS' and
     degree_report['upper_bound'] == 750 and degree_report['prime'] == prime and
     degree_report['diagonal_leading_coefficient_mod_prime'] == 12396338 and
     degree_report['equation_sha256'] == h(variant_path.read_bytes()), 'author degree script')
degree_opt = subprocess.run([sys.executable,'-O','-I','-S','-B',str(degree_script)], cwd=REPO,
                            capture_output=True, text=True, timeout=120)
need(degree_opt.returncode != 0 and 'optimized Python is not supported' in degree_opt.stderr,
     'author degree optimized run not rejected')

prior = subprocess.run([sys.executable,'-I','-S','-B',str(prior_checker)], cwd=REPO,
                       capture_output=True, text=True, timeout=120, check=True)
old_audit = json.loads(prior.stdout)
need(not prior.stderr and old_audit['status'] == 'PASS_EXTERNAL_K_RECIPE_INDEPENDENT_REVIEW', 'original recipe audit')
need(old_audit['raw_sha256'] == coefficient_data['K0']['raw_sha256'], 'reconstructed kernel mismatch')

# Copy the exact pinned inputs into an isolated matching tree; run the builder
# twice there and compare each output byte-for-byte with the published artifact.
with tempfile.TemporaryDirectory(prefix='original-k-80-review-') as tmp:
    root = Path(tmp)
    shadow = root / 'research/ten-positive-80-original-kernel-variant'
    shadow.mkdir(parents=True)
    (shadow / 'coefficients').mkdir()
    shadow_src = root / 'research/ten-positive-unshift-t-finite/data/equation_qcube_V2.json'
    shadow_src.parent.mkdir(parents=True)
    shutil.copyfile(source,shadow_src)
    shadow_payload = root / 'candidates/free-j-polarized-positive/source/positive/coefficients/payloads'
    shadow_payload.mkdir(parents=True)
    for details in variant['coefficient_binding']['ports'].values():
        shutil.copyfile(original / details['file'], shadow_payload / details['file'])
    shutil.copyfile(build_path, shadow / 'build.py')
    rows = []
    for _ in range(2):
        proc = subprocess.run([sys.executable,'-I','-S','-B',str(shadow/'build.py')], cwd=REPO,
                              capture_output=True, text=True, timeout=120, check=True)
        report = json.loads(proc.stdout)
        need(not proc.stderr and report['status'] == 'CANDIDATE_BUILT', 'builder run')
        need((shadow/'equation.json').read_bytes() == variant_path.read_bytes(), 'rebuilt JSON')
        for details in variant['coefficient_binding']['ports'].values():
            filename = details['file']
            need((shadow/'coefficients'/filename).read_bytes() == (candidate/'coefficients'/filename).read_bytes(), 'rebuilt ' + filename)
        rows.append(report)
    need(rows[0] == rows[1], 'nondeterministic builder output')
    optimized = subprocess.run([sys.executable,'-O','-I','-S','-B',str(shadow/'build.py')], cwd=REPO,
                               capture_output=True, text=True, timeout=120)
    need(optimized.returncode != 0 and 'optimized Python is not supported' in optimized.stderr, 'optimized run not rejected')
    original_source = shadow_src.read_bytes()
    shadow_src.write_bytes(original_source+b'\n')
    changed_source = subprocess.run([sys.executable,'-I','-S','-B',str(shadow/'build.py')], cwd=REPO,
                                    capture_output=True, text=True, timeout=120)
    need(changed_source.returncode != 0 and '80-row source changed' in changed_source.stderr, 'changed source not rejected')
    shadow_src.write_bytes(original_source)
    controls = {'optimized':optimized.returncode,'source':changed_source.returncode}
    for name, details in variant['coefficient_binding']['ports'].items():
        path = shadow_payload / details['file']
        original_payload = path.read_bytes()
        path.write_bytes(gzip.compress(gzip.decompress(original_payload)+b'\x01',mtime=0))
        changed = subprocess.run([sys.executable,'-I','-S','-B',str(shadow/'build.py')], cwd=REPO,
                                 capture_output=True, text=True, timeout=120)
        need(changed.returncode != 0 and ('payload mismatch: '+name) in changed.stderr, 'changed payload not rejected '+name)
        controls[name] = changed.returncode
        path.write_bytes(original_payload)

need(before == {str(p):h(p.read_bytes()) for p in files}, 'inputs changed during check')
print(json.dumps({'status':'PASS_EXTERNAL_GRAPH_TUPLE', 'input_sha256':before,
                  'port_data':coefficient_data, 'rows':80, 'reachable_rows':len(reachable),
                  'operation_counts':counts, 'degree_certificate':{'prime':prime, 'substitution':'all witnesses := t',
                  'degree':750, 'leading_coefficient_mod_prime':12396338, 'zero_leading_cancellations':0},
                  'author_degree_script':degree_report, 'author_degree_optimized_exit':degree_opt.returncode,
                  'original_kernel_recipe_review':old_audit, 'isolated_builder_runs':rows, 'rejection_controls':controls,
                  'scope':'external finite graph, degree, payload and reproducibility checks; no Lean/file binding, machine equivalence or iPRA endpoint'},
                 indent=2, sort_keys=True))
