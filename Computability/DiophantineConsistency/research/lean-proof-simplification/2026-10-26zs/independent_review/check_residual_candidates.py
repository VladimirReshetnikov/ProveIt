#!/usr/bin/env python3
"""Independent source/model audit. Does not invoke Lean or certify elaboration."""
from pathlib import Path
from collections import deque
import hashlib, json, shutil, subprocess, tempfile

def require(condition, message="Independent audit check failed"):
    """A failure guard that remains active under python -O and -OO."""
    if not condition:
        raise AssertionError(message)

# The failure path itself is exercised in every ordinary and optimized run.
try:
    require(False, "explicit failure guard negative control")
except AssertionError as error:
    if str(error) != "explicit failure guard negative control":
        raise RuntimeError("Failure guard raised an unexpected diagnostic") from error
else:
    raise RuntimeError("Failure guard negative control unexpectedly passed")

ROOT = Path(__file__).resolve().parents[1]
SRC_REL = Path('Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentPackingRank2011.lean')
SRC = ROOT / 'sources' / SRC_REL
source = SRC.read_text()
OUT = Path(__file__).parent
sha = lambda s: hashlib.sha256(s.encode()).hexdigest()
require(sha(source) == '614f47e52f31dfc199f98387e5c720f1ae51fb0725ce8d9f21223b540a30c546', "Audit check failed: sha(source) == '614f47e52f31dfc199f98387e5c720f1ae51fb0725ce8d9f21223b540a30c546'")

ends = {'fourBlocks_cast': '\nomit [NeZero N] in', 'rank_gt_twice_window': '\ntheorem fourBlocks_population'}
def extract(text, name):
    start = text.index('theorem ' + name + ' ')
    body = text.index(' := by\n', start) + len(' := by\n')
    end = text.index(ends[name], body)
    return text[start:body], text[body:end], body, end

def erase(text, names):
    for name in names:
        _, _, a, b = extract(text, name)
        text = text[:a] + '<PROOF BODY>\n' + text[b:]
    return text

variants = {
    'fourblocks_certificate': ('fourblocks_certificate.patch', ['fourBlocks_cast']),
    'rank_growth': ('rank_growth.patch', ['rank_gt_twice_window']),
    'combined': ('combined.patch', ['fourBlocks_cast', 'rank_gt_twice_window']),
}
result = {'scope': 'Source and independent integer models only; Lean was not executed.',
          'source_pin': '9d9d1123b39927d30363f1dcd53c23f0575c30ee',
          'source_sha256': sha(source),
          'failure_guards': 'Explicit require checks; failure path exercised; active under -O and -OO',
          'novelty_decisions': {
              'fourblocks_certificate': 'NARROW_CLIENT_DETOUR_REMOVAL_ONLY; existing certificate, no new algebra or casting mechanism',
              'rank_growth': 'EXCLUDE; prior zc report 349-369 and 570-582 reserves this normalized-growth mechanism',
              'combined': 'DO_NOT_RECOMMEND; includes excluded rank-growth edit'
          }, 'variants': {}}
for name, (patch_name, theorems) in variants.items():
    folder = ROOT / 'arithmetic_candidates' / name
    candidate = (folder / 'candidate/CurrentPackingRank2011.lean').read_text()
    require(erase(source, theorems) == erase(candidate, theorems), name)
    require([l for l in source.splitlines() if l.startswith('import ')] == [l for l in candidate.splitlines() if l.startswith('import ')], "Audit check failed: [l for l in source.splitlines() if l.startswith('import ')] == [l for l in candidate.splitlines() if l.startswith('import ')]")
    require(all(x not in candidate for x in ['sorry', 'admit', 'unsafe ', 'axiom ']), "Audit check failed: all(x not in candidate for x in ['sorry', 'admit', 'unsafe ', 'axiom '])")
    with tempfile.TemporaryDirectory(dir=OUT, prefix='patch-replay-') as td:
        target = Path(td) / SRC_REL
        target.parent.mkdir(parents=True)
        target.write_text(source)
        proc = subprocess.run(['patch', '--batch', '--fuzz=0', '-p1', '-i', str((folder / patch_name).resolve())], cwd=td, text=True, capture_output=True)
        require(proc.returncode == 0, proc.stdout + proc.stderr)
        require(target.read_text() == candidate, 'Audit check failed: target.read_text() == candidate')
    metrics = {}
    for theorem in theorems:
        h1, b1, _, _ = extract(source, theorem)
        h2, b2, _, _ = extract(candidate, theorem)
        require(h1 == h2, 'Audit check failed: h1 == h2')
        metrics[theorem] = {'header_unchanged': True, 'old_body_lines': len(b1.splitlines()), 'new_body_lines': len(b2.splitlines()), 'old_body_bytes': len(b1.encode()), 'new_body_bytes': len(b2.encode())}
    if 'fourBlocks_cast' in theorems:
        _, old, _, _ = extract(source, 'fourBlocks_cast')
        _, new, _, _ = extract(candidate, 'fourBlocks_cast')
        old_guard = old[old.index('push_cast [Nat.cast_sub'):old.index('    ring', old.index('push_cast [Nat.cast_sub'))]
        new_guard = new[new.index('push_cast [Nat.cast_sub'):new.index('  linear_combination')]
        require(''.join(old_guard.split()) == ''.join(new_guard.split()), "Audit check failed: ''.join(old_guard.split()) == ''.join(new_guard.split())")
        for required in ['have hJ := CurrentNativePacking2011.repunit_pos (N:=N)', 'have hHJ : 1 ≤ highPort*repunit width N := Nat.mul_pos highPort_pos hJ', 'have hCq : C ≤ q N := by omega', 'have hFq : F+1 ≤ q N := by omega', 'linear_combination -(q N : ℤ) * hb']:
            require(required in new, 'Audit check failed: required in new')
        metrics['fourBlocks_cast']['all_five_cast_sub_guards_unchanged'] = True
    if 'rank_gt_twice_window' in theorems:
        _, old, _, _ = extract(source, 'rank_gt_twice_window')
        _, new, _, _ = extract(candidate, 'rank_gt_twice_window')
        require(old[old.index('  have hn :='):] == new[new.index('  have hn :='):], "Audit check failed: old[old.index('  have hn :='):] == new[new.index('  have hn :='):]")
        metrics['rank_gt_twice_window']['final_bound_and_cast_chain_unchanged'] = True
    result['variants'][name] = {'patch_replay_exact': True, 'outside_target_bodies_byte_identical': True, 'imports_unchanged': True, 'candidate_sha256': sha(candidate), 'metrics': metrics}

# Exact coefficient arithmetic over Z[q,C,F,MC,MF,J,beta], independent of author's SymPy script.
N = 7
zero = (0,) * N
class P(dict):
    @staticmethod
    def coerce(x): return x if isinstance(x, P) else P({zero: x})
    def __add__(self, other):
        r = P(self)
        for m, c in P.coerce(other).items(): r[m] = r.get(m, 0) + c
        return P({m:c for m,c in r.items() if c})
    __radd__ = __add__
    def __neg__(self): return P({m:-c for m,c in self.items()})
    def __sub__(self, other): return self + -P.coerce(other)
    def __rsub__(self, other): return P.coerce(other) + -self
    def __mul__(self, other):
        r = P()
        for a, c in self.items():
            for b, d in P.coerce(other).items():
                m = tuple(x+y for x,y in zip(a,b)); r[m] = r.get(m,0) + c*d
        return P({m:c for m,c in r.items() if c})
    __rmul__ = __mul__
    def __pow__(self, n):
        r = P.coerce(1)
        for _ in range(n): r = r * self
        return r
variables = []
for i in range(N):
    m = list(zero); m[i] = 1; variables.append(P({tuple(m): 1}))
q,C,F,MC,MF,J,beta = variables
four = (C-1)+(MC*J+1)+q*(F+(MF*J-1))+q**2*(q-C)+q**3*(q-F-1)
rank = (q*(q-F)-C)*(q**2-1)+(MC+q*(MF+beta))*J
require(not four-rank-(-q*(beta*J+1-q)), 'Audit check failed: not four-rank-(-q*(beta*J+1-q))')
old_rank = ((q-1)*(q-F)+(q-F-C))*(q**2-1)+(MC+q*(MF+beta))*J
require(not old_rank-rank, 'Audit check failed: not old_rank-rank')
require(not old_rank-four-q*(beta*J-(q-1)), 'Audit check failed: not old_rank-four-q*(beta*J-(q-1))')
result['polynomial_identity'] = {'method': 'Independent exact integer coefficient dictionaries, not SymPy', 'fourBlocks_minus_rank': '-q * (beta * J + 1 - q)', 'existing_packing_four_block_same_polynomial': True}

sample_count = 0
for b in range(1,7):
    for j in range(1,5):
        Q = b*j+1
        for c in range(1,Q):
            for f in range(Q-c):
                for mc in range(3):
                    for mf in range(1,4):
                        require(1 <= c and 1 <= mf*j and c <= Q and f <= Q and 1 <= Q-f, 'Audit check failed: 1 <= c and 1 <= mf*j and c <= Q and f <= Q and 1 <= Q-f')
                        v = (c-1)+(mc*j+1)+Q*(f+(mf*j-1))+Q**2*(Q-c)+Q**3*(Q-f-1)
                        r = (Q*(Q-f)-c)*(Q**2-1)+(mc+Q*(mf+b))*j
                        require(v == r, 'Audit check failed: v == r')
                        sample_count += 1
result['bounded_natural_model'] = {'guarded_cases': sample_count, 'status': 'PASS, finite samples are not a proof'}
# Deliberately violated high-port guard. This is outside actual theorem hypotheses/definitions.
b,j,Q,c,f,mc,mf = 3,1,4,1,0,0,0
sub = lambda x,y: max(0,x-y)
v = sub(c,1)+(mc*j+1)+Q*(f+sub(mf*j,1))+Q**2*sub(Q,c)+Q**3*sub(sub(Q,f),1)
r = (Q*(Q-f)-c)*(Q**2-1)+(mc+Q*(mf+b))*j
require(v != r, 'Audit check failed: v != r')
result['negative_guard_control'] = {'guard_violated': '1 <= MF*J', 'fourBlocks_nat': v, 'rank_int': r, 'status': 'Mismatch expected and observed'}
for u in range(513):
    require(2*u <= 3*u < 2**(3*u), 'Audit check failed: 2*u <= 3*u < 2**(3*u)')
    require((2**u)**3 == 2**(3*u), 'Audit check failed: (2**u)**3 == 2**(3*u)')
result['rank_growth_model'] = {'tested_u': '0 through 512 inclusive', 'status': 'PASS, finite samples are not a proof', 'general_reason': 'For every natural u, 2*u <= 3*u; Nat.lt_two_pow_self at 3*u gives 3*u < 2^(3*u).'}

# Read only local dependency source. Existing paths establish tactic availability evidence.
leanroot = ROOT / 'sources/Computability/DiophantineConsistency/Lean'
queue = deque([('DiophantineConsistency.CurrentPackingRank2011', [])])
seen = set(); paths = {}; missing = []
wanted = {'Mathlib.Tactic.LinearCombination', 'Mathlib.Tactic', 'DiophantineConsistency.NativeSourceMask'}
while queue:
    module, path = queue.popleft(); path = path + [module]
    if module in seen: continue
    seen.add(module)
    if module in wanted: paths[module] = path
    if module.startswith('Mathlib'): continue
    file = leanroot.joinpath(*module.split('.')).with_suffix('.lean')
    if not file.exists(): missing.append(module); continue
    for line in file.read_text().splitlines():
        if line.startswith('import '):
            for imported in line.split()[1:]: queue.append((imported, path))
require('Mathlib.Tactic' in paths, "Audit check failed: 'Mathlib.Tactic' in paths")
require('DiophantineConsistency.NativeSourceMask' in paths, "Audit check failed: 'DiophantineConsistency.NativeSourceMask' in paths")
result['dependency_evidence'] = {'existing_import_paths': paths, 'source_files_missing_in_selective_mirror': missing, 'new_import_edges': 0, 'new_helpers': 0, 'new_cycle_possible_from_patch': False}
result['verification_limits'] = {'lean_executable': shutil.which('lean'), 'lake_executable': shutil.which('lake'), 'Lean_elaboration': 'NOT RUN', 'Lean_kernel': 'NOT RUN', 'downstream_build': 'NOT RUN', 'timing_or_proof_term_improvement': 'NOT MEASURED'}
(OUT / 'RESIDUAL_CANDIDATE_CHECKS.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
