#!/usr/bin/env python3
"""Exact local-edit and bounded arithmetic replay. This does not invoke Lean."""
from pathlib import Path
import difflib, hashlib, json
R = Path(__file__).resolve().parents[2]
D = Path(__file__).resolve().parent

def require(ok, message):
    if not ok:
        raise ValueError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def pell_y(a, n):
    x, y = 0, 1
    for _ in range(n):
        x, y = y, 2*a*y-x
    return x

def check():
    m = json.loads((D/'METRICS.json').read_text())
    p = R/'sources'/m['source_path']
    data = p.read_bytes()
    require(digest(data) == m['source_sha256'], 'Source SHA256 mismatch')
    require(hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
            == m['source_git_blob'], 'Source Git blob mismatch')
    s = data.decode()
    require(s.count(m['old_fragment']) == 1, 'Original fragment not unique')
    require(m['new_fragment'] ==
            '  have hKr : r+1 < K := lt_yn_of_two_le hP (by omega)\n',
            'Unexpected candidate proof')
    t = s.replace(m['old_fragment'], m['new_fragment'], 1)
    require((D/'NativeOuterSeedConstruction.lean').read_text() == t,
            'Candidate differs outside the exact replacement')
    require(digest(t.encode()) == m['new_sha256'], 'Candidate SHA256 mismatch')
    expected = ''.join(difflib.unified_diff(s.splitlines(True),t.splitlines(True),
        fromfile='a/'+m['source_path'],tofile='b/'+m['source_path']))
    require((D/'candidate.patch').read_text() == expected, 'Patch mismatch')
    for key, value in [('old_fragment_lines',len(m['old_fragment'].splitlines())),
                       ('new_fragment_lines',len(m['new_fragment'].splitlines())),
                       ('old_module_lines',len(s.splitlines())),
                       ('new_module_lines',len(t.splitlines()))]:
        require(m[key] == value, 'Line count mismatch: '+key)
    # Exact surrounding source facts, not a Lean elaboration test.
    for fragment in ['obtain ⟨hσ,hr,hsize⟩ := population_sizes hu hR hpop',
                     'let K := yn hP (r+1)',
                     'have hP : 1 < P := by dsimp [P]; omega',
                     'have hkR : R+1 < k := by dsimp [k]; omega']:
        require(fragment in s, 'Missing surrounding proof fact: '+fragment)
    helper = R/'dependencies/Computability/HilbertTenthProblem/Lean/Diophantine/Common/PellMod.lean'
    h = helper.read_text()
    require('variable {a : ℕ} (a1 : 1 < a)' in h, 'Pell helper base guard missing')
    require('theorem lt_yn_of_two_le {n : ℕ} (hn : 2 ≤ n) : n < yn a1 n := by' in h,
            'Pell helper signature mismatch')
    count = 0
    for a in range(2, 33):
        for n in range(2, 65):
            require(n < pell_y(a,n), 'Bounded strict-index inequality failed')
            count += 1
    controls = [{'case':'index zero', 'a':2, 'n':0},
                {'case':'index one', 'a':2, 'n':1},
                {'case':'base one', 'a':1, 'n':2}]
    for c in controls:
        c['y'] = pell_y(c['a'],c['n'])
        require(not(c['n'] < c['y']), 'Negative domain control unexpectedly strict')
    return {'status':'PASS_SOURCE_AND_BOUNDED_ARITHMETIC_ONLY',
            'source_sha256':m['source_sha256'], 'candidate_sha256':m['new_sha256'],
            'local_fragment_lines':[m['old_fragment_lines'],m['new_fragment_lines']],
            'module_lines':[m['old_module_lines'],m['new_module_lines']],
            'bounded_cases':count, 'negative_domain_controls':controls,
            'source_edit':'One exact local proof replacement; all other bytes unchanged',
            'Lean_elaboration':'NOT_RUN', 'kernel_verification':False}

if __name__ == '__main__':
    print(json.dumps(check(),indent=2))
