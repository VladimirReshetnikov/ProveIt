#!/usr/bin/env python3
"""Own literal-data/provenance review. Imports no submitted code, runs no machine."""
from pathlib import Path
import hashlib, json

D = Path(__file__).resolve().parent
A = Path('/tmp/zfc-intake192/review-upstream/extracted/K217_Dominated_Continuation_2026-10-20')
P = Path('/tmp/zfc-intake191/K218_Dominated_Rho8_2026-10-20/K218_Dominated_Rho8_2026-10-20')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

def table(p):
    result = {}
    for line in p.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, move, target = line.split()
        k = int(q), int(b)
        assert k not in result
        result[k] = int(w), move, int(target)
    return result

parent = table(P/'binary/machine/k218.native.tm')
unfolded = table(A/'machine/unfolded218.native.tm')
final = table(A/'machine/k217.native.tm')
compact = table(A/'machine/k217.tm')
assert len(final) == len(compact) == 434
assert {q for q,b in parent} - {q for q,b in final} == {400}
assert not ({q for q,b in final} - {q for q,b in parent})
delta = [{'state':q, 'read':b, 'old':parent[q,b], 'new':row}
         for (q,b),row in final.items() if row != parent[q,b]]
assert len(delta) == 9
assert {k for k in final if final[k] != unfolded[k]} == {(69,0),(224,0)}
assert [(k,v) for k,v in unfolded.items() if v[2] == 69] == [((53,1),(1,'R',69))]
assert [(k,v) for k,v in unfolded.items() if v[2] == 400] == [((224,0),(0,'R',400))]
assert unfolded[69,1] == unfolded[400,1] == final[69,1] == (1,'R',31)
assert final[69,0] == (0,'L',213)
assert final[213,0] == (0,'R',92) and final[213,1] == (1,'R',90)
assert final[92,0] == (0,'R',104) and final[90,0] == (0,'R',105)
phi = {int(k):v for k,v in json.loads((A/'machine/canonicalization.json').read_text())['native_to_canonical'].items()}
assert phi[0] == 0 and phi[254] == 217
assert {phi[q] for q,b in final} == set(range(217))
assert {(phi[q],b):(w,m,phi[t]) for (q,b),(w,m,t) in final.items()} == compact
old = json.loads((P/'source/sites218.json').read_text())
new = json.loads((A/'machine/sites217.json').read_text())
assert len(old) == len(new) == 4751
assert [x[1:] for x in old] == [x[1:] for x in new]
assert sum(x[0] != y[0] for x,y in zip(old,new)) == 94
assert len(new) + sum(x[1] == 'CD' for x in new) == 6176

read_files = ['README.md','report.tex','sections/result.tex','sections/construction.tex',
              'sections/theory.tex','sections/verification.tex','sections/reproduction.tex',
              'provenance/ATTRIBUTION.md','provenance/theory_review.md',
              'provenance/source_fold_review.md','code/reconstruct217.py',
              'code/audit_source_fold.py','code/audit_blank.py','code/check_joint_fold.py','verify.py']
pins = {str(A/f): sha(A/f) for f in read_files}
for p in [A/'machine/k217.native.tm', A/'machine/k217.tm', A/'machine/sites217.json',
          A/'machine/unfolded218.native.tm', A/'parent/K218_Dominated_Rho8_2026-10-20.zip',
          P/'source/sites218.json', P/'binary/machine/k218.native.tm',
          Path('/tmp/zfc-intake191-source149-second-peer/review.json')]:
    pins[str(p)] = sha(p)
out = {
    'status':'INDEPENDENT_ORDINARY_PROOF_AND_SOURCE_REVIEW_CLEAN',
    'reviewer':'drop_contract',
    'role':'Second independent reader of this new217 ordinary argument and supplied source. Earlier independent reviewer of inherited Source149 calibration; author of unrelated earlier searches, not this construction.',
    'arrival':'8a1796545e',
    'pins':pins,
    'literal_checks':{'retained_row_changes':delta,'removed_state':400,'states':217,'rows':434,
        'whole_primitive_word_equal':True,'primitive_occurrences':4751,
        'changed_source_addresses':94,'guarded_cases':6176,
        'unique_written_marker_entries':True,'canonical_bijection':True},
    'ordinary_findings':[
        'Three closed halt-free rotations preserve all-input source behavior; exact guarded CFG comparison, rather than closure or leaf census alone, establishes ordinal successor equality.',
        'Updated expected decoder role relation includes the changed child at every stage, avoiding a weak reachability-only check.',
        'The two written origin markers are established by the only incoming rows on arbitrary initial tapes. The read-zero selector consumes only the current zero and left marker, preserving both; read-one agrees directly.',
        'Positive one/three-step whole-tape blocks and determinism yield both halting directions from state0. No arbitrary initial merged-state assertion is needed.',
        'Dominated U<=A calibration is inherited from the separately reviewed149 certificate and compiler; zero alias, universal numeric instantiation, gates, cleanup counts and cofinal candidate padding remain intact.',
        'Exact new-table quantified runtime and full blank frame are separate necessary premises, delegated to root fresh checks, not inferred from decoder binding.'
    ],
    'publication_precision':[
        'audit_blank --directory machine independently computes312617 transitions and sparse/dense/canonical complete support; absent validation/startup.json means freshly compared stored trace rows is0. Do not promote the delivered historical312617 stored-event field to a new check.',
        'Ordinary proof formalizable in ZFC with inherited native-calculus calibration; no new compiled exact-table Lean/Rocq, internal PA endpoint, unconditional nonhalting, or minimality claim.'
    ],
    'scope_exclusions':['No supplied script invocation','No candidate simulation or compiler','No full numeric transition-table appendix prose read; literal table data checked separately','No reproof of all inherited foundational calibration','No review of new root actual execution yet'],
    'metadata_code':{'path':str(Path(__file__).resolve()),'sha256':sha(Path(__file__).resolve())}
}
(D/'review.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'receipt':str(D/'review.json'),'sha256':sha(D/'review.json')},indent=2))
