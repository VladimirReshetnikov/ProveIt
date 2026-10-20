#!/usr/bin/env python3
"""Copy this completed review's owned files into the intake host; no execution."""
import hashlib,json,shutil
from pathlib import Path
REPO=Path('/home/codex/.codex/worktrees/ec20/Proofs')
HOST=REPO/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
BASE=Path('/tmp/zfc-intake188-opening');R=BASE/'review';E=BASE/'execution'
CODE=HOST/'code/intake188-fresh-k218';DATA=HOST/'data/intake188-fresh-k218'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    assert json.loads((R/'review.json').read_text())['status']=='FRESH_DIRECT_LEAVES_EVIDENCE_REVIEW_PASS'
    assert not CODE.exists() and not DATA.exists()
    pairs=[]
    for n in ('prepare.py','run.py','finalize_review.py','publish.py'):pairs.append((R/n,CODE/'actual-adapter'/n))
    pairs += [(R/'prepare_portable.py',CODE/'prepare.py'),(R/'run_portable.py',CODE/'run.py')]
    for n in ('prepare-portable.diff','run-portable.diff'):pairs.append((R/n,CODE/n))
    for n in ('source-review.md','review.json','reproduction.md'):pairs.append((R/n,DATA/n))
    pairs += [(E/'result.json',DATA/'actual.json'),(E/'plan.json',DATA/'plan.json'),(BASE/'extraction.json',DATA/'original-extraction.json'),(BASE/'portable-prepared/plan.json',DATA/'portable-preparation.json')]
    pairs += [(p,DATA/'history'/p.relative_to(R/'history')) for p in sorted((R/'history').rglob('*')) if p.is_file()]
    for sub in ('output','logs'):
        pairs += [(p,DATA/sub/p.relative_to(E/sub)) for p in sorted((E/sub).rglob('*')) if p.is_file()]
    for row in json.loads((E/'plan.json').read_text())['inputs']:
        p=Path(row['path']);assert h(p)==row['sha256']
        if E/'packet/portable' in p.parents:dest=CODE/'supplied'/p.relative_to(E/'packet/portable')
        elif E/'runtime-inputs' in p.parents:dest=CODE/'runtime-inputs'/p.relative_to(E/'runtime-inputs')
        else:dest=DATA/'input-baseline'/p.relative_to(E/'baseline')
        pairs.append((p,dest))
    assert len({str(t) for s,t in pairs})==len(pairs)
    rows=[]
    for s,t in pairs:
        t.parent.mkdir(parents=True,exist_ok=True);assert not t.exists();shutil.copyfile(s,t);assert s.read_bytes()==t.read_bytes()
        rows.append({'source':str(s),'target':str(t.relative_to(REPO)),'sha256':h(t),'size':t.stat().st_size})
    rec={'status':'EXACT_FRESH_EVIDENCE_COPY_PASS','scope':'Additive owned code/data only; supplied original payload unmodified; publication is packaging, not a proof replay.','files':rows,'total_bytes':sum(x['size'] for x in rows)}
    (DATA/'publication.json').write_text(json.dumps(rec,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'files_including_publication':len(rows)+1,'bytes':rec['total_bytes'],'publication_sha256':h(DATA/'publication.json')}))
if __name__=='__main__':main()
