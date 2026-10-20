#!/usr/bin/env python3
import hashlib,json,shutil
from pathlib import Path
REPO=Path('/home/codex/.codex/worktrees/ec20/Proofs');HOST=REPO/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels';B=Path('/tmp/zfc-intake189-opening');R=B/'review';E=B/'execution';C=HOST/'code/intake189-fresh-state-search';D=HOST/'data/intake189-fresh-state-search'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    assert json.loads((R/'review.json').read_text())['status']=='SELECTED_STATERESEARCH_LEAVES_REVIEW_PASS'
    assert not C.exists() and not D.exists();pairs=[]
    for n in ('prepare.py','run.py','direct.py','finalize.py','publish.py'):pairs.append((R/n,C/'actual-adapter'/n))
    pairs += [(R/'prepare_portable.py',C/'prepare.py'),(R/'run_portable.py',C/'run.py'),(R/'direct.py',C/'direct.py')]
    for n in ('prepare-portable.diff','run-portable.diff'):pairs.append((R/n,C/n))
    for n in ('notes.md','review.json','reproduction.md','portable-review.json'):pairs.append((R/n,D/n))
    pairs += [(E/'result.json',D/'actual.json'),(E/'plan.json',D/'plan.json'),(B/'portable-prepared/plan.json',D/'portable-preparation.json')]
    for sub in ('output','logs'):
        pairs += [(p,D/sub/p.relative_to(E/sub)) for p in sorted((E/sub).rglob('*')) if p.is_file()]
    for p in sorted((E/'runtime-inputs').rglob('*')):
        if p.is_file():pairs.append((p,C/'runtime-inputs'/p.relative_to(E/'runtime-inputs')))
    for n in ('replay.py','check_source_closure.py'):pairs.append((E/'packet/verification'/n,C/'supplied'/n))
    for p in sorted((E/'packet/machines').rglob('*')):
        if p.is_file() and p.name!='manifest.json':pairs.append((p,D/'input-machines'/p.relative_to(E/'packet/machines')))
    for n in ('k219.native.tm','sites219.json'):pairs.append((E/'parent219/machine'/n,D/'input-parent219'/n))
    assert len({str(t)for s,t in pairs})==len(pairs)
    rows=[]
    for s,t in pairs:
        t.parent.mkdir(parents=True,exist_ok=True);assert not t.exists();shutil.copyfile(s,t);assert s.read_bytes()==t.read_bytes()
        rows.append({'source':str(s),'target':str(t.relative_to(REPO)),'sha256':h(t),'size':t.stat().st_size})
    (D/'publication.json').write_text(json.dumps({'status':'EXACT_SELECTED_FRESH_EVIDENCE_COPY_PASS','files':rows,'scope':'Owned additive publication; no wrapper, manifest, ancestor, or proof-assistant replay.'},indent=2)+'\n')
    print(json.dumps({'files':len(rows)+1,'bytes':sum(x['size']for x in rows),'publication_sha256':h(D/'publication.json')}))
if __name__=='__main__':main()
