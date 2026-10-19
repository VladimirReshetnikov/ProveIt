#!/usr/bin/env python3
"""Screen single neutral table changes, recomputing caller invariants.

First changes one literal transition using the all-tape neutral catalogue;
then derives fresh inductive windows and seeks a fold involving the old
target control. Discovery only: separately certify every returned candidate.
"""
from pathlib import Path
from collections import Counter
import hashlib,json,re,subprocess,time
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]/'baseline/zfc_composed237_old.tm'
table={}
for line in BASE.read_text().splitlines():
    if not line or line.startswith('#'):continue
    q,b,w,d,z=line.split();table[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(z))
def emit(path,T):
    path.write_text('#! start 95\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n' for (q,b),(w,d,z) in sorted(T.items())))
entries=[];out=dict(status='RUNNING',cases=entries,baseline_sha256=hashlib.sha256(BASE.read_bytes()).hexdigest(),scope='one all-tape-neutral row followed by a fresh-invariant direct fold involving its original target; radius5 and old/new cap65')
started=time.monotonic()
for line in (HERE/'neutral_alltape5.txt').read_text().splitlines():
    q,b,w,d,z,cap=map(int,line.split());focus=table[q,b][2]
    if focus in (95,254) or focus==z:continue
    patch=(q,b,w,d,z);modified=table|{(q,b):(w,d,z)}
    emit(HERE/'current_plateau.tm',modified)
    run=subprocess.run([str(HERE/'fold_after_redirect'),str(HERE/'current_plateau.tm'),'5','65',str(focus)],capture_output=True,text=True,check=True)
    match=re.search(r'FINISHED pairs (\d+) rowchecks (\d+) contexttests (\d+) candidates (\d+) seconds ([0-9.e+-]+)',run.stderr)
    assert match,run.stderr
    pairs,rows,contexts,candidates=map(int,match.groups()[:4])
    rec=dict(patch=patch,focus=focus,pairs=pairs,rowchecks=rows,contexttests=contexts,candidates=candidates,seconds=float(match.group(5)),output=run.stdout)
    entries.append(rec)
    if candidates:
        emit(HERE/f'plateau_survivor{len(entries)}.tm',modified)
        print('SURVIVOR',rec,flush=True)
    if len(entries)%30==0:
        out.update(elapsed_seconds=time.monotonic()-started)
        (HERE/'neutral_plateau_scan.json').write_text(json.dumps(out,indent=2)+'\n')
        print('SCREENED',len(entries),'candidates',sum(x['candidates'] for x in entries),'seconds',round(time.monotonic()-started,2),flush=True)
out.update(status='SCOPED_SEARCH_COMPLETE',case_count=len(entries),elapsed_seconds=time.monotonic()-started,
           total_pairs=sum(x['pairs'] for x in entries),total_rowchecks=sum(x['rowchecks'] for x in entries),
           total_contexttests=sum(x['contexttests'] for x in entries),candidates=sum(x['candidates'] for x in entries))
(HERE/'neutral_plateau_scan.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='cases'},indent=2),flush=True)
