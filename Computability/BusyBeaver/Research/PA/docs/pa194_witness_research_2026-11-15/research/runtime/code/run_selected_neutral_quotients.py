#!/usr/bin/env python3
"""Heuristic neutral-row/quotient nominations for AX readers and engine boxes."""
from pathlib import Path
import argparse,json,subprocess,time
p=argparse.ArgumentParser();p.add_argument('table',type=Path);p.add_argument('patterns',type=Path);p.add_argument('neutral',type=Path);p.add_argument('out',type=Path);p.add_argument('--radius',type=int,default=6);p.add_argument('--bound',type=int,default=160);p.add_argument('--merger',type=Path,default=Path(__file__).resolve().parent/'joint_return_merge');a=p.parse_args()
box={0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198}
r={tuple(map(int,l.split()[:2])):(int(l.split()[2]),1 if l.split()[3]=='R'else-1,int(l.split()[4]))for l in a.table.read_text().splitlines()}
allrows=[json.loads(s)for s in a.neutral.read_text().splitlines()];rows=[x for x in allrows if x['state']in box or x['state']>=2000]
a.out.mkdir(exist_ok=True);results=[];began=time.monotonic()
for i,c in enumerate(rows):
 rr=r.copy();rr[c['state'],c['read']]=tuple(c['new']);table=a.out/f'{i:03d}.tm';table.write_text(''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {n}\n'for(q,b),(w,d,n)in sorted(rr.items())))
 result=subprocess.run([str(a.merger.resolve()),str(table),str(a.radius),str(a.bound),str(a.patterns)],capture_output=True,text=True,check=True)
 (a.out/f'{i:03d}.hits.jsonl').write_text(result.stdout);(a.out/f'{i:03d}.log').write_text(result.stderr)
 rec=dict(index=i,edit=c,hits=len(result.stdout.splitlines()),summary=result.stderr.splitlines()[-1]);results.append(rec);print(json.dumps(rec),flush=True)
(a.out/'receipt.json').write_text(json.dumps(dict(all_neutral_rows=len(allrows),selected_candidates=len(rows),hits=sum(x['hits']for x in results),seconds=time.monotonic()-began,results=results,scope='Heuristic nomination with frozen original windows. Any hit requires combined one-step certificates or fresh source proofs.'),indent=2)+'\n')
