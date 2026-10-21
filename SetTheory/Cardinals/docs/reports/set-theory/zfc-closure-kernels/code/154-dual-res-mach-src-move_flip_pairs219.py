"""Prioritize uniform incoming-move-flip merge families (finite search)."""
from pathlib import Path
import argparse,json
from verify_runtime_portable import read_table
R=Path(__file__).resolve().parent
PACKET=R.parent;PACKAGED=(PACKET/'inputs/k219.native.tm').is_file()
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--table',type=Path,default=PACKET/'inputs/k219.native.tm' if PACKAGED else R.parent/'baseline219/K219_Construction_2026-10-20/machine/k219.native.tm')
ap.add_argument('--pairs-dir',type=Path,default=PACKET/'pairs' if PACKAGED else R/'whole_primitive/k219')
ap.add_argument('--output-dir',type=Path,default=PACKET/'regenerated/movement_pairs' if PACKAGED else R/'whole_primitive/k219_gate_combined')
args=ap.parse_args();P=args.pairs_dir;T=read_table(args.table)
incoming={q:set()for q,b in T}
for(q,b),(w,d,t)in T.items():
    if t in incoming:incoming[t].add(d)
files=['priority_pairs.txt','common_pairs.txt','new_state_pairs.txt','semantic_pairs.txt']
seen=set();pairs=[]
for name in files:
    for line in(P/name).read_text().splitlines():
        a,b=map(int,line.split())
        for keep,drop in [(a,b),(b,a)]:
            if drop==0 or len(incoming[drop])!=1 or(keep,drop)in seen:continue
            seen.add((keep,drop));pairs.append((keep,drop))
O=args.output_dir;O.mkdir(parents=True,exist_ok=True)
(O/'move_pairs.txt').write_text(''.join(f'{a} {b}\n'for a,b in pairs))
for part in range(2):
    (O/f'move_pairs_{part}.txt').write_text(''.join(f'{a} {b}\n'for a,b in pairs[part::2]))
receipt=dict(scope='Prioritized finite uniform incoming-movement flips, both retained rows arbitrary.',
    incoming_directions={q:sorted(v)for q,v in incoming.items()},pairs=len(pairs),
    uniform_incoming_states=sum(len(v)==1 for v in incoming.values()),input_pair_files=files)
(O/'move_pair_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items()if k!='incoming_directions'}))
