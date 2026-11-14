"""Independent positive control for predecessor-tagging state bypass."""
from pathlib import Path
import subprocess,json
HERE=Path(__file__).resolve().parent
T={}
def row(q,b,w,d,t):T[q,b]=(w,d,t)
row(0,0,0,1,1);row(0,1,1,1,9)
for b in (0,1):
    row(1,b,b,1,3+b)
    row(2,b,b,-1,5+b)
    row(3,b,b,1,9);row(4,b,b,1,9)
row(5,0,0,1,9);row(5,1,0,1,7)
row(6,0,0,1,9);row(6,1,0,1,8)
row(7,0,0,1,3);row(7,1,1,1,9)
row(8,0,0,1,9);row(8,1,1,1,4)
temp=HERE/'bypass_control';temp.mkdir(exist_ok=True)
(temp/'table.txt').write_text(''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {t}\n'for(q,b),(w,d,t)in sorted(T.items())))
(temp/'contexts.txt').write_text(''.join(f'{q} {(mask>>2)&1} {mask}\n'for q in range(9)for mask in range(32)))
proc=subprocess.run([str(HERE/'scan_bypass'),str(temp/'table.txt'),str(temp/'contexts.txt'),str(temp/'result.txt'),'9'],capture_output=True,text=True,check=True)
out=(temp/'result.txt').read_text();assert 'DROP 1 incoming 1\nPATCH 0 0 options ' in out
section=out.split('DROP 1 incoming 1\n',1)[1].split('DROP',1)[0]
assert '\n1 1 2\n' in section
stutter=subprocess.run([str(HERE/'scan_stutter_bypass'),str(temp/'table.txt'),str(temp/'contexts.txt'),str(temp/'stutter_result.txt'),'9','2'],capture_output=True,text=True,check=True)
section=(temp/'stutter_result.txt').read_text().split('DROP 1 incoming 1\n',1)[1].split('DROP',1)[0]
assert '\n1 1 2\n' in section
# The child writes a temporary 1 at the predecessor bit, then restores 0.
# Every compatible whole five-cell window reaches the two-step parent endpoint.
patch=dict(T);patch[0,0]=(1,1,2);patch={k:v for k,v in patch.items()if k[0]!=1}
def trace(table,q,h,tape,steps):
    for _ in range(steps):
        w,d,q=table[q,tape[h]];tape[h]=w;h+=d
    return q,h,tape
checked=0
for mask in range(32):
    if (mask>>2)&1:continue
    tape={i:(mask>>(i+2))&1 for i in range(-2,3)}
    parent=trace(T,0,0,dict(tape),2)
    child=trace(patch,0,0,dict(tape),4)
    assert parent==child
    checked+=1
report=dict(control='temporary predecessor bit distinguishes eliminated-state entry',deleted_state=1,
            patch=[0,0,1,'R',2],parent_steps=2,child_steps=4,all_compatible_windows=checked,counters=proc.stdout.strip(),stutter_counters=stutter.stdout.strip())
(temp/'receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
