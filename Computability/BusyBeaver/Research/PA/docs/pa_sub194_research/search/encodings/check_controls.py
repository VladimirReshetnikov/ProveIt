#!/usr/bin/env python3
"""Positive/adverse controls for the two inherited local templates."""
from pathlib import Path
import json,subprocess

HERE=Path(__file__).resolve().parent
OUT=HERE/'controls';OUT.mkdir(exist_ok=True)
def toy():return {(q,b):(b,1,194) for q in range(194) for b in (0,1)}
def write(t,path):path.write_text(''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {n}\n' for (q,b),(w,d,n) in sorted(t.items())))
def context(p1,p2,path):
    with path.open('w') as f:
        f.write('2\n')
        for q in range(194):
            for b in (0,1):
                words=[m for m in range(32) if (m>>2)&1==b and (p1(m) if q==1 else p2(m))] if q in (1,2) else []
                f.write(f'{q} {b} {len(words)} '+' '.join(map(str,words))+'\n')
def run(exe,table,ctx,out):
    r=subprocess.run([str(HERE/exe),str(table),str(ctx),'64','1','2'],capture_output=True,text=True,check=True)
    (OUT/out).write_text(r.stdout);return r.stdout
t=toy();t[0,0]=(0,1,1);t[1,0]=(0,1,5);t[2,1]=(1,1,6);t[3,0]=(0,1,4);t[4,0]=(0,1,5)
tp=OUT/'shift.tm';cp=OUT/'shift_context.txt';write(t,tp);context(lambda m:(m&7)==0,lambda m:bool(m&4),cp)
assert 'PASS 1 2 0 0 1 3 3 -2' in run('fold_shift',tp,cp,'shift_positive.txt')
t[3,0]=(0,-1,4);write(t,tp)
assert 'PASS 1 2 0 0 1 3 ' not in run('fold_shift',tp,cp,'shift_adverse.txt')
t=toy();t[0,0]=(1,1,1);t[1,0]=(0,1,5);t[2,1]=(1,1,6);t[3,0]=(1,1,4);t[4,0]=(0,1,5)
tp=OUT/'phase.tm';cp=OUT/'phase_context.txt';write(t,tp);context(lambda m:(m&6)==2,lambda m:(m&6)==6,cp)
assert 'PASS 1 2 0 0 -1 3 3 -1' in run('fold_bitphase',tp,cp,'phase_positive.txt')
t[3,0]=(0,1,4);write(t,tp)
assert 'PASS 1 2 0 0 -1 3 ' not in run('fold_bitphase',tp,cp,'phase_adverse.txt')
t=toy();t[0,0]=(1,1,1);t[1,0]=(0,1,5);t[2,1]=(1,1,6);t[3,0]=(1,1,4);t[4,0]=(0,1,5)
tp=OUT/'combined.tm';cp=OUT/'combined_context.txt';write(t,tp);context(lambda m:(m&7)==2,lambda m:bool(m&4),cp)
assert 'PASS 1 2 0 0 1 3 3 -1' in run('fold_combined',tp,cp,'combined_positive.txt')
t[3,0]=(0,1,4);write(t,tp)
assert 'PASS 1 2 0 0 1 3 ' not in run('fold_combined',tp,cp,'combined_adverse.txt')
r={'head_offset_positive_and_adverse':True,'neighboring_bit_positive_and_adverse':True,'combined_positive_and_adverse':True}
(OUT/'receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
