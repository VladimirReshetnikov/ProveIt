"""Try relocating one read-0 runtime branch, leaving its state free to initialize.

This differs from a whole-state merge: only all incoming edges that can
reach q/read0 are redirected, while incoming q/read1 edges remain unchanged.
All survivors must pass every affine instruction case. Register-box states
are protected, so this does not change the published box contracts.
"""
from pathlib import Path
from collections import defaultdict
import json, time, hashlib

ROOT=Path(__file__).resolve().parent
from prepare_inputs import prepare
prepare()
from tmlib import load
T,_=load(ROOT/'machine/runtime252_oldlabels.tm')
executor_bytes=(ROOT/'symexec.py').read_bytes()
assert hashlib.sha256(executor_bytes).hexdigest()=='5bf83da419c47b9c8d79fcc755e40048f599255c2f1b2cb4656dc04bb02bb85d'
raw=executor_bytes.decode()
code='SKIP ='+raw.split('SKIP =',1)[1].split('paths = json.load',1)[0]
code=code.replace("form = 'c'; box_eff = []; steps = 0; visits = 0", "form = 'c'; box_eff = []; steps = 0; visits = 0; prev = None")
code=code.replace("w, d, q2 = T[(q, s[1])]; steps += 1", "w, d, q2 = T[(q, s[1])]; prev = RECORD(q,s[1],prev); steps += 1")
code=code.replace("if d == 'L' and q2 == q:\n                L =", "if d == 'L' and q2 == q:\n                prev = RECORD(q,b,prev)\n                L =")
code=code.replace("if d == 'R' and q2 == q:\n                L =", "if d == 'R' and q2 == q:\n                prev = RECORD(q,b,prev)\n                L =")
code=code.replace("if w == 0 and d == 'L':\n            q =", "if w == 0 and d == 'L':\n            prev = RECORD(q,0,prev)\n            q =")
code=code.replace("q = '2' if r == 0 else '6';", "prev = 'BOX'; q = '2' if r == 0 else '6';")
code=code.replace("q = '48'; form = 'l'; steps += 1; continue", "prev = 'BOX'; q = '48'; form = 'l'; steps += 1; continue")
code=code.replace("form = 'l'; steps += 1; continue\n        w, d, q2 = T[(q, 0)]", "prev = 'BOX'; form = 'l'; steps += 1; continue\n        w, d, q2 = T[(q, 0)]")

incoming=defaultdict(set); caseuse=defaultdict(set); active=[0]
def record(q,b,prev):
    incoming[q,b].add(prev); caseuse[q,b].add(active[0]); return q,b
ns={'T':T,'D0':40,'RECORD':record}
exec(compile(code,'adapted_symbolic_executor','exec'),ns)
paths=json.loads((ROOT/'paths.json').read_text())
cases=[]
for p,op in paths:
    Q=p[3:]
    branches=[('z','dec0'),('p','dec')] if op.endswith('.decnz') else [('-', 'inc' if op.endswith('.inc') else None)]
    for br,eff in branches:
        if op.endswith('.inc') or (op.endswith('.decnz') and br=='p'): Q2=ns['inc'](Q)
        elif op.endswith('.decnz'): Q2=ns['inc'](ns['strip']('0',1,Q))
        elif op.startswith('_continue'): Q2=ns['strip']('1',int(op.split('.')[1]),Q)
        elif op.startswith('_break'): Q2=ns['inc'](ns['strip']('0',int(op.split('.')[1]),Q))
        else: Q2=''
        e=() if eff is None else ((eff,ns['REG'][op.split('.')[1]]),)
        if Q2 is None: exp=ns['canon']([('b',1)],[('r',0,1,41),('b',1),('box',('plain',)+e)])
        else: exp=ns['canon']([('b',1)],ns['tape_R'](Q2,0,e))
        cases.append((Q,br,exp,op=='halt'))
def check(c):
    Q,br,exp,halt=c
    try:
        out=ns['run']('96',[('b',1)],ns['tape_R'](Q,0,()),br,exp,fuel=1000)
    except (ns['Fail'],KeyError): return False
    return out[0]==('halt' if halt else 'ok')
for i,c in enumerate(cases):
    active[0]=i
    assert check(c),i
ns['RECORD']=lambda q,b,prev:(q,b)
core={0,1,2,3,5,6,28,31,38,40,43,44,48,56,59,60,63,64,69,73,75,83,84,85,95,97,109,112,131,96}
eligible=[]
for q in sorted({q for q,b in T},key=int):
    pred=incoming[q,0]
    if int(q) in core or not pred or any(not isinstance(x,tuple) for x in pred): continue
    if any(int(a) in core for a,b in pred): continue
    allincoming={key for key,(w,d,t) in T.items() if t==q}
    eligible.append((q,sorted(pred)))
result={'eligible':eligible,'candidates':0,'survivors':[],'scope':'Protected-box affine diagnostic; no kernel or startup proof.'}
print('eligible',eligible,flush=True)
started=time.monotonic()
for q,pred in eligible:
    relevant=set(caseuse[q,0])
    for e in pred: relevant |= caseuse[e]
    witnesses=sorted(relevant,key=lambda j:len(cases[j][0]))
    for dest,write,move in [(d,w,m) for d in sorted({q for q,b in T},key=int) for w in [0,1] for m in ['L','R']]:
        if dest==q: continue
        tt=dict(T)
        for e in pred:
            tt[e]=(write,move,dest)
        tt[q,0]=(1,'R','97')
        ns['T']=tt; result['candidates']+=1
        if all(check(cases[j]) for j in witnesses) and all(check(c) for c in cases):
            result['survivors'].append({'boot_state':q,'redirected_rows':pred,'destination':dest,'write':write,'move':move})
            name=f'relocated252_q{q}_r{dest}_w{write}_{move}.tm'
            (ROOT/'machine'/name).write_text(f'#! start {q}\n'+''.join(f'{a} {b} {w} {d} {n}\n' for (a,b),(w,d,n) in sorted(tt.items())))
            print('SURVIVOR',result['survivors'][-1],flush=True)
    print('done',q,'seconds',round(time.monotonic()-started,2),flush=True)
result['seconds']=time.monotonic()-started
(ROOT/'boot_relocation_complete.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
