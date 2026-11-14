#!/usr/bin/env python3
"""Broaden the local quotient search on narrow-fitness 194-state grammars.
Discovery only; accepted machine must be independently verified.
"""
from pathlib import Path
import sys, json, itertools, subprocess, time, hashlib
sys.dont_write_bytecode=True
P=Path(__file__).resolve().parent
PRIMARY=P/'reference_primary'
sys.path.insert(0,str(PRIMARY))
import compiler as c
import build194 as b
inc=('leaf','inc',1)
c.MACROS[(inc,inc)]=99
c.MACROS[((inc,inc),(inc,inc))]=190
EDITS={(38,0):(0,True,11),(38,1):(1,True,122),(164,1):(1,True,130),(214,0):(0,True,312),(214,1):(1,True,20),(312,0):(0,True,188)}

def valid(raw,folds):
    child,aliases=b.apply_folds(raw,folds)
    try:b.check_local_folds(raw,child,aliases,folds)
    except (AssertionError,KeyError):return None
    return child

def witness(raw,shape):
    ops=c.opportunities_fast(raw,shape)
    bound=len(c.max_matching(ops))
    for goal in range(bound,-1,-1):
        taken=set(); chosen=[]
        def go(i):
            if len(chosen)==goal:
                rows=valid(raw,chosen)
                return (rows,chosen.copy()) if rows is not None else None
            if len(chosen)+len(ops)-i<goal:return None
            a,z,acts=ops[i]
            if a not in taken and z not in taken:
                taken.update((a,z))
                for aa in itertools.product(*acts):
                    chosen.append((a,z,aa))
                    result=go(i+1)
                    if result is not None:return result
                    chosen.pop()
                taken.difference_update((a,z))
            return go(i+1)
        found=go(0)
        if found is not None:return found
    raise RuntimeError('No empty witness?')

started=time.monotonic(); seen=set(); handled=set(); audit=[]; found=None
while time.monotonic()-started<650:
    pending=sorted(P.glob('collect.hit*.grammar.json'),key=lambda f:int(f.name.split('.hit')[1].split('.')[0]))
    fresh=[f for f in pending if f.name not in handled]
    for f in fresh:
        handled.add(f.name)
        grammar=c.read_grammar(f)
        raw,index,shape=c.build(grammar);raw.update(EDITS)
        digest=hashlib.sha256(b.table_text(raw).encode()).hexdigest()
        if digest in seen:continue
        seen.add(digest)
        rows,folds=witness(raw,shape)
        n=len(rows)//2
        if n>194:
            audit.append({'file':f.name,'n':n,'skip':'wrong fitness'})
            continue
        tmp=P/'sample_input.tm';tmp.write_text(b.table_text(rows))
        proc=subprocess.run([str(P/'action_merge'),str(tmp),'5','150'],capture_output=True,text=True)
        assert proc.returncode==0,proc.stderr
        entries=[json.loads(s) for s in proc.stdout.splitlines() if s.strip()]
        audit.append({'file':f.name,'n':n,'raw_states':len(raw)//2,'folds':len(folds),'extra_opportunities':len(entries)})
        if entries or n<194:
            candidate={'file':f.name,'raw_states':len(raw)//2,'states':n,'folds':folds,'additional':entries}
            (P/'sample_winner.tm').write_text(b.table_text(rows))
            (P/'sample_winner.json').write_text(json.dumps(candidate,indent=2))
            found=candidate
            print('FOUND',json.dumps(candidate),flush=True)
            break
        if len(audit)%50==0:print('SCREENED',len(audit),'grammar_files',len(handled),'seconds',time.monotonic()-started,flush=True)
    if found is not None:break
    if 'DONE' in (P/'collect.log').read_text() and not [f for f in P.glob('collect.hit*.grammar.json') if f.name not in handled]:break
    if not fresh:time.sleep(1)
receipt={'screened':len(audit),'files_seen':len(handled),'distinct_raw_tables':len(seen),'found':found,'elapsed':time.monotonic()-started,'radius':5,'max_local_steps':150,'audit':audit}
(P/'sample_receipt.json').write_text(json.dumps(receipt,indent=2))
print('DONE',len(audit),'found',found is not None,'seconds',time.monotonic()-started,flush=True)
