#!/usr/bin/env python3
"""Exact all-natural dispatcher endpoints after redirecting302 to4.

This is a semantics probe, not an equivalence claim for the whole program.
"""
from pathlib import Path
import hashlib
import json
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/'k220_replay/baseline/K221_Construction_2026-10-20'
sys.path.insert(0,str(BASE/'portable'));import build221 as b
sys.path.insert(0,str(BASE/'portable/runtime/vendor'));import symbolic_runtime as rt
r=rt.r
P=ROOT/'baseline219/K219_Construction_2026-10-20/machine'
T=b.read_table((P/'k219.native.tm').read_bytes());S=json.loads((P/'sites219.json').read_text())
U={(q,bit):(w,d,4 if z==302 else z)for(q,bit),(w,d,z)in T.items()if q!=302}
mp={int(q):int(z)for q,z in json.loads((BASE/'portable/runtime/reference_results/legacy_mapping.json').read_text()).items()}
for q in {q for q,bit in T}|{254}:
    if q not in mp:mp[q]=q+1000
L={(mp[q],bit):(w,d,mp[z])for(q,bit),(w,d,z)in U.items()}
oldL={(mp[q],bit):(w,d,mp[z])for(q,bit),(w,d,z)in T.items()}
lemmas,_=rt.prove_blocks(L);oldlemmas,_=rt.prove_blocks(oldL)
inv={z:q for q,z in mp.items()}


def probe(site,positive):
    pc,op,arg=site
    values=[rt.var(2+i)for i in range(9)]
    if op=='CD':values[arg]=rt.add(rt.num(1),values[arg])if positive else rt.ZERO
    physical=[None]*9
    for i,j in enumerate(r.PHY):physical[j]=values[i]
    result=physical.copy();delta=0;extra=None
    if op=='CD'and positive:
        result[r.PHY[arg]]=rt.minus1(result[r.PHY[arg]]);delta=1
    elif op=='CI':
        result[r.PHY[arg]]=rt.add(result[r.PHY[arg]],rt.num(1));extra=1
    state=rt.State(96,[rt.bit(1),rt.BLANK],[rt.bit(int(x))for x in pc]+[rt.run(0,rt.add(rt.var(1),rt.num(64-len(pc)))),rt.bit(1)]+rt.file_bits(physical))
    targets={}
    candidates={'ordinary_increment':r.inc(pc)}
    if op in('CD','CB'):candidates['usual_zero_break']=r.inc(r.strip(pc,'0',arg if op=='CB'else 1))
    for label,(successor,overflow)in candidates.items():
        goal=rt.State(96,[rt.bit(1),rt.BLANK],[rt.bit(int(x))for x in successor]+[rt.run(0,rt.add(rt.var(1),rt.num(64+delta+overflow-len(successor)))),rt.bit(1)]+rt.file_bits(result,extra))
        targets[label]=(goal.key(),rt.num(-overflow),successor)
    clock=motion=rt.ZERO;rows=set()
    for n in range(4000):
        key=state.key()
        if n and state.q==96 and any(atom[0]=='run'and atom[1]==0 and atom[2][1]==1 for atom in state.right):
            matched=[label for label,(g,m,s)in targets.items()if key==g and motion==m]
            return dict(symbolic_steps=n,duration=clock,motion=motion,matched=matched,
                        successor={label:targets[label][2]for label in matched},rows=sorted(rows),
                        actual_key=None if matched else key)
        clock,motion,event=state.step(L,lemmas,clock,motion)
        if event[0]!='list':rows.add((inv[event[1][0]],event[1][1]))
    raise AssertionError('No dispatcher return')


def main():
    started=time.monotonic();selected=set()
    # Every right-child decrement, one representative of each left-CD register,
    # and every CB1 entering the source/helper state103.
    first={}
    for i,(pc,op,arg)in enumerate(S):
        if op=='CD':
            first.setdefault((arg,pc[-1]),i)
            if pc.endswith('1'):selected.add(i)
    selected.update(first.values())
    cb103=[]
    for i,site in enumerate(S):
        if site[1:]==['CB',1]:
            result=rt.case(oldL,oldlemmas,site,False)
            if(mp[103],1)in result['rows']:selected.add(i);cb103.append(i)
    records=[]
    for i in sorted(selected):
        site=S[i]
        for positive in((False,True)if site[1]=='CD'else(False,)):
            try:
                result=probe(site,positive)
                records.append(dict(index=i,site=site,positive=positive,**result))
                print(i,site,positive,result['matched'],flush=True)
            except Exception as e:
                records.append(dict(index=i,site=site,positive=positive,error=str(e)))
                print('FAILED',i,site,positive,str(e),flush=True)
    dest=ROOT/'machine218/drop302_probe';dest.mkdir(exist_ok=True)
    (dest/'candidate218_experimental.tm').write_bytes(b.table_bytes(U))
    sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
    receipt=dict(status='SEMANTICS_PROBE_ONLY',states=len(U)//2,table_sha256=sha(dest/'candidate218_experimental.tm'),
                 cb103_indices=cb103,cases=records,seconds=time.monotonic()-started,
                 proof_boundary='Whole-program semantics intentionally changed. This is not a candidate claimed equivalent to Con(ZFC). Exact symbolic all-natural primitive endpoints only.')
    (dest/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items()if k!='cases'}),flush=True)


if __name__=='__main__':main()
