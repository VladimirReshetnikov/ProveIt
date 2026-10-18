#!/usr/bin/env python3
"""Read-only episode search over all feasible universally symbolic sites.

The six skipped guards are separately justified by the source phase analysis.
Every stored cube is an overapproximation of a full affine tape expression.
"""
import importlib.util,json,sys,os
from pathlib import Path
from collections import Counter

BASE=Path(os.environ.get('ZFC246_SOURCE',str(Path(__file__).resolve().parents[1]/'sources/context246/zfc-context246')))
HERE=Path(__file__).resolve().parent
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m);return m
dec=load('episode_bdd',HERE/'decoder_bdd.py')
contexts={q:set() for q in dec.Tq}
observations=0
def observe(q,left,right):
    global observations
    q=int(q)
    if q not in dec.pure or q in dec.cuts:return
    observations+=1
    cube={}
    for segments,offset,d in ((left,-1,-1),(right,0,1)):
        uncertain=False
        for seg in segments:
            if abs(offset)>42:break
            if seg[0]=='box':
                cube[offset]=0
                uncertain=True
                break
            b,a,c=(seg[1],0,1) if seg[0]=='b' else seg[1:]
            for _ in range(min(c,43)):
                if abs(offset)>42:break
                cube[offset]=b;offset+=d
            if a>0:
                uncertain=True;break
        if d==-1 and not uncertain:
            while abs(offset)<=42:cube[offset]=0;offset-=1
    contexts[q].add(tuple(sorted(cube.items())))

engine=(BASE/'reviews/prior250/code/affine_engine.py').read_text()
engine=engine.replace("if seg[0]=='b':\n            write,move,following=table[q,seg[1]];q=following;", "if seg[0]=='b':\n            observe(q,left,right)\n            write,move,following=table[q,seg[1]];q=following;")
engine=engine.replace("        write,move,following=table[q,0]\n", "        observe(q,left,right)\n        write,move,following=table[q,0]\n")
scope={'observe':observe}
exec(compile(engine,'affine_engine_with_observation','exec'),scope)
build=load('phase_builder',BASE/'code/rebuild_machines.py')
T={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in build.build().items()}
def increment(pc):return pc[:pc.rindex('0')]+'1' if '0' in pc else None
def strip(pc,symbol,count):
    while pc and count:count-=pc[-1]==symbol;pc=pc[:-1]
    return pc
checked=0
for leaf,(pc,op,logical) in enumerate(build.program_sites()):
    if leaf in (6317,6318,6435,6436):continue
    r=build.PHYSICAL[logical] if op in ('CI','CD') else logical
    for zero in ((True,False) if op=='CD' else (None,)):
        if op=='CD' and not zero and leaf in (6316,6434):continue
        branch=(r,zero) if op=='CD' else None
        if op=='CI' or op=='CD' and not zero:successor=increment(pc)
        elif op=='CD':successor=increment(strip(pc,'0',1))
        elif op=='CB':successor=increment(strip(pc,'0',r))
        elif op=='CC':successor=strip(pc,'1',r)
        else:successor=''
        effect=('inc',r) if op=='CI' else (('dec',r) if op=='CD' and not zero else None)
        extra=int(op=='CD' and not zero)
        if successor is None:right=[('r',0,1,41+extra),('b',1),('box',('plain',effect))]
        else:right=[('b',int(b)) for b in successor]+[('r',0,1,40+extra-len(successor)),('b',1),('box',('plain',effect))]
        scope['run'](T,pc,branch,scope['canon']([('b',1)],right),halt=op=='CH',fuel=1000)
        checked+=1
assert checked==8385
print('Contexts gathered',observations,sum(len(s) for s in contexts.values()),flush=True)
protected={2,4,6,48,63,73,83,95,109,112,131,255,75,60,44,31,56,38,40,28,64,69}
hits=[]
for q in sorted(dec.Tq & dec.pure - dec.cuts - protected):
    cubes=tuple(contexts[q])
    if not cubes:print('unused',q,flush=True);continue
    sq=dec.summary(q)
    for r in sorted(dec.Tq-{q}):
        if dec.depends(r,q):continue
        sr=dec.summary(r)
        if all(dec.cube(sq,c)==dec.cube(sr,c) for c in cubes):
            hits.append(dict(remove=q,replace=r,contexts=len(cubes)))
print(json.dumps(dict(cases=checked,observations=observations,hits=hits),indent=2))
reverse_hits=[]
for q in sorted(dec.Tq & dec.pure - dec.cuts - protected):
    cubes=tuple(contexts[q])
    if not cubes:continue
    sq=dec.summary(q)
    entries=[]
    for d in sorted({d for s,b,w,d in dec.incoming[q]}):
        options=[]
        for r in sorted(dec.Tq-{q}):
            if dec.depends(r,q):continue
            sr=dec.shift(dec.summary(r),-2*d)
            if all(dec.cube(sq,c)==dec.cube(sr,c) for c in cubes):options.append(r)
        if not options:break
        entries.append(dict(incoming_motion=d,opposite_targets=options))
    else:reverse_hits.append(dict(remove=q,replacements=entries))
print('Reverse hits',reverse_hits,flush=True)
(HERE/'decoder_phase_results.json').write_text(json.dumps(dict(cases=checked,
    observations=observations,context_counts={q:len(cs) for q,cs in contexts.items()},hits=hits,reverse_hits=reverse_hits),indent=2)+'\n')
