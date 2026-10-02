#!/usr/bin/env python3
"""Portable independent review checks for the two 808b53ed8 signal archives.

verify(collision_root, direct_root, manifest=None) accepts extracted package roots,
imports only three independently source-pinned reviewed modules, and returns
finite check results without writing files. Optional manifest is the safe-extract
archive/member inventory. Executed module names are restored in a finally block.
The CLI takes explicit roots; there are no permanent temporary-path dependencies.
"""
from pathlib import Path, PurePosixPath
from fractions import Fraction as F
from contextlib import contextmanager
import argparse, hashlib, itertools as it, json, random, sys, types

ARCHIVES = {
 'Collision_Geometry_Diophantine_Signal_Machines.zip': '584bfaadc7ba69ee97fcf2339190632fa0e4ba82a5ebb70cb3dbd5caebdd5f04',
 'Signal_Machine_Diophantine_Certificates.zip': '288d8f9790748ab0dde812bf8f770758306ac78ec1a0a04c75499245471d9ca1',
}
SOURCE_PINS = (
 ('review808b_collision', 0, 'code/signal_certificates.py', 'abdcb7705c98c009e943c55eabaee923b72a3bbaa74f2606e620504bc92f6400'),
 ('signal_geometry', 1, 'scripts/signal_geometry.py', 'bf700f4abafede5aa719080ef5bf795fae2ca5f459690bf3c43a1d76cb3e982d'),
 ('review808b_sparse', 1, 'scripts/signal_sparse.py', '2aa5ef0e41c12cf4e30ddf20a3c54fc4d6dec0331a4f50e304b5d19c625c4ebc'),
)

@contextmanager
def source_modules(roots):
    prepared=[]
    for name,which,member,digest in SOURCE_PINS:
        path=roots[which]/member;raw=path.read_bytes()
        if hashlib.sha256(raw).hexdigest()!=digest:
            raise ValueError(f'Executed source hash mismatch: {member}')
        prepared.append((name,path,raw))
    missing=object();saved={};modules=[]
    try:
        for name,path,raw in prepared:
            saved[name]=sys.modules.get(name,missing)
            module=types.ModuleType(name);module.__file__=str(path)
            sys.modules[name]=module;exec(compile(raw,str(path),'exec'),module.__dict__)
            modules.append(module)
        yield modules
    finally:
        for name,old in saved.items():
            if old is missing:sys.modules.pop(name,None)
            else:sys.modules[name]=old

def verify(collision_root, direct_root, manifest=None):
    if not __debug__:raise RuntimeError('Assertions required; do not use Python -O.')
    roots=(Path(collision_root),Path(direct_root));checked=0
    if manifest is not None:
        for item in manifest:
            if item['archive'] not in ARCHIVES or item['sha256']!=ARCHIVES[item['archive']]:
                raise ValueError('Unexpected archive manifest.')
            root=roots[0 if item['archive'].startswith('Collision_') else 1]
            for member,meta in item['members'].items():
                path=PurePosixPath(member)
                if path.is_absolute() or '..' in path.parts or len(path.parts)<2:
                    raise ValueError('Unsafe member path.')
                raw=(root/Path(*path.parts[1:])).read_bytes()
                if hashlib.sha256(raw).hexdigest()!=meta['sha256'] or len(raw)!=meta['bytes']:
                    raise ValueError(f'Member mismatch: {member}')
                checked+=1
    with source_modules(roots) as modules:
        result=_checks(*modules,*roots)
    result['status']='PASS'
    result['scope']='Finite exact independent review and literal source-reduction scout; no production compiler or fixed universal operation claim'
    result['archive_sha256']=dict(ARCHIVES)
    result['source_sha256']={member:digest for _,_,member,digest in SOURCE_PINS}
    result['original_members_unchanged']=checked
    if manifest is not None:result['archives']=manifest
    return result

def _checks(cg,geo,sp,CG,SM):
    rng=random.Random(80853);counts={};ledgers=[]
    def row_value(row,a):return sum(c*(1 if k=='@' else a[k]) for k,c in row.items())
    def energy(rows,a):return sum(row_value(r,a)**2 for r in rows)
    def clean(r):return {k:v for k,v in r.items() if v}
    def minus(a,b):return clean({k:a.get(k,0)-b.get(k,0) for k in a.keys()|b.keys()})
    def at(c,s,i):
        z=c['segments'][s];r=dict(z['p'])
        if i:r['t'+str(i)]=r.get('t'+str(i),0)+z['v']
        if z['born']:r['t'+str(z['born'])]=r.get('t'+str(z['born']),0)-z['v']
        return clean(r)
    def gap(c,pair,i):return minus(at(c,pair[1],i),at(c,pair[0],i))
    def skeleton(machine,initial,layers):
        live=list(range(len(initial)));n=len(live);out=[];time=F(0);times=[]
        for layer in layers:
            batch=[];new=[]
            for block in layer['blocks']:
                if len(block)==1:new.append(live[block[0]])
                else:
                    batch.append(tuple(live[i] for i in block));labels=[initial[i] for i in block]
                    output=geo.output(machine,labels);new.extend(range(n,n+len(output)));n+=len(output)
            live=new;initial=layer['labels'];out.append(tuple(batch));time+=layer['dt'];times.append(time)
        return tuple(out),tuple(times)
    def reduction(c,n):
        # Source-multiset subtraction: every deleted nonzero row must be an actual emitted row.
        remaining=list(c['rows']);deleted=[];birth=0;death=0
        flights={}
        for e,event in enumerate(c['events']):
            for signal in event['incoming']:
                r=minus({event['position']:1},at(c,signal,event['batch']))
                assert r in remaining;flights[e,signal]=r
        for life in c['lifetimes']:
            pair=life['pair']
            if life['lower_equal']:
                r=gap(c,pair,life['start']);assert r=={} and r in remaining
                remaining.remove(r);deleted.append(r);birth+=1
            if life['end'] is not None and life['upper_equal']:
                r=gap(c,pair,life['end']);e=c['segments'][pair[0]]['death']
                assert e==c['segments'][pair[1]]['death']
                assert r==minus(flights[e,pair[0]],flights[e,pair[1]])
                assert r in remaining;remaining.remove(r);deleted.append(r);death+=1
        assert death==c['counts']['incoming']-c['counts']['events']
        erased=[]
        if c['K']>0 or c['halt']:
            for j in range(n-1):
                life=next(l for l in c['lifetimes'] if tuple(l['pair'])==(f'initial{j}',f'initial{j+1}'))
                assert life['start']==0 and not life['lower_equal']
                name=f'input_gap{j}';r={f'x{j+1}':1,f'x{j}':-1,name:-1,'@':-1}
                assert r in remaining;remaining.remove(r);erased.append(name)
                # Its retained lower row has B*(x_{j+1}-x_j)-h-1, B>=1.
                index=c['lifetimes'].index(life);lr=gap(c,life['pair'],0);lr.update({f'lower{index}':-1,'@':-1})
                assert lr in remaining and c['B']>=1
        assert all(not(set(r)&set(erased)) for r in remaining)
        assert all(r in remaining for r in flights.values())
        return remaining,deleted,erased,birth,death
    # Compare independent all-pairs and adjacent-only semantics and both literal compilers.
    fixtures=[]
    speeds={'a':0,'b':2,'c':3,'d':4}
    fixtures.extend([
        ((speeds,{}),list('dba'),[0,2,4],4),
        ((speeds,{frozenset('da'):()}),list('dada'),[0,4,10,14],3),
        ((speeds,{frozenset('da'):tuple('abcd')}),list('dada'),[0,4,10,14],5),
        ((speeds,{}),list('abcd'),[0,1,2,3],0),
        ((speeds,{}),[],[],0),((speeds,{}),['a'],[0],0)])
    for _ in range(140):
        speeds={k:v for k,v in zip('abcd',rng.choice([(0,1,3,5),(0,2,3,4),(0,2,2,5)]))}
        subsets=[s for k in range(2,5) for s in it.combinations(speeds,k) if len({speeds[a] for a in s})==len(s)]
        outsets=[s for k in range(5) for s in it.combinations(speeds,k) if len({speeds[a] for a in s})==len(s)]
        rules={frozenset(s):rng.choice(outsets) for s in subsets}
        n=rng.randrange(2,8);labels=[rng.choice(tuple(speeds)) for _ in range(n)];pos=[rng.randrange(4)]
        for _ in range(n-1):pos.append(pos[-1]+rng.randrange(1,6))
        fixtures.append(((speeds,rules),labels,pos,rng.randrange(7)))
    comparisons=0;forms=0;zero_maps=0;deleted_birth=0;deleted_death=0;erased_input=0;corrections=0;mutations=0;rank=0;galilean=0
    for machine,labels,pos,K in fixtures:
        layers=geo.trace(machine,labels,pos,K);schema=[l['blocks'] for l in layers]
        if len(labels)>=2:
            gaps=[b-a for a,b in zip(pos,pos[1:])];cm=cg.Machine(*machine)
            crun=cg.simulate(cm,labels,gaps,K);sk,times=skeleton(machine,labels,layers)
            assert crun.skeleton==sk and crun.times==times;comparisons+=1
            chamber=cg.compile_skeleton(cm,labels,sk);assert chamber.accepts(gaps)
            assert chamber.evaluate(gaps,chamber.witnesses(gaps))==0
            for i,t in enumerate(times):assert cg.dot(chamber.times[i],gaps)==t
            # A negative common velocity shift changes positions, never chronology.
            neg=cg.Machine({k:v-7 for k,v in machine[0].items()},machine[1]);nr=cg.simulate(neg,labels,gaps,K)
            assert nr.skeleton==sk and nr.times==times
            nc=cg.compile_skeleton(neg,labels,sk);assert nc.equalities==chamber.equalities and nc.strict==chamber.strict;galilean+=1
        final=layers[-1]['labels'] if layers else labels
        halted=all(machine[0][a]<=machine[0][b] for a,b in zip(final,final[1:]))
        for halt in [False]+([True] if halted else []):
            c=sp.compile_sparse(machine,labels,schema,halt);a=sp.sparse_witness(c,pos,layers)
            f=geo.compile_schema(machine,labels,schema,halt);fa=geo.witness(f,pos,layers)
            assert geo.polynomial(c,a)==geo.polynomial(f,fa)==0;forms+=1
            reduced,deleted,erased,birth,death=reduction(c,len(labels));deleted_birth+=birth;deleted_death+=death;erased_input+=len(erased)
            projected={k:v for k,v in a.items() if k not in erased};restored=dict(projected)
            for name in erased:
                j=int(name[len('input_gap'):]);restored[name]=projected[f'x{j+1}']-projected[f'x{j}']-1
            assert restored==a and energy(reduced,projected)==0;zero_maps+=1
            for name in c['variables']:
                if name in erased:continue
                bad=projected.copy();bad[name]+=1;assert energy(reduced,bad)>0;mutations+=1
            for _ in range(3):
                b={k:rng.randrange(-3,4) for k in projected};restored=dict(b)
                for name in erased:
                    j=int(name[len('input_gap'):]);restored[name]=b[f'x{j+1}']-b[f'x{j}']-1
                assert energy(c['rows'],restored)-energy(reduced,b)==energy(deleted,restored);corrections+=1
            if rank<35 and c['variables']:
                new=dict(c,variables=[x for x in c['variables'] if x not in erased],rows=reduced)
                assert geo.linear_rank(new)==len(new['variables']);rank+=1
            if len(ledgers)<10:ledgers.append({'n':len(labels),'K':c['K'],'halt':halt,'events':c['counts']['events'],'before_R':len(c['rows']),'after_R':len(reduced),'before_W':len(c['variables']),'after_W':len(c['variables'])-len(erased),'birth_zero_rows':birth,'death_rows':death})
    counts.update(independent_simulator_fixtures=comparisons,negative_speed_galilean_checks=galilean,full_sparse_source_forms=forms,complete_zero_bijections=zero_maps,deleted_birth_identities=deleted_birth,deleted_death_flight_identities=deleted_death,erased_input_slacks=erased_input,signed_full_SOS_corrections=corrections,projected_coordinate_mutations_rejected=mutations,projected_full_rank_checks=rank)
    # Exhaustive first-batch false-order/triple/simultaneous checks in both codebases.
    candidates=0;rejected=0
    speeds={'a':0,'b':2,'c':3,'d':4};cm=cg.Machine(speeds,{})
    for labels in it.product('abcd',repeat=3):
        for gaps in it.product(range(1,5),repeat=2):
            pos=[0,gaps[0],sum(gaps)];actual=cg.simulate(cm,labels,gaps,1)
            for blocks in ([[0,1],[2]],[[0],[1,2]],[[0,1,2]]):
                sk=(tuple(tuple(b) for b in blocks if len(b)>1),)
                try:ch=cg.compile_skeleton(cm,labels,sk);c=sp.compile_sparse((speeds,{}),labels,[blocks])
                except (cg.InvalidSkeleton,AssertionError):continue
                b=next(b for b in blocks if len(b)>1);j,k=b[:2];dt=F(pos[k]-pos[j],speeds[labels[j]]-speeds[labels[k]])
                layer=dict(dt=dt,end=[p+speeds[l]*dt for p,l in zip(pos,labels)],blocks=blocks)
                try:
                    a=sp.sparse_witness(c,pos,[layer]);ok=geo.polynomial(c,a)==0
                except AssertionError:ok=False
                expected=actual.skeleton==sk;assert ch.accepts(gaps)==ok==expected;candidates+=1;rejected+=int(not expected)
    counts['cross_report_first_batch_candidates']=candidates;counts['wrong_first_batch_candidates']=rejected
    # Strong boundary fixtures: omit an independent site, omit the third incoming signal, and attempt forbidden outputs.
    boundary=0
    for gaps,labels,sk in [((4,6,4),'dada',(((0,1),),)),((2,2),'dba',(((0,1),),)),((3,1),'dba',(((0,1),),))]:
        c=cg.compile_skeleton(cm,labels,sk);assert not c.accepts(gaps);boundary+=1
    try:cg.compile_skeleton(cg.Machine({'r':1,'l':0},{},False),['r','l'],(((0,1),),))
    except cg.InvalidSkeleton:boundary+=1
    else:raise AssertionError('undefined rule accepted')
    counts['explicit_boundary_rejections']=boundary
    # Source-derived low-row examples, retaining the entire emitted relation.
    m=({'r':2,'s':0},{frozenset(('r','s')):()});layers=geo.trace(m,['r','s'],[0,1],1)
    c=sp.compile_sparse(m,['r','s'],[layers[0]['blocks']],True);new,deleted,erased,birth,death=reduction(c,2)
    assert (len(c['rows']),len(new),len(c['variables']),len(erased))==(6,4,5,1)
    counts['annihilation_projection']={'residuals_before':6,'residuals_after':4,'witnesses_before':5,'witnesses_after':4}
    # K=0 prefix retains input checks; K=0 halting uses terminal lower checks to restore input slack.
    for halt in (False,True):
        c=sp.compile_sparse(({'a':0,'b':1},{}),['a','b'],[],halt)
        rows,_,erased,_,_=reduction(c,2)
        assert len(erased)==int(halt)
    counts['zero_batch_projection_cases']=2
    # Full rational-domain counterexample to erasing the initial-order slack.
    # Unused speed 3 enlarges D to 6; the emitted source is still the actual compiler output.
    m=({'r':1,'s':0,'q':3},{frozenset(('r','s')):()});l=geo.trace(m,['r','s'],[0,1],1)
    c=sp.compile_sparse(m,['r','s'],[l[0]['blocks']],True);new,_,erased,_,_=reduction(c,2)
    rational={'x0':F(0),'x1':F(1,2),'t1':F(3),'d1':F(2),'e0':F(3),'lower0':F(2)}
    assert c['B']==6 and energy(new,rational)==0 and all(v>=0 for v in rational.values())
    assert rational['x1']-rational['x0']-1==F(-1,2)
    counts['rational_projection_exception']={k:str(v) for k,v in rational.items()}
    counts['domain_note']='The input-slack projection is a natural-integer theorem, not a nonnegative-rational theorem: the displayed full reduced source has a rational zero but its only original input slack is -1/2.'
    # Literal shipped chamber simplifications with unique restoration of erased slacks.
    chamber_plan={
        'tournament_left':[(0,1)],'tournament_right':[(1,0)],
        'tournament_triple':[(1,0)],'simultaneous_two_sites':[(0,0,1),(1,1,0)],
        'zeno_clock_24_batches':[(3,2)]}
    chamber_ledgers=[];chamber_cases=0;chamber_identities=0
    for name,omit in chamber_plan.items():
        d=json.loads((CG/'data'/f'{name}.json').read_text());E=d['equalities'];G=[tuple(r) for r in d['strict']]
        assert all(r in G for r in omit);keep=[i for i,r in enumerate(G) if r not in omit]
        def matdot(row,g):return sum(a*b for a,b in zip(row,g))
        for g in it.product(range(7),repeat=d['dimension']):
            eq=all(matdot(r,g)==0 for r in E)
            old=eq and all(matdot(r,g)>0 for r in G)
            reduced=eq and all(matdot(G[i],g)>0 for i in keep)
            assert old==reduced
            if reduced:assert all(matdot(r,g)-1>=0 for r in omit)
            chamber_cases+=1
        for _ in range(30):
            g=[rng.randrange(-3,4) for _ in range(d['dimension'])];z=[rng.randrange(-3,4) for _ in keep]
            restored={i:value for i,value in zip(keep,z)}
            restored.update({i:matdot(r,g)-1 for i,r in enumerate(G) if r in omit})
            old=sum(matdot(r,g)**2 for r in E)+sum((matdot(r,g)-1-restored[i])**2 for i,r in enumerate(G))
            reduced=sum(matdot(r,g)**2 for r in E)+sum((matdot(G[i],g)-1-value)**2 for i,value in zip(keep,z))
            assert old==reduced;chamber_identities+=1
        chamber_ledgers.append({'packet':name,'old_R':len(E)+len(G),'new_R':len(E)+len(keep),'old_W':len(G),'new_W':len(keep),'deleted_rows':omit})
    counts['chamber_projection_cases']=chamber_cases;counts['chamber_signed_graph_identities']=chamber_identities;counts['chamber_projection_ledgers']=chamber_ledgers
    # Load/export guards: genuine emitted Certificate strictly checks all natural scalar coordinates.
    cert=cg.compile_skeleton(cm,['d','a'],(((0,1),),));w=cert.witnesses([1]);guards=0
    for bad in (False,1.0,-1):
        for which in ('seed','slack'):
            g=[1];z=list(w)
            if which=='seed':g[0]=bad
            else:z[0]=bad
            try:cert.evaluate(g,z)
            except ValueError:guards+=1
            else:raise AssertionError('invalid arithmetic coordinate accepted')
    counts['natural_coordinate_rejections']=guards
    # Existing output matrices evaluated independently of either polynomial class.
    exports=0
    for p in sorted(CG.glob('data/*.json')):
        d=json.loads(p.read_text())
        if 'equalities' not in d:continue
        assert all(type(x) is int for r in d['equalities']+d['strict'] for x in r)
        assert all(len(r)==d['dimension'] for r in d['equalities']+d['strict']);exports+=1
    for name in ('signal_geometry_examples.json','signal_sparse_examples.json'):
        for item in json.loads((SM/'examples'/name).read_text()):
            c=item['certificate'];a=item['assignment'];assert all(type(x) is int and x>=0 for x in a.values())
            assert all(type(coef) is int for r in c['rows'] for coef in r.values())
            assert energy(c['rows'],a)==0;exports+=1
    counts['integer_export_packets']=exports
    receipts={'collision':json.loads((CG/'data/checks.json').read_text()),'direct':{p.name:json.loads(p.read_text()) for p in sorted((SM/'expected_receipts').glob('*.json'))}}
    return {'counts':counts,'example_ledgers':ledgers,'author_receipts':receipts}

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--collision-root',type=Path,required=True)
    parser.add_argument('--direct-root',type=Path,required=True)
    parser.add_argument('--manifest',type=Path)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    manifest=json.loads(args.manifest.read_text()) if args.manifest else None
    result=verify(args.collision_root,args.direct_root,manifest)
    text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(json.dumps(result['counts'],indent=2))
