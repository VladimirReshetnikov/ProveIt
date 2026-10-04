#!/usr/bin/env python3
"""Independent standard-library checker. No author/upstream code is imported.
Finite-support evaluator uses particle-to-endpoint alignments, never gap flight shortcuts.
The mathematical all-configuration proof is in AUDIT.md, not inferred from tests.
"""
import hashlib, itertools, json, pathlib, random, time
from dataclasses import dataclass

ROOT = pathlib.Path(__file__).resolve().parent
@dataclass(frozen=True)
class Row:
    name: str
    e0: frozenset
    e1: frozenset
    lo: int
    hi: int
    @property
    def offsets(self): return self.e0 | self.e1
    @property
    def delta(self): return self.e0 ^ self.e1

A = (Row('AR',frozenset((0,1)),frozenset((0,2)),-4,6),
     Row('AL',frozenset((0,4)),frozenset((0,3)),-4,8),
     Row('AC',frozenset((0,1,6)),frozenset((-1,2,7)),-5,8))
B = (Row('BR',frozenset((0,2)),frozenset((1,2)),-4,6),
     Row('BL',frozenset((0,3)),frozenset((-1,3)),-5,7),
     Row('BC',frozenset((-5,0,3)),frozenset((-5,0,1)),-5,8))
ROWS = {r.name:r for r in A+B}

def require(ok, why):
    if not ok: raise RuntimeError(why)

def raw(s, rows):
    result={}
    for r in rows:
        # Every positive-weight endpoint contains a particle and every potential
        # endpoint alignment is considered. Empty surrounding space is implicit.
        anchors={p-e for p in s for e in r.offsets}
        for x in anchors:
            seen=frozenset(p-x for p in s if x+r.lo<=p<=x+r.hi)
            if seen==r.e0: result[(r.name,x)]=0
            elif seen==r.e1: result[(r.name,x)]=1
    return result

def swap(s,key):
    name,x=key
    return s ^ frozenset(x+v for v in ROWS[name].delta)

def statuses(s,rows,keys=None):
    keys=raw(s,rows) if keys is None else keys
    result={}
    for key in keys:
        isolated=not any(other!=key and abs(other[1]-key[1])<=30 for other in keys)
        prospective=(set(raw(swap(s,key),rows))==set(keys))
        result[key]=(isolated,prospective)
    return result

def step(s, rows, verify=True):
    keys=raw(s,rows)
    status=statuses(s,rows,keys)
    selected={k for k,v in status.items() if v==(True,True)}
    out=s
    for k in selected: out=swap(out,k)
    if verify:
        require(set(raw(out,rows))==set(keys), ('raw key drift',s,rows,out))
        require(statuses(out,rows)==status, ('eligibility drift',s,out,status))
        require(len(out)==len(s), ('mass',s,out))
        restored=out
        for k in selected: restored=swap(restored,k)
        require(restored==s, ('involution',s,out))
    return out,keys,status

def F(s,verify=True): return step(step(s,A,verify)[0],B,verify)[0]
def Finv(s,verify=True): return step(step(s,B,verify)[0],A,verify)[0]

def state(D,t):
    require(0<=t<2*D-22,('phase domain',D,t))
    return (frozenset((0,5+t,6+t,D)) if t<=D-11 else
            frozenset((0,2*D-18-t,2*D-14-t,D+1)))

def pattern(s): return {p for p in s if 0<=p<=6}=={0,5,6}

def exhaustive_overlaps():
    records=[]; assignments=0; changed=0
    for rows in (A,B):
        for source in rows:
            fixed=set(range(source.lo,source.hi+1))
            for side,endpoint in enumerate((source.e0,source.e1)):
                for target in rows:
                    for anchor in range(-30,31):
                        win=set(range(anchor+target.lo,anchor+target.hi+1))
                        if not win.intersection(source.delta): continue
                        require(abs(anchor)<=15,('influence bound',source,target,anchor))
                        free=sorted(win-fixed)
                        counts=[0,0,0,0]; witness=None
                        # Complete truth table for this pairwise interaction:
                        # all outside bits matter only if they lie in target W.
                        for mask in range(1<<len(free)):
                            context=set(endpoint)|{p for j,p in enumerate(free) if mask>>j&1}
                            out=context.symmetric_difference(source.delta)
                            before=frozenset(p-anchor for p in context if p in win)
                            after=frozenset(p-anchor for p in out if p in win)
                            b=before in (target.e0,target.e1)
                            a=after in (target.e0,target.e1)
                            counts[2*int(b)+int(a)]+=1
                            if a!=b and witness is None: witness=sorted(context)
                            require(out.symmetric_difference(source.delta)==context,'toggle inverse')
                            own=frozenset(p for p in out if p in fixed)
                            require(own==(source.e1 if side==0 else source.e0),'own-key failure')
                        assignments+=sum(counts); changed+=counts[1]+counts[2]
                        records.append({'source':source.name,'side':side,'target':target.name,
                            'anchor':anchor,'free_bits':len(free),
                            'counts_00_01_10_11':counts,'first_changed_witness':witness})
    # A source-side swap reverses the before/after predicate table exactly.
    indexed={(x['source'],x['side'],x['target'],x['anchor']):x for x in records}
    for x in records:
        y=indexed[(x['source'],1-x['side'],x['target'],x['anchor'])]
        c=x['counts_00_01_10_11']; d=y['counts_00_01_10_11']
        require(c==[d[0],d[2],d[1],d[3]],'side symmetry')
    (ROOT/'critical-overlap-truth-tables.json').write_text(json.dumps(records,indent=2)+'\n')
    return {'interaction_tables':len(records),'complete_assignments':assignments,
        'predicate_change_assignments':changed,'maximum_free_bits':max(x['free_bits'] for x in records)}

def orbit_checks():
    cycles=0; phases=0; big=0; raw_counter={r.name:0 for r in A+B}
    for D in range(13,121):
        s=frozenset((0,5,6,D))
        for t in range(2*D-22):
            require(s==state(D,t),('orbit',D,t,s))
            require(pattern(s)==(t==0),('hit exclusivity',D,t,s))
            mid,ak,ast=step(s,A)
            out,bk,bst=step(mid,B)
            require(len(ak)==len(bk)==1,('legal key uniqueness',D,t,ak,bk))
            for keys,status in ((ak,ast),(bk,bst)):
                require(next(iter(status.values()))==(True,True),'legal rejection')
                raw_counter[next(iter(keys))[0]]+=1
            require(Finv(out)==s,('inverse composition',D,t))
            s=out; phases+=1
        require(s==frozenset((0,5,6,D+1)),('cycle return',D,s));cycles+=1
    for D in (10**6,10**20,10**50,10**100):
        ts={0,1,D-12,D-11,D-10,D-9,2*D-25,2*D-24,2*D-23}
        for t in sorted(ts):
            s=state(D,t); out=F(s)
            expected=(frozenset((0,5,6,D+1)) if t==2*D-23 else state(D,t+1))
            require(out==expected,('big coordinate one-step',D,t,out))
            require(Finv(out)==s,('big inverse',D,t))
            require(pattern(s)==(t==0),'big hit');big+=1
    # Continuous multi-cycle trace validates the time formula independently of
    # merely substituting isolated phases into the closed form.
    s=frozenset((0,5,6,13)); hits=[]; last=60*60+3*60
    for t in range(last+1):
        if pattern(s): hits.append(t)
        if t<last: s=F(s,False)
    require(hits==[k*k+3*k for k in range(61)],('quadratic times',hits))
    return {'complete_cycles':cycles,'complete_cycle_steps':phases,
        'large_coordinate_boundary_steps':big,'largest_D_digits':101,
        'halfstep_row_counts':raw_counter,'continuous_steps':last,'continuous_hits':len(hits)}

def generic_checks():
    rng=random.Random(20261004); cases=0; moved=0; multi=0; rejected=0
    examples={}
    corpus=[]
    # Arbitrary dense finite words, plus spatially separated active/malformed islands.
    for _ in range(2000):
        p=rng.choice((.03,.08,.15,.3,.6,.9))
        corpus.append(frozenset(x for x in range(-80,81) if rng.random()<p))
    for r in A+B:
        for side in (r.e0,r.e1):
            for q in A+B:
                for other in (q.e0,q.e1):
                    for gap in (0,1,4,8,14,15,16,23,24,29,30,31,32,37,38,39,45,60,80):
                        corpus.append(side|frozenset(gap+x for x in other))
    for s in corpus:
        for rows in (A,B):
            out,keys,status=step(s,rows)
            back=step(out,rows)[0]
            require(back==s,('actual second block',s,out))
            selected=[k for k,v in status.items() if v==(True,True)]
            moved+=out!=s;multi+=len(selected)>1
            iso_reject=[k for k,v in status.items() if v==(True,False)]
            rejected+=bool(iso_reject)
            if iso_reject and 'isolated_prospective_rejection' not in examples:
                examples['isolated_prospective_rejection']={'support':sorted(s),'block':rows[0].name[0],
                    'keys':[list(k) for k in keys],'rejected':[list(k) for k in iso_reject]}
            if len(selected)>1 and 'multiple_selected' not in examples:
                examples['multiple_selected']={'support':sorted(s),'block':rows[0].name[0],
                    'selected':[list(k) for k in selected],'output':sorted(out)}
        require(Finv(F(s,False),False)==s,'global inverse random')
        require(F(Finv(s,False),False)==s,'global right inverse random')
        shift=137
        require(F(frozenset(x+shift for x in s),False)==frozenset(x+shift for x in F(s,False)),
                'translation covariance')
        cases+=1
    require(moved>0 and multi>0 and rejected>0,('nonvacuity',moved,multi,rejected))
    return {'configurations':cases,'block_checks':2*cases,'changed_blocks':moved,
        'multiple_selected_blocks':multi,'isolated_prospective_rejections':rejected,'examples':examples}

def main():
    start=time.time()
    for r in A+B:
        require(len(r.e0)==len(r.e1),'equal weight')
        require(r.offsets<=set(range(-7,8)),'write radius')
        require(-8<=r.lo<=r.hi<=8,'read radius')
        require(r.offsets<=set(range(r.lo,r.hi+1)),'endpoint containment')
    report={'schema':1,'all_checks_passed':True,'independence':'Authored independently from the six literal rows; no upstream/author code imported or executed.'}
    report['critical_overlaps']=exhaustive_overlaps();print(json.dumps(report['critical_overlaps']),flush=True)
    report['orbit']=orbit_checks();print(json.dumps(report['orbit']),flush=True)
    report['generic_finite_inputs']=generic_checks();print(json.dumps(report['generic_finite_inputs']),flush=True)
    report['elapsed_seconds']=round(time.time()-start,3)
    report['checker_sha256']=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()
    report['overlap_certificate_sha256']=hashlib.sha256((ROOT/'critical-overlap-truth-tables.json').read_bytes()).hexdigest()
    (ROOT/'independent-results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
