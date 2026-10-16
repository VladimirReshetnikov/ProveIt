#!/usr/bin/env python3
"""Mixed-read two-state fusions on the actual public 253-state table.

A fusion keeps one state label, deletes the other, takes its read-0 action
from one parent and its read-1 action from the other, and redirects every
target of the deleted label. Pure-row folds and identical candidates are
excluded. All 55 published register-box rows remain byte-for-byte identical.
The existing attributed affine executor filters candidates; a survivor is
rechecked on every instruction case, then tested from a completely blank
tape. No consistency endpoint or proof-assistant certification is claimed.
"""
from pathlib import Path
import argparse
import ast
import collections
import hashlib
import itertools
import json
import sys
import time

if not __debug__:
    raise SystemExit('Run without Python optimization; assertions are checks.')
HERE=Path(__file__).resolve().parent
SRC=HERE/'source'
sys.path.insert(0,str(SRC))
import context_search as cs

PINS={
    'zfc_253.tm':'84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95',
    'zfc_254.tm':'d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb',
    'symexec.py':'5bf83da419c47b9c8d79fcc755e40048f599255c2f1b2cb4656dc04bb02bb85d',
    'Prog254.v':'1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746',
}

def read_table(path):
    rows={}; start=None
    for line in path.read_text().splitlines():
        if line.startswith('#! start '): start=line.split()[-1]
        elif line and not line.startswith('#'):
            q,b,w,d,n=line.split(); rows[q,int(b)]=int(w),d,n
    return rows,start

def assignment(path,name):
    for n in ast.parse(path.read_text()).body:
        if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id==name for t in n.targets):
            return ast.literal_eval(n.value)
    raise ValueError(name)

class Tracking(dict):
    def __init__(self,t): super().__init__(t); self.used=set()
    def __getitem__(self,k): self.used.add(k); return super().__getitem__(k)

def literal_blank_run(t,initial,limit,target):
    q,h,ones=initial,0,set()
    for steps in range(limit+1):
        if q=='96' and h==target[0] and ones==target[1]:
            return dict(outcome='exact_public_boot_frame',steps=steps,state=q,head=h,ones=len(ones))
        if q=='254': return dict(outcome='halt',steps=steps,state=q,head=h,ones=len(ones))
        if steps==limit: return dict(outcome='fuel_limit',steps=steps,state=q,head=h,ones=len(ones))
        w,d,q=t[q,int(h in ones)]
        if w: ones.add(h)
        else: ones.discard(h)
        h+=1 if d=='R' else -1

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=HERE/'hybrid-fusion-results.json')
    ap.add_argument('--affine-fuel',type=int,default=1000)
    ap.add_argument('--blank-fuel',type=int,default=2000000)
    args=ap.parse_args()
    if min(args.affine_fuel,args.blank_fuel)<1: ap.error('positive fuel required')
    for file,pin in PINS.items(): assert hashlib.sha256((SRC/file).read_bytes()).hexdigest()==pin,file
    labels=assignment(SRC/'12-sorts-code-regenerate_253.py','OLD_LABELS')
    compact,start=read_table(SRC/'zfc_253.tm')
    base,base_start=read_table(SRC/'zfc_254.tm')
    table={(str(labels[int(q)]),b):(w,d,str(labels[int(n)])) for (q,b),(w,d,n) in compact.items()}
    start=str(labels[int(start)])
    reconstructed={k:v for k,v in base.items() if k[0]!='8'}
    reconstructed.update({('3',0):(0,'L','48'),('5',0):(1,'R','97'),('5',1):(1,'R','64'),('49',1):(0,'R','5')})
    assert table==reconstructed and start=='5'
    box=assignment(SRC/'20-complete-vendor-decoder255-verify.py','BOX_STATES')
    protected={(str(q),b) for q in box for b in (0,1)}-{('3',0)}
    assert len(protected)==55 and all(table[k]==base[k] for k in protected)
    ns=cs.executor(table,SRC/'symexec.py')
    sites=cs.program_sites(SRC/'Prog254.v')
    cases=cs.cases(ns,sites)
    assert len(cases)==8391
    def check_case(t,i):
        ns['T']=t
        _,path,op,r,branch,expected=cases[i]
        try:
            result=ns['run']('96',[('b',1)],ns['tape_R'](path,0,()),branch,expected,fuel=args.affine_fuel)
            return (result[0]==('halt' if op=='CH' else 'ok'), result)
        except (ns['Fail'],KeyError) as ex:
            return False,(type(ex).__name__,str(ex))
    begun=time.monotonic()
    usage=collections.defaultdict(set); counts=[]
    for i in range(len(cases)):
        trace=Tracking(table); ok,out=check_case(trace,i)
        assert ok,(i,out)
        counts.append(out[1])
        for k in trace.used: usage[k].add(i)
    target_ones={-18,23}; pos=24
    physical=[0,2,0,0,0,0,5,0,0]
    spare=[0,0,1,0,0,0,0,0,1]+[0]*149
    for v in physical+spare:
        pos+=1
        target_ones.update(range(pos,pos+v+1)); pos+=v+1
    assert len(target_ones)==178
    boot=literal_blank_run(table,start,313000,(-17,target_ones))
    assert boot['outcome']=='exact_public_boot_frame' and boot['steps']==312975,boot
    report=dict(scope='Mixed-read two-state fusions; attributed affine box contracts; no kernel or consistency claim',
                source_ProveIt_commit='6ec2e80dbbe45a99b7812fb5757977307959a51e',
                public253_commit='0d544f2a2e3c18f12278441a74b7879f31cbe856',
                upstream254_commit='297ab8df7e5de329605c3875b4934643b371a5e3',
                source_sha256=PINS, driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                affine_fuel=args.affine_fuel,blank_fuel=args.blank_fuel,
                baseline_affine_cases=len(cases),baseline_boot=boot,protected_pairs=sorted(protected),
                candidates=[],duplicates_or_pure=0,protected_rejected=0,runtime_survivors=[],blank_survivors=[])
    out=args.output.resolve(); out.parent.mkdir(parents=True,exist_ok=True)
    def save():
        report['elapsed_seconds']=time.monotonic()-begun
        out.write_text(json.dumps(report,indent=2)+'\n')
    print('BASELINE',len(cases),'affine cases and complete blank bootstrap pass',flush=True)
    states=sorted({q for q,b in table},key=int)
    nonbox=[q for q in states if int(q) not in box]
    pairs=list(itertools.combinations(nonbox,2))
    # State 3/read0 lies outside the conservative box boundary. Its read1
    # transition is frozen; allowing a mixed read0 transplant covers that
    # additional legal case without deleting a box-interface state.
    pairs.extend(('3',q) for q in nonbox if q!='96')
    for pi,(a,b) in enumerate(pairs):
        keep,dead=(a,b) if b!='96' else (b,a)
        # Keep the dispatch label: the executor's stopping condition is 96.
        assert dead!='96' and int(dead) not in box
        def mapped(row):
            w,d,n=row; return w,d,keep if n==dead else n
        pure0=(mapped(table[keep,0]),mapped(table[keep,1]))
        pure1=(mapped(table[dead,0]),mapped(table[dead,1]))
        fused_seen=set()
        for donor0,donor1 in ((keep,dead),(dead,keep)):
            fusion=(mapped(table[donor0,0]),mapped(table[donor1,1]))
            if fusion in (pure0,pure1) or fusion in fused_seen:
                report['duplicates_or_pure']+=1; continue
            fused_seen.add(fusion)
            candidate={(q,s):mapped(row) for (q,s),row in table.items() if q!=dead}
            candidate[keep,0],candidate[keep,1]=fusion
            if any(candidate.get(k)!=table[k] for k in protected):
                report['protected_rejected']+=1; continue
            assert len(candidate)==504 and all(n in set(states)-{dead}|{'254'} for w,d,n in candidate.values())
            changed={k for k in table if candidate.get(k)!=table[k]}
            affected=set().union(*(usage[k] for k in changed))
            assert affected,'Genuinely changed runtime data should affect at least one advertised case'
            witnesses=sorted(affected,key=lambda i:(counts[i],i))
            rec=dict(keep=keep,dead=dead,read0_from=donor0,read1_from=donor1,working_states=252,
                     all55_protected_rows_unchanged=True,changed_rows=sorted(changed),
                     fused_rows=fusion,affected_baseline_cases=len(affected),tested=0)
            for i in witnesses:
                ok,result=check_case(candidate,i);rec['tested']+=1
                if not ok:
                    rec['outcome']='affine_rejected';rec['first_failure']=dict(case=i,site=cases[i][:-1],result=result);break
            else:
                for i in range(len(cases)):
                    ok,result=check_case(candidate,i); rec['tested']+=1
                    if not ok:
                        rec['outcome']='full_recheck_rejected';rec['first_failure']=dict(case=i,site=cases[i][:-1],result=result);break
                else:
                    rec['outcome']='all8391_affine_pass';report['runtime_survivors'].append((keep,dead,donor0,donor1))
                    mapped_start=keep if start==dead else start
                    rec['blank_run']=literal_blank_run(candidate,mapped_start,args.blank_fuel,(-17,target_ones))
                    if rec['blank_run']['outcome']=='exact_public_boot_frame': report['blank_survivors'].append((keep,dead,donor0,donor1))
                    target=out.parent/f'hybrid-{keep}-{dead}-read0-{donor0}.tm'
                    target.write_text('#! start '+mapped_start+'\n'+''.join(f'{q} {s} {w} {d} {n}\n' for (q,s),(w,d,n) in sorted(candidate.items(),key=lambda kv:(int(kv[0][0]),kv[0][1]))))
                    rec['table_file']=target.name;rec['table_sha256']=hashlib.sha256(target.read_bytes()).hexdigest()
                    print('SURVIVOR',rec,flush=True)
            report['candidates'].append(rec)
        if (pi+1)%2000==0:
            print('PAIRS',pi+1,'/',len(pairs),'CANDIDATES',len(report['candidates']),'SECONDS',round(time.monotonic()-begun,1),flush=True)
            save()
    report['unordered_parent_pairs']=len(pairs)
    report['outcome_counts']=dict(collections.Counter(c['outcome'] for c in report['candidates']))
    report['failure_reason_counts']=dict(collections.Counter(c['first_failure']['result'][-1] for c in report['candidates'] if 'first_failure' in c))
    save()
    print('FINAL',json.dumps({k:v for k,v in report.items() if k not in ('candidates','protected_pairs','failure_reason_counts')}),flush=True)

if __name__=='__main__': main()
