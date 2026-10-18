#!/usr/bin/env python3
"""Synthesize the disputed action of compatible partial-state fusions.

The two states agree on one quotient transition. Their other transition is
not selected from the two originals: every write/direction/retained target,
including halt, is tried. All 55 register support rows remain literal.
Failure is a finite sufficient-checker outcome, not a semantic counterexample.
"""
from pathlib import Path
from collections import Counter, defaultdict
import argparse, hashlib, importlib.util, json, re, sys, time
from types import SimpleNamespace

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent/'ProveIt'
BASE = ROOT/'Computability/BusyBeaver/Research/ZFC'
sys.path.insert(0,str(BASE))
sys.dont_write_bytecode = True
import candidate252_independent_audit as audit

def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    return mod

def setup():
    strict_path=ROOT/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py'
    sys.modules['cost_search']=SimpleNamespace()
    strict=load(strict_path,'synthesized_fusion_strict')
    raw=(BASE/'candidate-permutation252/zfc_permutation252_old.tm').read_bytes()
    assert hashlib.sha256(raw).hexdigest()==audit.EXPECTED_SHA
    num=audit.read_table(raw)
    table={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in num.items()}
    prog=ROOT/'lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v'
    body=prog.read_text().split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
    edge=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    nodes=re.findall(r'\(('+edge+r'),\s*('+edge+r')\)',body)
    assert len(nodes)==6459
    cases=[]
    def visit(n,p):
        for b,e in enumerate(nodes[n]):
            path=p+str(b);op,*arg=e.split()
            if op=='CN':visit(int(arg[0]),path);continue
            r=int(arg[0]) if arg else None
            for zero in ((True,False) if op=='CD' else (None,)):
                phys=audit.NEWPHYS[r] if op in ('CI','CD') else r
                guard=(phys,zero) if op=='CD' else None
                nxt=audit.successor(path,op,r,zero)
                effect=('inc',phys) if op=='CI' else ('dec',phys) if op=='CD' and not zero else None
                right=[('b',int(c)) for c in (nxt or '')]
                right += [('r',0,1,(41 if nxt is None else 40)-len(nxt or '')),('b',1),('box',('plain',effect))]
                cases.append((path,op,guard,strict.canon([('b',1)],right)))
    visit(0,'');assert len(cases)==8391
    return strict,table,num,cases,strict_path,prog

class Tracking(dict):
    def __init__(self,table):super().__init__(table);self.used=set()
    def __getitem__(self,k):self.used.add(k);return super().__getitem__(k)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--seconds',type=float,default=900)
    ap.add_argument('--output',type=Path,default=HERE/'synthesized-fusion.json')
    ap.add_argument('--skip-six',action='store_true')
    ap.add_argument('--resume',action='store_true',help='Resume a checkpoint ending after a complete pair group.')
    args=ap.parse_args();assert __debug__ and args.seconds>0
    strict,table,num,cases,strict_path,prog=setup()
    excluded={8202,8203,8204,8358,8359,8360} if args.skip_six else set()
    def check(T,i):
        p,op,guard,target=cases[i]
        try:
            counts,literal=strict.run(T,p,guard,target,halt=op=='CH',fuel=1000)
            assert literal>0
            return True,sum(counts.values()),None
        except AssertionError as e:return False,0,'fuel' if str(e)=='symbolic fuel exhausted' else 'unsupported'
        except KeyError:return False,0,'missing_transition'
    usage=defaultdict(set);cost={};began=time.monotonic()
    for i in range(len(cases)):
        tracked=Tracking(table);ok,n,_=check(tracked,i);assert ok,('baseline',i)
        cost[i]=n
        for row in tracked.used:usage[row].add(i)
    spare=[0]*65;spare[8]=1
    boot_target=audit.paint('',40,[0]*9,spare,2)
    q,h,ones,_,_=audit.run_prefix(num,82552)
    assert (q,h,ones)==(96,2,boot_target)
    protected={(str(q),b) for q,b in audit.BOX_PAIRS}
    states=sorted({q for q,b in table},key=int)
    forbidden={'96'}|{q for q,b in protected}|{table[k][2] for k in protected}
    eligible=set(states)-forbidden
    pairs=[]
    for dead in sorted(eligible,key=int):
        for keep in states:
            if dead==keep or keep=='96' or (keep in eligible and int(dead)>int(keep)):continue
            def quot(v):return v[0],v[1],keep if v[2]==dead else v[2]
            for bit in (0,1):
                if (keep,1-bit) in protected:continue
                if quot(table[dead,bit])==quot(table[keep,bit]) and quot(table[dead,1-bit])!=quot(table[keep,1-bit]):
                    pairs.append((dead,keep,1-bit))
    assert len(pairs)==264
    result={'status':'running','scope':__doc__,'baseline_sha256':audit.EXPECTED_SHA,
        'baseline_cases':8391,'baseline_boot_steps':82552,'pairs':len(pairs),
        'planned':len(pairs)*4*len(states),'excluded_source_cases':sorted(excluded),
        'checked':0,'case_checks':0,'survivors':[],'groups':[],
        'affine_fuel':1000,'seconds_limit':args.seconds,
        'attribution':'Mira-Cult original 254; Jeff verification; Wade compiler; mira-emmy public253; ProveIt permutation252; source27 strict affine checker.',
        'inputs':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in (strict_path,prog)},
        'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    reasons=Counter();journal=args.output.with_suffix('.jsonl');offset=0;past=0
    if args.resume:
        previous=json.loads(args.output.read_text())
        assert previous['baseline_sha256']==result['baseline_sha256']
        assert previous['excluded_source_cases']==result['excluded_source_cases']
        assert previous['checked']==1008*len(previous['groups'])
        for actual,(dead,keep,bit) in zip(previous['groups'],pairs):
            assert (actual['dead'],actual['keep'],actual['bit'])==(int(dead),int(keep),bit)
            assert actual['checked']==1008
        offset=len(previous['groups']);past=previous['elapsed_seconds']
        # Ignore incomplete post-checkpoint work, including any interrupted
        # final journal line. Every retained ledger row is parsed afresh.
        lines=journal.read_text().splitlines()[:previous['checked']]
        assert len(lines)==previous['checked']
        for line in lines: assert len(json.loads(line))==8
        journal.write_text('\n'.join(lines)+'\n')
        previous.setdefault('resume_history',[]).append({'previous_driver_sha256':previous['driver_sha256'],
            'checkpoint_recipes':previous['checked'],'journal_prefix_sha256':hashlib.sha256(journal.read_bytes()).hexdigest()})
        previous['driver_sha256']=result['driver_sha256']
        result=previous;result['status']='running';reasons=Counter(result['reasons'])
    def save():
        result['elapsed_seconds']=past+time.monotonic()-began
        result['reasons']=dict(reasons)
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('BASELINE PASS, synthesized fusion recipes',result['planned'],flush=True);save()
    stopped=False
    with journal.open('a' if args.resume else 'w') as f:
        for dead,keep,bit in pairs[offset:]:
            if time.monotonic()-began>=args.seconds:stopped=True;break
            candidate={(q,b):(w,d,keep if t==dead else t) for (q,b),(w,d,t) in table.items() if q!=dead}
            affected=(usage[dead,0]|usage[dead,1]|usage[keep,bit])-excluded
            order=sorted(affected,key=lambda i:(cost[i],i))
            assert len(candidate)==502 and all(candidate[k]==table[k] for k in protected)
            group={'dead':int(dead),'keep':int(keep),'bit':bit,'checked':0,'affected':len(affected),'failures':Counter()}
            result['groups'].append(group)
            witnesses=[]
            targets=[q for q in states if q!=dead]+['254']
            for w in (0,1):
                for d in ('L','R'):
                    for t in targets:
                        candidate[keep,bit]=w,d,t
                        failed=None;reason=None
                        for i in witnesses+[i for i in order if i not in witnesses]:
                            ok,_,reason=check(candidate,i);result['case_checks']+=1
                            if not ok:failed=i;break
                        if failed is None:
                            for i in range(len(cases)):
                                if i in excluded:continue
                                ok,_,reason=check(candidate,i);result['case_checks']+=1
                                if not ok:failed=i;break
                        if failed is None:
                            entry={'dead':int(dead),'keep':int(keep),'bit':bit,'action':[w,d,int(t)]}
                            data='#! start 64\n'+''.join(f'{q} {b} {a} {dd} {tt}\n' for (q,b),(a,dd,tt) in sorted(candidate.items(),key=lambda x:(int(x[0][0]),x[0][1])))
                            path=HERE/f'synth-{dead}-{keep}-{bit}-{w}-{d}-{t}.tm';path.write_text(data)
                            entry['file']=str(path);entry['sha256']=hashlib.sha256(data.encode()).hexdigest()
                            result['survivors'].append(entry);print('SURVIVOR',entry,flush=True)
                        else:
                            reasons[reason]+=1;group['failures'][reason]+=1
                            if failed not in witnesses:witnesses.insert(0,failed)
                        record=[int(dead),int(keep),bit,w,d,int(t),failed,reason]
                        f.write(json.dumps(record,separators=(',',':'))+'\n')
                        result['checked']+=1;group['checked']+=1
            save()
            if len(result['groups'])%10==0:print('completed groups',len(result['groups']),'recipes',result['checked'],'elapsed',round(time.monotonic()-began,1),flush=True)
    result['status']='partial' if stopped else 'completed'
    result['journal_sha256']=hashlib.sha256(journal.read_bytes()).hexdigest()
    result['journal_bytes']=journal.stat().st_size
    save()
    print({k:result[k] for k in ('status','checked','case_checks','survivors','elapsed_seconds')},flush=True)

if __name__=='__main__':main()
