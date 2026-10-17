#!/usr/bin/env python3
"""Compile the no-filler MP edge into the frozen 252 table; test uniform folds.

The source edit is Prog254.v node6423 right6434->6453. Reusing each replaced
decision node's old binary label makes the emitted edit exactly row204/read1,
target113->132. The 8366 affine checks refer to this changed source, not the
original 8391-guard program. Their register-box contracts remain conditional.
The abstract no-filler calculus equivalence is in EnumNoFiller254.lean.
"""
from __future__ import annotations
import argparse
from collections import Counter,defaultdict
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time
from types import SimpleNamespace

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sys.dont_write_bytecode=True

def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

class Tracking(dict):
    def __init__(self,t):super().__init__(t);self.used=set()
    def __getitem__(self,k):self.used.add(k);return super().__getitem__(k)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,default=ROOT/'ProveIt')
    ap.add_argument('--input-dir',type=Path,
                    help='Portable closure containing Prog254.v, frozen252_old.tm, candidate252_independent_audit.py, and strict_affine.py.')
    ap.add_argument('--output',type=Path,default=HERE/'nofiller_frozen')
    ap.add_argument('--seconds',type=float,default=600)
    ap.add_argument('--boot-limit',type=int,default=1_000_000)
    ap.add_argument('--skip-folds',action='store_true')
    args=ap.parse_args();out=args.output;out.mkdir(parents=True,exist_ok=True)
    repo=args.repo;base=repo/'Computability/BusyBeaver/Research/ZFC'
    a=load('nf_audit',(args.input_dir/'candidate252_independent_audit.py')if args.input_dir else(base/'candidate252_independent_audit.py'))
    d=load('nf_dag',HERE/'gap_dag_audit.py')
    sys.modules['cost_search']=SimpleNamespace()
    sp=(args.input_dir/'strict_affine.py')if args.input_dir else(repo/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py')
    strict=load('nf_strict',sp)
    source=(args.input_dir/'Prog254.v')if args.input_dir else(repo/'lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v')
    raw=source.read_bytes();assert hashlib.sha256(raw).hexdigest()==d.EXPECTED_SHA256
    nodes=d.read_nodes(raw)
    assert nodes[6423]==(('N',6424),('N',6434))
    nodes[6423]=(('N',6424),('N',6453))
    tree=d.source_tree(nodes)
    src_stats=d.audit_tree(tree)
    assert src_stats['unique_decision_pairs']==203 and src_stats['guarded_cases']==8366
    frozen=((args.input_dir/'frozen252_old.tm')if args.input_dir else(base/'candidate-permutation252/zfc_permutation252_old.tm')).read_bytes()
    assert hashlib.sha256(frozen).hexdigest()==a.EXPECTED_SHA
    table={(str(q),b):(v,m,str(t))for(q,b),(v,m,t)in a.read_table(frozen).items()}
    assert table['204',1]==(1,'R','113')
    table['204',1]=(1,'R','132')
    protected={(str(q),b)for q,b in a.BOX_PAIRS}
    def encode(t):
        return ('#! start 64\n'+''.join(f'{q} {b} {v} {m} {s}\n'for(q,b),(v,m,s)in sorted(t.items(),key=lambda x:(int(x[0][0]),x[0][1])))).encode()
    (out/'nofiller252_old.tm').write_bytes(encode(table))
    cases=[]
    for path,e in d.leaves(tree):
        op='C'+e[0];r=e[1]if len(e)>1 else None
        for zero in ((True,False)if op=='CD'else(None,)):
            physical=a.NEWPHYS[r]if op in('CI','CD')else r
            branch=(physical,zero)if op=='CD'else None
            nxt=a.successor(path,op,r,zero)
            effect=('inc',physical)if op=='CI'else('dec',physical)if op=='CD'and not zero else None
            right=([('b',int(c))for c in nxt]if nxt is not None else[])
            right += [('r',0,1,(41 if nxt is None else 40)-len(nxt or'')),('b',1),('box',('plain',effect))]
            cases.append((path,op,r,zero,branch,strict.canon([('b',1)],right)))
    assert len(cases)==8366
    def check(t,i):
        path,op,r,zero,branch,target=cases[i]
        try:
            rules,literal=strict.run(t,path,branch,target,halt=op=='CH',fuel=1000)
            assert literal>0
            return True,sum(rules.values()),None
        except (AssertionError,KeyError)as e:return False,0,str(e)
    def boot(t):
        q,h,ones='64',0,set();used=set()
        for tick in range(args.boot_limit+1):
            if q=='254':return {'outcome':'halt','steps':tick},used
            if q=='96'and ones and min(ones)==h-1:
                right=sorted(i for i in ones if i>=h)
                if right and right[0]-h>=40:
                    gap=right[0]-h;pos=right[0]+1;vs=[]
                    while pos<=max(ones):
                        if pos in ones:break
                        pos+=1;n=0
                        while pos in ones:n+=1;pos+=1
                        if not n:break
                        vs.append(n-1)
                    else:
                        if len(vs)>=9:
                            regs=[vs[j]for j in a.NEWPHYS]
                            record={'outcome':'root','steps':tick,'gap':gap,'head':h,'logical_registers':regs,'spares':vs[9:]}
                            if regs[1]==regs[2]==regs[5]==0:
                                record['outcome']='safe_root';record['ones']=sorted(ones)
                                return record,used
            if tick==args.boot_limit:return {'outcome':'fuel','steps':tick,'state':q,'head':h,'ones':len(ones)},used
            used.add((q,int(h in ones)));v,m,q=t[q,int(h in ones)]
            if v:ones.add(h)
            else:ones.discard(h)
            h+=1 if m=='R'else -1
    result={'scope':__doc__,'status':'running','source_sha256':d.EXPECTED_SHA256,'frozen_table_sha256':a.EXPECTED_SHA,
        'new_table_sha256':hashlib.sha256(encode(table)).hexdigest(),'source_pairs':203,'source_guards':8366,
        'changed_binary_row':{'state':204,'read':1,'old':[1,'R',113],'new':[1,'R',132]},
        'baseline_passed':False,'baseline_failure':None,'folds':{'planned':0,'tested':0,'checks':0,'survivors':[]},
        'kernel_binary_simulation':False,'state_improvement_claimed':False}
    start=time.monotonic();usage=defaultdict(list)
    def save():
        result['elapsed_seconds']=time.monotonic()-start
        (out/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    for i in range(len(cases)):
        traced=Tracking(table);ok,steps,err=check(traced,i)
        if not ok:
            result.update(status='baseline_failed',baseline_failure={'case':i,'data':cases[i][:4],'reason':err});save();print(json.dumps(result,indent=2));return
        for q in{q for q,b in traced.used}:usage[q].append((steps,i))
    for us in usage.values():us.sort()
    result['baseline_passed']=True
    result['boot'],bootused=boot(table)
    result['boot_rows']=len(bootused)
    result['runtime_states']=len(usage)
    save();print('BASELINE8366 PASS; boot '+json.dumps(result['boot']),flush=True)
    if args.skip_folds:result['status']='baseline_only';save();return
    states=sorted({q for q,b in table},key=int)
    protected_targets={table[k][2]for k in protected}
    eligible=[q for q in states if q!='96'and q not in protected_targets and all((q,b)not in protected for b in(0,1))]
    result['folds']['planned']=len(eligible)*(len(states)-1)
    failures=Counter();search_start=time.monotonic()
    with(out/'folds.jsonl').open('w')as journal:
        for dead in eligible:
            for target in states:
                if target==dead:continue
                if time.monotonic()-search_start>=args.seconds:result['status']='fold_time_limit';save();return
                candidate={(q,b):(v,m,target if s==dead else s)for(q,b),(v,m,s)in table.items()if q!=dead}
                assert len(candidate)==502 and all(candidate[k]==table[k]for k in protected)
                fail=None;reason=None
                for steps,i in usage[dead]:
                    ok,_,reason=check(candidate,i);result['folds']['checks']+=1
                    if not ok:fail=i;break
                if fail is None:
                    for i in range(len(cases)):
                        ok,_,reason=check(candidate,i);result['folds']['checks']+=1
                        if not ok:fail=i;break
                rec={'deleted':int(dead),'target':int(target),'failure':fail,'reason':reason}
                result['folds']['tested']+=1
                if fail is None:
                    rec['boot'],_=boot(candidate);result['folds']['survivors'].append(rec)
                    (out/f'nofiller251_{dead}_{target}.tm').write_bytes(encode(candidate))
                    print('SURVIVOR '+json.dumps(rec),flush=True)
                else:failures[reason]+=1
                journal.write(json.dumps(rec,separators=(',',':'))+'\n')
            result['folds']['failure_reasons']=dict(failures);save()
    result['status']='fold_complete';save()
    print(json.dumps({'status':result['status'],'baseline_cases':len(cases),
        'fold_recipes':result['folds']['tested'],'affine_checks':result['folds']['checks'],
        'survivors':result['folds']['survivors'],'elapsed_seconds':result['elapsed_seconds']},indent=2),flush=True)

if __name__=='__main__':main()
