#!/usr/bin/env python3
"""Bounded uniform state folds of the frozen register-permutation252 table.

The 55 proved Box-support rows and dispatch96 are fixed. Every remaining
deletion is redirected uniformly to every other existing working state.
Strict affine diagnostics use the new physical register guards and retain
single-effect box contracts. Survivors receive all8391 checks before any
literal blank run. Fuel/time failure is never a nonhalting/impossibility proof.
The frozen252 artifact is read-only. No Lean/Coq process is started.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
import hashlib
import importlib.util
import json
from pathlib import Path
import platform
import sys
import tempfile
import time
from types import SimpleNamespace

sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[4]


class Tracking(dict):
    def __init__(self, rows): super().__init__(rows);self.used=set()
    def __getitem__(self,key):self.used.add(key);return super().__getitem__(key)


def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,default=ROOT)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--scratch',type=Path)
    ap.add_argument('--seconds',type=float,default=120)
    ap.add_argument('--affine-fuel',type=int,default=1000)
    ap.add_argument('--boot-limit',type=int,default=1000000)
    args=ap.parse_args()
    if not __debug__:ap.error('Assertions must remain enabled')
    if min(args.seconds,args.affine_fuel,args.boot_limit)<=0:ap.error('Positive bounds required')
    repo=args.repo.resolve();base=repo/'Computability/BusyBeaver/Research/ZFC'
    w=args.scratch.resolve()if args.scratch else Path(tempfile.mkdtemp(prefix='zfc-perm252-folds-'))
    if w==repo or repo in w.parents:ap.error('External scratch required')
    w.mkdir(parents=True,exist_ok=True)
    audit=load_module('permutation252_fold_audit',base/'candidate252_independent_audit.py')
    frozen=base/'candidate-permutation252/zfc_permutation252_old.tm';raw=frozen.read_bytes()
    assert hashlib.sha256(raw).hexdigest()==audit.EXPECTED_SHA
    numeric=audit.read_table(raw)
    table={(str(q),b):(v,d,str(t))for(q,b),(v,d,t)in numeric.items()}
    states=sorted({q for q,b in table},key=int);protected={(str(q),b)for q,b in audit.BOX_PAIRS}
    assert len(table)==504 and len(states)==252 and len(protected)==55
    source=repo/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py'
    (w/'strict_affine.py').write_bytes(source.read_bytes());sys.modules['cost_search']=SimpleNamespace()
    strict=load_module('permutation252_fold_strict',w/'strict_affine.py')
    # Parse the pinned literal source directly, without a host DAG substitution.
    prog=repo/'lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v'
    text=prog.read_text().split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
    import re
    edge=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    nodes=re.findall(r'\(('+edge+r'),\s*('+edge+r')\)',text);assert len(nodes)==6459
    cases=[]
    def visit(q,p):
        for b,e in enumerate(nodes[q]):
            path=p+str(b);op,*arg=e.split()
            if op=='CN':visit(int(arg[0]),path);continue
            r=int(arg[0])if arg else None
            for zero in((True,False)if op=='CD'else(None,)):
                physical=audit.NEWPHYS[r]if op in('CI','CD')else r
                branch=(physical,zero)if op=='CD'else None
                nxt=audit.successor(path,op,r,zero)
                effect=('inc',physical)if op=='CI'else('dec',physical)if op=='CD'and not zero else None
                right=([('b',int(c))for c in nxt]if nxt is not None else[])
                right += [('r',0,1,(41 if nxt is None else 40)-len(nxt or'')),('b',1),('box',('plain',effect))]
                cases.append((path,op,r,zero,branch,strict.canon([('b',1)],right)))
    visit(0,'');assert len(cases)==8391
    def check(current,i):
        p,op,r,zero,branch,target=cases[i]
        try:
            rules,literal=strict.run(current,p,branch,target,halt=op=='CH',fuel=args.affine_fuel)
            assert literal>0
            return True,sum(rules.values()),None
        except AssertionError as exc:
            return False,0,'fuel'if str(exc)=='symbolic fuel exhausted'else'unsupported_symbolic_rule'
        except KeyError:return False,0,'missing_transition'
    began=time.monotonic();usage=defaultdict(list)
    for i in range(len(cases)):
        traced=Tracking(table);ok,steps,_=check(traced,i);assert ok,('baseline_case',i)
        for q in{q for q,b in traced.used}:usage[q].append((steps,i))
    for group in usage.values():group.sort()
    q,h,ones,_,_=audit.run_prefix(numeric,82552)
    spares=[0]*65;spares[8]=1;target=audit.paint('',40,[0]*9,spares,2)
    assert(q,h,ones)==(96,2,target)
    protected_targets={table[k][2]for k in protected}
    eligible=[q for q in states if q!='96'and q not in protected_targets
              and all((q,b)not in protected for b in(0,1))]
    assert len(eligible)==221 and all(usage[q]for q in eligible)
    result={'status':'running','scope':'Bounded251-state uniformfold diagnostics ofactualpermutation252; no consistency/minimality claim or kernel proof ofmodifiedtables.',
            'source_table':str(frozen.relative_to(repo)),'table_sha256':audit.EXPECTED_SHA,
            'attribution':'Mira-Cult/Jeff/Wade original254; mira-emmy public253 PR20; originalcandidatepermutation [0,3,4,5,8,1,6,2,7]; newboundedfold experiment.',
            'logical_to_physical':list(audit.NEWPHYS),'protected_pairs':55,'fixed_dispatch_old':96,
            'extra_deletions_excluded_by_protected_incoming_rows':[7,9],
            'development_guard':'Initialeligibility omitted protectedincomingtargets7/9; byteidentityassertion stoppedbeforeanycandidatecompleted. Correctedfamilyexcludesboth.',
            'eligible_deletions':list(map(int,eligible)),'working_states_old':list(map(int,states)),
            'planned_recipes':len(eligible)*(len(states)-1),'baseline8391':'PASS','baseline_exact82552wholeboot':'PASS',
            'affine_fuel':args.affine_fuel,'search_wall_seconds_limit':args.seconds,'boot_limit':args.boot_limit,
            'python':platform.python_version(),'command':[sys.executable,*sys.argv],
            'input_sha256':{'driver':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'strict':hashlib.sha256(source.read_bytes()).hexdigest(),'Prog254':hashlib.sha256(prog.read_bytes()).hexdigest()},
            'sources':[],'completed_recipes':0,'affine_checks':0,'affine_survivors':[],
            'whole_boot_survivors':[],'finite_failure_is_not_impossibility':True,'scratch':str(w)}
    out=args.output.resolve();out.parent.mkdir(parents=True,exist_ok=True)
    journal=w/'recipes.jsonl';reason_counts=Counter();stopped=False
    def save():
        result['elapsed_seconds']=time.monotonic()-began;result['failure_reasons']=dict(reason_counts)
        out.write_text(json.dumps(result,indent=2)+'\n')
    save();print('BASELINE strict8391+literal82552 PASS; planned55471',flush=True)
    with journal.open('w')as record:
        for dead in eligible:
            group={'deleted_old':int(dead),'affected_cases':len(usage[dead]),'completed_destinations':0,'first_failure_case_in_destination_order':[]}
            result['sources'].append(group)
            for replacement in states:
                if replacement==dead:continue
                if time.monotonic()-began>=args.seconds:stopped=True;break
                candidate={(q,b):(v,d,replacement if t==dead else t)for(q,b),(v,d,t)in table.items()if q!=dead}
                assert len(candidate)==502 and all(candidate[k]==table[k]for k in protected)
                fail=None;reason=None
                for steps,i in usage[dead]:
                    ok,_,reason=check(candidate,i);result['affine_checks']+=1
                    if not ok:fail=i;break
                if fail is None:
                    for i in range(len(cases)):
                        ok,_,reason=check(candidate,i);result['affine_checks']+=1
                        if not ok:fail=i;break
                entry={'deleted':int(dead),'replacement':int(replacement),'first_failure_case':fail,'reason':reason}
                if fail is None:
                    print('AFFINE SURVIVOR',dead,replacement,flush=True)
                    result['affine_survivors'].append([int(dead),int(replacement)])
                    data=('#! start 64\n'+''.join(f'{q} {b} {v} {d} {t}\n'for(q,b),(v,d,t)in sorted(candidate.items(),key=lambda x:(int(x[0][0]),x[0][1])))).encode()
                    path=w/f'fold_{dead}_{replacement}.tm';path.write_bytes(data)
                    q,h,one='64',0,set();boot=None
                    for tick in range(args.boot_limit+1):
                        if q=='96'and h==2 and one==target:boot={'outcome':'exact82552target_frame','steps':tick};break
                        if q=='254':boot={'outcome':'halt','steps':tick};break
                        if tick==args.boot_limit:boot={'outcome':'fuel_limit','steps':tick};break
                        v,d,q=candidate[q,int(h in one)]
                        if v:one.add(h)
                        else:one.discard(h)
                        h+=1 if d=='R'else-1
                    entry['boot']=boot;entry['candidate_sha256']=hashlib.sha256(data).hexdigest();entry['table']=str(path)
                    if boot['outcome']=='exact82552target_frame':
                        result['whole_boot_survivors'].append(entry)
                        print('EXACT WHOLE BOOT SURVIVOR',json.dumps(entry),flush=True)
                else:reason_counts[reason]+=1
                record.write(json.dumps(entry,separators=(',',':'))+'\n');record.flush()
                group['first_failure_case_in_destination_order'].append(fail)
                group['completed_destinations']+=1;result['completed_recipes']+=1
            save()
            if stopped:break
    result['status']='time_bound_partial'if stopped else'completed'
    result['recipe_journal']={'path':str(journal),'sha256':hashlib.sha256(journal.read_bytes()).hexdigest(),'bytes':journal.stat().st_size}
    if not stopped:assert result['completed_recipes']==55471
    save();print(json.dumps({k:result[k]for k in('status','completed_recipes','affine_checks','affine_survivors','whole_boot_survivors','elapsed_seconds')}),flush=True)


if __name__=='__main__':main()
