#!/usr/bin/env python3
"""Rescreen folds using inductively proved zero-register information.

Unlike the baseline screen, zero-decrement excursions on any known-zero
register are admissible. This remains a sufficient diagnostic, not a
lower-bound procedure. No changed machine is accepted by finite samples.
"""
from pathlib import Path
import sys,importlib.util,json,time
from types import SimpleNamespace
from collections import defaultdict,Counter
ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/'upstream/Computability/BusyBeaver/Research/ZFC'
sys.path.insert(0,str(BASE))
import candidate252_independent_audit as audit
import permutation252_phase_analysis as phase
sys.modules['cost_search']=SimpleNamespace()
source=ROOT/'upstream/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py'
spec=importlib.util.spec_from_file_location('strict_specialized',source)
strict=importlib.util.module_from_spec(spec);spec.loader.exec_module(strict)
table={(str(q),b):(w,d,str(t)) for(q,b),(w,d,t)in audit.read_table((BASE/'candidate-permutation252/zfc_permutation252_old.tm').read_bytes()).items()}
prog=(ROOT/'upstream/lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v').read_bytes()
sites,cases,targets,first=phase.program_graph(prog)
values,enabled,*_=phase.phase_analysis(sites,cases,targets,first)
zero_set=set()
zero_tests=0
def oracle(q,branch,state):
    global zero_tests
    if state==('plain',None) and q in strict.SKIP:
        r=strict.SKIP[q];return ('2' if r==0 else '6'),('mark',r)
    if state[0]=='mark':
        r=state[1]
        if q=='73':return '48',('plain',('inc',r))
        if q=='43':
            if r in zero_set:
                zero_tests+=1
                return '3',('plain',None)
            if branch is not None and branch[0]==r:
                return ('3',('plain',None)) if branch[1] else ('63' if r==0 else '48',('plain',('dec',r)))
    return None
strict.oracle=oracle
records=[]
for i,(site,path,op,arg,zero)in enumerate(cases):
    phys=audit.NEWPHYS[arg] if op in('CI','CD')else arg
    branch=(phys,zero)if op=='CD'else None
    nxt=audit.successor(path,op,arg,zero)
    effect=('inc',phys)if op=='CI'else ('dec',phys)if op=='CD'and not zero else None
    right=([('b',int(b))for b in nxt]if nxt is not None else[])
    right += [('r',0,1,(41 if nxt is None else 40)-len(nxt or'')),('b',1),('box',('plain',effect))]
    zeros={audit.NEWPHYS[r]for r,m in enumerate(values[site]or[])if m==1}
    if op=='CD'and zero:zeros.add(phys)
    records.append((path,op,branch,strict.canon([('b',1)],right),zeros))
def check(rows,i):
    global zero_set
    p,op,branch,target,zero_set=records[i]
    try:
        result,literal=strict.run(rows,p,branch,target,halt=op=='CH',fuel=1000)
        return literal>0,sum(result.values()),None
    except(AssertionError,KeyError)as ex:return False,0,str(ex)
class Track(dict):
    def __init__(self,r):super().__init__(r);self.used=set()
    def __getitem__(self,k):self.used.add(k);return super().__getitem__(k)
if __name__=='__main__':
    usage=defaultdict(list);begin=time.monotonic()
    for i in range(len(cases)):
        if not enabled[i]:continue
        t=Track(table);ok,n,err=check(t,i);assert ok,(i,err)
        for q in {q for q,b in t.used}:usage[q].append((n,i))
    for us in usage.values():us.sort()
    protected={(str(q),b)for q,b in audit.BOX_PAIRS}
    prot_targets={table[k][2]for k in protected}
    states=sorted({q for q,b in table},key=int)
    eligible=[q for q in states if q not in prot_targets|{'96'}and all((q,b)not in protected for b in(0,1))]
    failed=Counter();survivors=[];checked=0;recipes=0
    for dead in eligible:
        for dst in states:
            if dead==dst:continue
            rows={(q,b):(w,d,dst if t==dead else t)for(q,b),(w,d,t)in table.items()if q!=dead}
            for _,i in usage[dead]:
                ok,n,err=check(rows,i);checked+=1
                if not ok:failed[err]+=1;break
            else:
                for i in range(len(cases)):
                    if not enabled[i]:continue
                    ok,n,err=check(rows,i);checked+=1
                    if not ok:failed[err]+=1;break
                else:
                    survivors.append([int(dead),int(dst)])
                    print('SURVIVOR',dead,dst,flush=True)
            recipes+=1
        print('finished',dead,'recipes',recipes,'seconds',round(time.monotonic()-begin,2),flush=True)
    report={'recipes':recipes,'cases':checked,'survivors':survivors,
            'zero_tests':zero_tests,'failures':dict(failed),'seconds':time.monotonic()-begin,
            'baseline_table_sha256':audit.EXPECTED_SHA,'enabled_cases':sum(enabled),
            'scope':'Universal source-mask-specialized box contracts; bounded symbolic screen. No global machine theorem.'}
    (ROOT/'root_experiments/specialized_fold_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items()if k!='failures'},indent=2))
