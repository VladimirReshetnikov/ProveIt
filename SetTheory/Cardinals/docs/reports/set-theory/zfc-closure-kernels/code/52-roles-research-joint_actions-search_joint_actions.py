#!/usr/bin/env python3
"""Joint incoming-action synthesis for deletion of a permutation252 state.

Unlike prior target-only searches, every external incoming row may change its
write, movement and destination, with jointly compensating edits allowed.
The family preserves the four register-box contracts and dispatcher. Success
requires all 8,391 conditional affine contracts; a rejected finite diagnostic
is not an impossibility theorem. Provenance and complete frontier are saved.
"""
from __future__ import annotations
import argparse, collections, hashlib, importlib.util, itertools, json, re, sys, time
from pathlib import Path
from types import SimpleNamespace

def load(name, path):
    spec=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(spec);sys.modules[name]=mod;spec.loader.exec_module(mod);return mod

class NeedRow(Exception):
    def __init__(self,index): self.index=index

class Table:
    def __init__(self,base,deleted=None,pending=None,assigned=None,track=False):
        self.base=base;self.deleted=deleted;self.pending=pending or {};self.assigned=assigned or {};self.used=set() if track else None
    def __getitem__(self,key):
        if self.used is not None:self.used.add(key)
        if key[0]==self.deleted:raise KeyError(key)
        if key in self.pending:raise NeedRow(self.pending[key])
        return self.assigned.get(key,self.base[key])

def setup(repo,fuel):
    z=repo/'Computability/BusyBeaver/Research/ZFC'
    audit=load('action_audit',z/'candidate252_independent_audit.py')
    raw=(z/'candidate-permutation252/zfc_permutation252_old.tm').read_bytes()
    assert hashlib.sha256(raw).hexdigest()==audit.EXPECTED_SHA
    table={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in audit.read_table(raw).items()}
    strictpath=repo/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py'
    sys.modules['cost_search']=SimpleNamespace()
    strict_text=strictpath.read_text()
    strict_text=strict_text.replace("literal_steps=0;rule_count=Counter()","literal_steps=0;rule_count=Counter();seen=set()")
    strict_text=strict_text.replace("        if onleft:\n","        key=(q,onleft,tuple(left),tuple(right))\n        if key in seen:raise AssertionError('exact_symbolic_cycle')\n        seen.add(key)\n        if onleft:\n",1)
    strict=SimpleNamespace();exec(compile(strict_text,str(strictpath),'exec'),strict.__dict__)
    text=(repo/'lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v').read_text().split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
    edge=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    nodes=re.findall(r'\(('+edge+r'),\s*('+edge+r')\)',text);assert len(nodes)==6459
    cases=[]
    def visit(q,p):
        for b,e in enumerate(nodes[q]):
            path=p+str(b);op,*arg=e.split()
            if op=='CN':visit(int(arg[0]),path);continue
            r=int(arg[0]) if arg else None
            for zero in ((True,False) if op=='CD' else (None,)):
                physical=audit.NEWPHYS[r] if op in ('CI','CD') else r
                branch=(physical,zero) if op=='CD' else None
                nxt=audit.successor(path,op,r,zero)
                effect=('inc',physical) if op=='CI' else ('dec',physical) if op=='CD' and not zero else None
                right=[('b',int(c)) for c in (nxt or '')]+[('r',0,1,(41 if nxt is None else 40)-len(nxt or '')),('b',1),('box',('plain',effect))]
                cases.append((path,branch,strict.canon([('b',1)],right),op=='CH'))
    visit(0,'');assert len(cases)==8391
    def check(current,i):
        p,b,t,h=cases[i]
        try:
            rules,literal=strict.run(current,p,b,t,halt=h,fuel=fuel);assert literal>0
            return True,sum(rules.values()),None
        except AssertionError as exc:
            return False,0,'fuel' if str(exc)=='symbolic fuel exhausted' else str(exc)[:180]
        except KeyError:return False,0,'missing_transition'
    usage=collections.defaultdict(set);cost={}
    for i in range(len(cases)):
        traced=Table(table,track=True);ok,c,_=check(traced,i);assert ok,('baseline',i);cost[i]=c
        for k in traced.used:usage[k].add(i)
    q,h,tape,_,_=audit.run_prefix(audit.read_table(raw),82552)
    spares=[0]*65;spares[8]=1
    assert (q,h,tape)==(96,2,audit.paint('',40,[0]*9,spares,2))
    return table,audit,cases,check,usage,cost

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--seconds',type=float,default=600);ap.add_argument('--fuel',type=int,default=1000)
    ap.add_argument('--degree',type=int,default=2);ap.add_argument('--deletions',type=str);ap.add_argument('--resume',type=Path)
    args=ap.parse_args();assert __debug__ and args.fuel>0
    started=time.monotonic();table,audit,cases,check,usage,cost=setup(args.repo,args.fuel)
    states=sorted({q for q,b in table},key=int);protected={(str(q),b) for q,b in audit.BOX_PAIRS}
    protected_targets={table[k][2] for k in protected}
    eligible=[q for q in states if q not in {'64','96'}|protected_targets and all((q,b) not in protected for b in (0,1))]
    incoming={q:sorted([k for k,(_,_,t) in table.items() if t==q and k[0]!=q],key=lambda k:(int(k[0]),k[1])) for q in eligible}
    family=[q for q in eligible if len(incoming[q])==args.degree and all(k not in protected and k[0]!='96' for k in incoming[q])]
    if args.deletions:
        allowed=set(args.deletions.split(','));family=[q for q in family if q in allowed]
    family.sort(key=lambda q:(q!='107',int(q)))
    affected={q:sorted(set.union(*(usage[k] for k in incoming[q])),key=lambda i:(cost[i],i)) for q in family}
    actions={q:list(itertools.product((0,1),('L','R'),[t for t in states if t!=q])) for q in family}
    domain=4*(len(states)-1);assert domain==1004
    stack=[(q,{}) for q in reversed(family)]
    groups={q:{'deleted_old':int(q),'incoming':[list(k) for k in incoming[q]],'planned':domain**args.degree,'pruned':0,'partial_nodes':0,'symbolic_checks':0,'survivors':0} for q in family}
    result={'status':'running','research_date':'2026-10-17','source_revision':'beb2c633ae57a0883d28fb6d0c75342d08cfdeda','baseline_sha256':audit.EXPECTED_SHA,'baseline_states':252,'baseline_cases':8391,'baseline_boot_steps':82552,'baseline_checks':'PASS','candidate_states':251,'domain_per_incoming_row':domain,'degree':args.degree,'planned':len(family)*domain**args.degree,'pruned':0,'partial_nodes':0,'checks':0,'survivors':[],'groups':list(groups.values()),'fuel':args.fuel,'seconds_limit':args.seconds,'claim':'Finite conditional symbolic diagnostic only; rejection is not semantic impossibility. Any positive result needs independent proof and blank initialization.','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    args.output.parent.mkdir(parents=True,exist_ok=True);digest=hashlib.sha256();failures=collections.Counter()
    if args.resume:
        prev=json.loads(args.resume.read_text())
        assert prev['baseline_sha256']==audit.EXPECTED_SHA and prev['degree']==args.degree and prev['domain_per_incoming_row']==domain
        stack=[(str(e['deleted_old']),{int(i):tuple(v) for i,v in e['assigned_actions'].items()}) for e in reversed(prev['frontier'])]
        for k in ('pruned','partial_nodes','checks','survivors'):result[k]=prev[k]
        for g in prev['groups']:groups[str(g['deleted_old'])].update(g)
        failures.update(prev['failures']);digest.update(('resumed:'+prev['event_digest_sha256']).encode())
        result['prior_elapsed_seconds']=prev['elapsed_seconds'];result['prior_event_digest']=prev['event_digest_sha256']
    weight=lambda a:domain**(args.degree-len(a))
    def save():
        result['elapsed_seconds']=time.monotonic()-started
        result['frontier']=[{'deleted_old':int(q),'assigned_actions':{str(i):list(v) for i,v in a.items()},'completions':weight(a)} for q,a in reversed(stack)]
        result['remaining']=sum(weight(a) for q,a in stack)
        assert result['planned']==result['pruned']+len(result['survivors'])+result['remaining']
        result['failures']=dict(failures);result['event_digest_sha256']=digest.hexdigest()
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'baseline':'8391 cases and exact 82552 steps passed','states':list(map(int,family)),'planned':result['planned']}),flush=True);save()
    last_report=time.monotonic()
    while stack and time.monotonic()-started<args.seconds:
        dead,assign=stack.pop();g=groups[dead];keys=incoming[dead]
        current=Table(table,deleted=dead,pending={k:i for i,k in enumerate(keys) if i not in assign},assigned={keys[i]:a for i,a in assign.items()})
        failed=reason=need=None;count=0
        try:
            for i in affected[dead]:
                ok,_,reason=check(current,i);count+=1
                if not ok:failed=i;break
            if failed is None:
                for i in range(len(cases)):
                    ok,_,reason=check(current,i);count+=1
                    if not ok:failed=i;break
        except NeedRow as req:need=req.index
        result['partial_nodes']+=1;g['partial_nodes']+=1;result['checks']+=count;g['symbolic_checks']+=count
        event=[int(dead),sorted(assign.items()),need,failed,reason]
        digest.update((json.dumps(event,separators=(',',':'))+'\n').encode())
        if need is not None:
            for a in reversed(actions[dead]):stack.append((dead,{**assign,need:a}))
        elif failed is not None:
            n=weight(assign);g['pruned']+=n;result['pruned']+=n;failures[str(reason)]+=1
        elif len(assign)<args.degree:
            need=next(i for i in range(args.degree) if i not in assign)
            for a in reversed(actions[dead]):stack.append((dead,{**assign,need:a}))
        else:
            candidate={k:v for k,v in table.items() if k[0]!=dead};candidate.update({keys[i]:a for i,a in assign.items()})
            assert len(candidate)==502 and all(t!=dead for _,_,t in candidate.values())
            assert all(candidate[k]==table[k] for k in protected)
            out=args.output.parent/f'candidate251-delete{dead}-{len(result["survivors"])}.tm'
            data='#! start 64\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(candidate.items(),key=lambda x:(int(x[0][0]),x[0][1])))
            out.write_text(data);g['survivors']+=1
            record={'deleted':int(dead),'actions':{str(i):list(a) for i,a in assign.items()},'table':str(out),'sha256':hashlib.sha256(data.encode()).hexdigest()}
            result['survivors'].append(record);print('SURVIVOR '+json.dumps(record),flush=True)
        if time.monotonic()-last_report>=20:
            save();print(json.dumps({'dead':dead,'nodes':result['partial_nodes'],'pruned':result['pruned'],'remaining':result['remaining'],'seconds':round(result['elapsed_seconds'],1)}),flush=True);last_report=time.monotonic()
    result['status']='complete' if not stack else 'time_bounded_partial';save()
    print(json.dumps({k:result[k] for k in ['status','planned','pruned','remaining','partial_nodes','checks','survivors','elapsed_seconds']}),flush=True)

if __name__=='__main__':main()
