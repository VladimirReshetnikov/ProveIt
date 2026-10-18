#!/usr/bin/env python3
"""Diagnostic one-incoming-action deletion search on the exact context246 table.

Uses the attributed prefix250/246 affine checker; its four universal box
contracts remain protected. A successful check is a conditional macro theorem,
not an independently formalized endpoint.
"""
from pathlib import Path
import importlib.util, json, time, argparse, gzip
from collections import Counter

ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/'baseline246/zfc-context246'
def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
review=module('review',BASE/'code/review_affine_source.py')
affine=module('affine',BASE/'sources/prior/prefix_affine.py')
T=review.read_tm(BASE/'machine/zfc_prefix246_old.tm')
_,sites=review.parse_source(BASE/'sources/Prog254.v')

def cases():
    for p,op,r in sites:
        for zero in ((True,False) if op=='CD' else (None,)):
            branch=(r,zero) if op=='CD' else None
            extra,effect,overflow=0,None,False
            if op=='CI':succ,overflow=review.full_inc(p);effect=('inc',r)
            elif op=='CD' and not zero:
                succ,overflow=review.full_inc(p);effect=('dec',r);extra=1
            elif op=='CD':succ,overflow=review.full_inc(review.full_strip(p,'0',1))
            elif op=='CB':succ,overflow=review.full_inc(review.full_strip(p,'0',r))
            elif op=='CC':succ=review.full_strip(p,'1',r)
            else:succ=''
            right=[('b',int(b)) for b in succ]+[('r',0,1,40+extra+int(overflow)-len(succ)),('b',1),('box',('plain',effect))]
            yield p,op,r,zero,branch,affine.canon([('b',1)],right)
CASES=list(cases())
class TraceTable(dict):
    def __getitem__(self,k):
        self.used.add(k);return super().__getitem__(k)
    def __init__(self,table):super().__init__(table);self.used=set()
def check(table,i):
    p,op,r,zero,branch,target=CASES[i]
    return affine.run(table,p,branch,target,halt=op=='CH',fuel=1200)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=600)
    ap.add_argument('--states',type=str);args=ap.parse_args()
    if not __debug__:raise SystemExit('Assertions required')
    started=time.monotonic();traced=TraceTable(T);usage=[]
    for i in range(len(CASES)):
        traced.used=set();check(traced,i);usage.append(traced.used)
    print('Baseline PASS',len(CASES),'cases',time.monotonic()-started,flush=True)
    # The four box contracts may invoke these rows on arbitrarily large blocks.
    box_states=set(map(str,[2,4,6,20,28,31,38,40,44,48,56,60,63,64,69,73,75,83,95,109,112,131,255]))
    # Extract finite literal support from the four universal block/list
    # induction derivations, not merely from a finite sample footprint.
    proof=json.loads((BASE/'results/macro-inductions.json').read_text())
    protected=set()
    def walk(value):
        if isinstance(value,dict):
            if value.get('rule') in ('literal','unary-induction'):
                k=(str(value['state']),value['read'])
                assert T[k]==(value['row'][0],value['row'][1],str(value['row'][2]))
                protected.add(k)
            for child in value.values():walk(child)
        elif isinstance(value,list):
            for child in value:walk(child)
    walk(proof)
    protected_targets={T[k][2] for k in protected}
    states=sorted({q for q,b in T},key=int)
    candidates=[]
    for q in states:
        if q in box_states|protected_targets|{'95','96'}:continue
        inc=[k for k,row in T.items() if row[2]==q and k[0]!=q]
        if len(inc)!=1 or inc[0] in protected:continue
        if args.states and int(q) not in set(map(int,args.states.split(','))):continue
        candidates.append((q,inc[0]))
    out=ROOT/'experiments/action_search';out.mkdir(exist_ok=True)
    stats=Counter();survivors=[];done=[];stopped=False
    with gzip.open(out/'ledger.jsonl.gz','wt') as journal:
        for q,key in candidates:
            affected={key,(q,0),(q,1)}
            ids=[i for i,u in enumerate(usage) if u&affected]
            assert ids
            old=T[key]
            for w in (0,1):
                for d in ('L','R'):
                    for r in states+['254']:
                        if r==q:continue
                        if time.monotonic()-started>args.seconds:
                            stopped=True;break
                        # Delete q and replace its only incoming action. The
                        # deleted state's self-loops disappear with its rows.
                        mutant={k:v for k,v in T.items() if k[0]!=q}
                        mutant[key]=(w,d,r)
                        failed=None
                        for at,i in enumerate(ids):
                            stats['case_checks']+=1
                            try:check(mutant,i)
                            except (AssertionError,KeyError) as e:
                                failed=(i,str(e));ids.insert(0,ids.pop(at));break
                        stats['recipes']+=1
                        if failed is None:
                            # Recheck the full set on every apparent survivor.
                            try:
                                for i in range(len(CASES)):check(mutant,i)
                            except (AssertionError,KeyError) as e:
                                raise AssertionError(('footprint pruning error',q,key,(w,d,r),i,str(e)))
                            item=dict(deleted=q,incoming=list(key),action=[w,d,r],all_cases=len(CASES))
                            survivors.append(item)
                            name=f'delete{q}-{key[0]}-{key[1]}-{w}{d}{r}.tm'
                            (out/name).write_text('#! start 95\n'+''.join(f'{a} {b} {x} {y} {z}\n' for (a,b),(x,y,z) in sorted(mutant.items(),key=lambda z:(int(z[0][0]),z[0][1]))))
                            print('SURVIVOR',item,flush=True)
                        journal.write(json.dumps([q,list(key),[w,d,r],failed],separators=(',',':'))+'\n')
                    if stopped:break
                if stopped:break
            if stopped:break
            done.append(q);print('Finished',q,'recipes',stats['recipes'],'checks',stats['case_checks'],'seconds',round(time.monotonic()-started,2),flush=True)
    result=dict(status='partial' if stopped else 'complete',seconds=time.monotonic()-started,stats=dict(stats),baseline_cases=len(CASES),states_planned=[q for q,k in candidates],states_completed=done,survivors=survivors,protected_rows=sorted(protected),scope='Conditional universal affine checks with unchanged four box contracts; search failures are not impossibility theorems.')
    (out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
