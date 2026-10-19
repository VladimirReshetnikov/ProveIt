#!/usr/bin/env python3
"""Finite affine search on a new composition of two 246-state controls.

Each candidate preserves all 42 mathematical macro-support rows. Every survivor
must pass all 8391 guarded instruction cases. A diagnostic rejection does not
prove inequivalence or a state lower bound.
"""
from pathlib import Path
from collections import defaultdict,Counter
import importlib.util,sys,json,time,hashlib,argparse

ROOT=Path(__file__).resolve().parents[1]
HERE=ROOT/'results'
sys.path.insert(0,str(ROOT/'vendor/code'))
import prefix_affine as affine
import review_affine_source as review
import check_macro_inductions as macro

def read(path):
    table={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();table[q,int(b)]=(int(w),d,t)
    return table

class Tracked(dict):
    def __init__(self,table):super().__init__(table);self.used=set()
    def __getitem__(self,key):self.used.add(key);return super().__getitem__(key)

def cases(sites):
    for p,op,v in sites:
        for zero in ((True,False) if op=='CD' else (None,)):
            guard=(v,zero) if op=='CD' else None
            extra=0;effect=None;overflow=False
            if op=='CI':nxt,overflow=review.full_inc(p);effect=('inc',v)
            elif op=='CD' and not zero:nxt,overflow=review.full_inc(p);effect=('dec',v);extra=1
            elif op=='CD':nxt,overflow=review.full_inc(review.full_strip(p,'0',1))
            elif op=='CB':nxt,overflow=review.full_inc(review.full_strip(p,'0',v))
            elif op=='CC':nxt=review.full_strip(p,'1',v)
            else:nxt=''
            target=affine.canon([('b',1)],[('b',int(c)) for c in nxt]+[
                ('r',0,1,40+extra+int(overflow)-len(nxt)),('b',1),('box',('plain',effect))])
            yield p,guard,target,op=='CH'

def check(t,c):
    rules,steps=affine.run(t,*c[:3],halt=c[3],fuel=1500)
    assert steps>0
    return sum(rules.values())

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--table',type=Path,default=ROOT/'machine/zfc_composed246_old.tm')
    parser.add_argument('--sites',type=Path,default=ROOT/'sources/rotated-sites-physical.json')
    parser.add_argument('--output',type=Path,default=ROOT/'results/composed_merge_rerun.json')
    parser.add_argument('--all-pairs',action='store_true')
    args=parser.parse_args()
    assert __debug__
    started=time.monotonic();table=read(args.table)
    cc=list(cases(json.loads(args.sites.read_text())));assert len(cc)==8391
    mt=Tracked({(int(q),b):(w,d,int(t)) for (q,b),(w,d,t) in table.items()})
    macro.TABLE=mt;macro.DERIVED.clear();macro.BLOCK_PROOFS.clear();macro.WORD_IDENTITY_PROVED=False
    macro.prove_blocks();macro.prove_word_identity();macro.prove_macros();macro.prove_marks()
    protected={(str(q),b) for q,b in mt.used};assert len(protected)==42
    usage=defaultdict(set);cost=[]
    for i,c in enumerate(cc):
        t=Tracked(table);cost.append(check(t,c))
        for row in t.used:usage[row].add(i)
    print('Baseline 8391 guards and 42-row macro proof PASS',flush=True)
    states=sorted({q for q,b in table},key=int)
    forbidden={'96'}|{q for q,b in protected}|{table[row][2] for row in protected}
    changed={'13','19','29','41','58','74','178','208','218','237'}
    recipes=[]
    for dead in states:
        if dead in forbidden:continue
        for keep in states:
            if dead==keep:continue
            if not args.all_pairs and dead not in changed and keep not in changed:continue
            recipes.append((dead,keep,None))
            for bit in (0,1):
                if keep=='96' or (keep,bit) in protected:continue
                if table[dead,bit]==table[keep,bit]:continue
                recipes.append((dead,keep,bit))
    result={'status':'running','scope':'Finite conditional affine fold search; no sub246 consistency claim.',
            'table_sha256':hashlib.sha256(args.table.read_bytes()).hexdigest(),
            'sites_sha256':hashlib.sha256(args.sites.read_bytes()).hexdigest(),
            'baseline_guarded_cases':len(cc),'protected_macro_rows':len(protected),
            'recipes':len(recipes),'completed':0,'case_checks':0,'survivors':[],'failures':[],
            'changed_states':sorted(map(int,changed)),'family':'all-pairs' if args.all_pairs else 'touch-a-changed-state'}
    failures=Counter()
    for dead,keep,bit in recipes:
        t={(q,b):(w,d,keep if s==dead else s) for (q,b),(w,d,s) in table.items() if q!=dead}
        if bit is not None:
            w,d,s=table[dead,bit];t[keep,bit]=(w,d,keep if s==dead else s)
        assert all(t[row]==table[row] for row in protected)
        affected=usage[dead,0]|usage[dead,1]
        if bit is not None:affected=affected|usage[keep,bit]
        failed=None;why=None
        for i in sorted(affected,key=cost.__getitem__):
            result['case_checks']+=1
            try:check(t,cc[i])
            except (AssertionError,KeyError) as e:failed=i;why=type(e).__name__;break
        if failed is None:
            for i,c in enumerate(cc):
                result['case_checks']+=1
                try:check(t,c)
                except (AssertionError,KeyError) as e:failed=i;why=type(e).__name__;break
        if failed is None:
            item=[int(dead),int(keep),bit]
            result['survivors'].append(item);print('SURVIVOR',item,flush=True)
            raw=f'#! start {keep if dead=="95" else "95"}\n'+''.join(f'{q} {b} {w} {d} {s}\n' for (q,b),(w,d,s) in sorted(t.items(),key=lambda kv:(int(kv[0][0]),kv[0][1])))
            (HERE/f'composed245_{dead}_{keep}_{bit}.tm').write_text(raw)
        else:
            failures[why]+=1;result['failures'].append([int(dead),int(keep),bit,failed,why])
        result['completed']+=1
        if result['completed']%10000==0:print('Progress',result['completed'],round(time.monotonic()-started,2),flush=True)
    result.update(status='completed',failure_reasons=dict(failures),seconds=time.monotonic()-started)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='failures'},indent=2),flush=True)

if __name__=='__main__':main()
