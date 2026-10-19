#!/usr/bin/env python3
"""Exact-table universal runtime replay, with a pure state-name adapter.

Proof rules are the unchanged inherited symbolic_runtime.py. The adapter
renames five routine entries plus the halt; it neither changes transitions
nor skips machine steps. Source calibration and blank startup are separate.
"""
from pathlib import Path
import argparse, hashlib, json, sys, time

ROOT=Path(__file__).resolve().parents[1]
ENGINE=Path(__file__).resolve().parent/'engine'
sys.path.insert(0,str(ENGINE))
import symbolic_runtime as s

def require(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read_table(p):
    t={};start=None
    for ln in p.read_text().splitlines():
        if ln.startswith('#! start '):start=int(ln[9:])
        elif ln and not ln.startswith('#'):
            q,b,w,d,z=ln.split();q,b,w,z=map(int,(q,b,w,z))
            require((q,b) not in t and b in (0,1) and w in (0,1) and d in ('L','R'),'malformed row')
            t[q,b]=(w,1 if d=='R' else -1,z)
    qs={q for q,b in t};halts={z for w,d,z in t.values()}-qs
    require(start==0 and len(halts)==1 and set(t)=={(q,b) for q in qs for b in (0,1)},'table census')
    return t,start,next(iter(halts))
def read_sites(p):
    rows=json.loads(p.read_text())
    if len(rows[0])==3:return rows
    codes={'EInc':'CI','EDecnz':'CD','EBreak':'CB','EContinue':'CC','EHalt':'CH'}
    out=[]
    for path,instr in rows:
        v=instr.split();out.append([path,codes[v[0]],int(v[1]) if len(v)>1 else None])
    return out

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--table',type=Path,required=True);ap.add_argument('--sites',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True);ap.add_argument('--limit',type=int,default=0)
    a=ap.parse_args();require(__debug__ and not sys.flags.optimize,'assertions disabled')
    old,start,halt=read_table(a.table);ss=read_sites(a.sites)
    anchors={0:95,84:96,64:73,40:48,97:112,halt:254}
    states={q for q,b in old}|{halt};mp={q:anchors.get(q,300+q) for q in states}
    require(len(set(mp.values()))==len(mp),'noninjective adapter')
    inverse={v:k for k,v in mp.items()};table={(mp[q],b):(w,d,mp[z]) for(q,b),(w,d,z) in old.items()}
    require(all(0<len(pc)<=64 and set(pc)<={'0','1'} for pc,o,r in ss),'source paths')
    leaves={pc for pc,o,r in ss};prefixes={pc[:k] for pc in leaves for k in range(len(pc))}
    require(len(leaves)==len(ss) and not leaves&prefixes and all(p+b in leaves|prefixes for p in prefixes for b in '01'),'source tree')
    expected=sum(2 if x[1]=='CD' else 1 for x in ss)
    report=dict(status='IN_PROGRESS',working_states=len(old)//2,rows=len(old),expected_cases=expected,
        table_sha256=sha(a.table),sites_sha256=sha(a.sites),engine_sha256=sha(s.__file__),helper_sha256=sha(s.r.__file__),
        driver_sha256=sha(__file__),adapter={str(k):v for k,v in sorted(mp.items())},
        scope='All independent natural primary values, every zero/positive decrement guard, arbitrary natural gap, arbitrary first spare and finite spare tail. Exact whole tape and source successor; positive duration. Ordinary mathematical certificate.',
        proof_construction_limit=4000,actual_runtime_bound=None)
    a.output.parent.mkdir(parents=True,exist_ok=True);began=time.monotonic();cases=[];used=set()
    def save():
        report.update(cases=len(cases),seconds=time.monotonic()-began)
        a.output.write_text(json.dumps(report,indent=2)+'\n')
    try:
        lemmas,blocks=s.prove_blocks(table);report['list_induction_blocks']=blocks
        for index,site in enumerate(ss):
            for positive in ((False,True) if site[1]=='CD' else (False,)):
                ans=s.case(table,lemmas,site,positive)
                used.update((inverse[q],b) for q,b in ans.pop('rows'));ans.pop('trace')
                cases.append(dict(site_index=index,positive=positive,**ans))
                if len(cases)%1000==0:save();print('proved',len(cases),'of',expected,flush=True)
                if a.limit and len(cases)>=a.limit and len(cases)<expected:
                    report['status']='PARTIAL_PREFIX_PASS';save();return
        casepath=a.output.with_name(a.output.stem+'_cases.json');casepath.write_text(json.dumps(cases,indent=2)+'\n')
        report.update(status='UNIVERSAL_MATHEMATICAL_PASS',symbolic_steps=sum(x['symbolic_steps'] for x in cases),
            maximum_symbolic_steps=max(x['symbolic_steps'] for x in cases),minimum_actual_steps=min(x['duration'][0] for x in cases),
            used_rows=sorted(used),unused_rows=sorted(set(old)-used),cases_file=casepath.name,cases_sha256=sha(casepath))
        save();print(json.dumps({k:v for k,v in report.items() if k not in ('adapter','list_induction_blocks','used_rows')},indent=2),flush=True)
    except Exception as e:
        report.update(status='NOT_PROVED',site_index=locals().get('index'),site=locals().get('site'),positive=locals().get('positive'),error=repr(e));save();raise
if __name__=='__main__':main()
