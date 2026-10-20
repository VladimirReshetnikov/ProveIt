#!/usr/bin/env python3
"""Audit the seven-zero scanner on every source case without six PC zeros.

This deliberately records failures and excluded cases; a pass is conditional
on the displayed PC restriction, and is not an accepted blank-machine proof.
"""
from pathlib import Path
import argparse, hashlib, json, sys, time

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('table',type=Path)
    ap.add_argument('sites',type=Path)
    ap.add_argument('output',type=Path)
    ap.add_argument('--proof-root',type=Path,required=True,
                    help='The extracted retained K225 portable/baseline226 directory')
    a=ap.parse_args()
    portable=a.proof_root.resolve()
    sys.path.insert(0,str(portable))
    import build
    sys.path.insert(0,str(portable/'vendor/proveit'))
    import symbolic_runtime as engine
    build.require(__debug__ and not sys.flags.optimize,'Assertions must be enabled')
    build.require(sha(portable/'vendor/proveit/symbolic_runtime.py')==
                  'c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145','Changed proof engine')
    build.require(sha(portable/'vendor/proveit/independent_runtime.py')==
                  '0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346','Changed proof helper')
    table=build.parse(a.table.read_bytes(),95,254)
    m=json.loads((portable/'source/legacy_state_map.json').read_text())['k230_to_old']
    q34,q50,q75=(m[str(q)] for q in (34,50,75))
    assert table[q34,0]==(0,-1,q50)
    assert table[q50,0]==(0,-1,q75)
    table[q34,0]=(0,-1,q75)
    del table[q50,0],table[q50,1]
    assert not any(t==q50 for w,d,t in table.values())
    sites=json.loads(a.sites.read_text())
    root=build.source.tree(sites)
    build.require(sites==[list(x) for x in build.source.sites(root)],'Source is not in tree order')
    ordered,graph,entry=build.source.graph(sites)
    build.require([list(x) for x in ordered]==sites and entry==0,'Unexpected source order or entry')
    original=sum(2 if op=='CD' else 1 for pc,op,arg in sites)
    badpcs=[s for s in sites if '000000' in s[0]]
    omitted=sum(2 if op=='CD' else 1 for pc,op,arg in badpcs)
    result=dict(status='RUNNING',original_table_sha256=sha(a.table),source_sha256=sha(a.sites),
                engine_sha256=sha(portable/'vendor/proveit/symbolic_runtime.py'),
                helper_sha256=sha(portable/'vendor/proveit/independent_runtime.py'),
                checker_sha256=sha(Path(__file__)),
                changed_row=[q34,0,0,-1,q75],removed_state=q50,
                normalized_changed_row=[34,0,0,-1,75],normalized_removed_state=50,
                source_leaves=len(sites),original_cases=original,excluded_cases=omitted,
                excluded_sites=badpcs,remaining_cases=original-omitted,
                scope='All natural registers and arbitrary finite spare tails for exactly the source PCs with no six consecutive zeros. Blank initialization is a separate obligation.')
    started=time.monotonic(); passed=[]; failed=[]
    def save():
        result.update(seconds=time.monotonic()-started,passed_count=len(passed),failed_count=len(failed),failed=failed)
        a.output.write_text(json.dumps(result,indent=2)+'\n')
    try:
        lemmas,blocks=engine.prove_blocks(table)
        result['blocks']=blocks
        for i,s in enumerate(sites):
            if '000000' in s[0]: continue
            for positive in ((False,True) if s[1]=='CD' else (False,)):
                try:
                    r=engine.case(table,lemmas,s,positive)
                    r.pop('trace'); r.pop('rows')
                    passed.append(dict(site_index=i,positive=positive,**r))
                except Exception as e:
                    failed.append(dict(site_index=i,site=s,positive=positive,error=repr(e)))
                    print('FAIL',failed[-1],flush=True)
                if (len(passed)+len(failed))%500==0:
                    save(); print('CASES',len(passed)+len(failed),'of',original-omitted,'FAIL',len(failed),flush=True)
        assert len(passed)+len(failed)==original-omitted
        result['status']='CONDITIONAL_UNIVERSAL_PASS' if not failed else 'CONDITIONAL_FAILED'
        casefile=a.output.with_name(a.output.stem+'_cases.json')
        casefile.write_text(json.dumps(passed,separators=(',',':'))+'\n')
        result.update(cases_file=casefile.name,cases_sha256=sha(casefile))
        save(); print(json.dumps({k:v for k,v in result.items() if k not in ('blocks','failed','excluded_sites')},indent=2),flush=True)
    except Exception as e:
        result.update(status='PROOF_ENGINE_FAILED',error=repr(e));save();raise

if __name__=='__main__':main()
