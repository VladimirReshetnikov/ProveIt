#!/usr/bin/env python3
"""Audit an arbitrary old-label table against a separately certified source tree.

The full macro induction checker is rerun on this exact table before affine
oracles are admitted.  The register-program bisimulation is inherited from the
source_sites certificate; this tool does not silently change source paths.
State labels 95, 96 and 254 denote start, dispatcher and halt respectively.
"""
import argparse
from pathlib import Path
import time

import build_routing_machine as build
import check_macro_inductions as induction
import parametric_prefix_affine as affine
from parametric_affine_driver import check_sites


def macro_audit(table):
    induction.TABLE = table
    induction.WORD_IDENTITY_PROVED = False
    induction.DERIVED.clear()
    induction.BLOCK_PROOFS.clear()
    induction.prove_blocks()
    word = induction.prove_word_identity()
    macros = induction.prove_macros()
    marks = induction.prove_marks()
    return dict(status='PASS', block_theorems=list(induction.BLOCK_PROOFS.values()),
                word_identity=word, macro_theorems=macros, mark_theorems=marks,
                scope='Universal unary and finite-list induction templates rerun on the actual proposed table; no kernel endpoint.')


def audit_existing_machine(table_path, sites_path, padding=64, boot_limit=500000,
                           output=None):
    import json
    began=time.monotonic()
    table_path,sites_path=Path(table_path),Path(sites_path)
    table,start=build.rebuild.read_table(table_path)
    states={q for q,b in table}
    assert start==95 and 95 in states and 96 in states
    assert len(table)==2*len(states)
    assert {q for w,d,q in table.values()}-states=={254}
    sites=json.loads(sites_path.read_text())
    assert len(sites)==6460 and len({p for p,op,r in sites})==6460
    assert padding>=max(len(p) for p,op,r in sites)
    result=dict(status='PENDING',working_states=len(states),table_sha256=build.digest(table_path),
                sites_sha256=build.digest(sites_path),padding=padding,
                source_scope='Same complete source instruction paths as the supplied previously certified sites file; no source modification.')
    try:
        macros=macro_audit(table)
        result['macro_inductions']={k:v for k,v in macros.items() if k not in ('block_theorems','macro_theorems','mark_theorems')}
        if output is not None:
            Path(output).mkdir(parents=True,exist_ok=True)
            build.write_json(Path(output)/'macro-inductions.json',macros)
    except Exception as e:
        result['macro_inductions']=dict(status='FAIL',error=repr(e))
    if result['macro_inductions']['status']=='PASS':
        affine.PADDING=padding
        current={}
        native_run=affine.run
        def tracked(*a,**k):
            current.update(pc=a[1],branch=a[2])
            return native_run(*a,**k)
        affine.run=tracked
        try:
            checks=build.review.check_oracle(affine)
            result['affine_all_cases']=dict(status='PASS',oracle_gate_checks=checks,
                **check_sites(affine,{(str(q),b):(w,d,str(t)) for(q,b),(w,d,t)in table.items()},sites,padding))
        except Exception as e:
            result['affine_all_cases']=dict(status='FAIL',first_bad_case=current.copy(),error=repr(e))
        finally:
            affine.run=native_run
    result['blank_boot']=build.sparse_boot(table,boot_limit,minimum_gap=padding)
    if output is not None and result['blank_boot']['status']=='PASS':
        build.write_json(Path(output)/'blank_boot.json',result['blank_boot'])
    result['blank_boot']={k:v for k,v in result['blank_boot'].items() if k not in ('all_one_positions','spare_values','used_rows')}
    affine_status=result.get('affine_all_cases',{}).get('status')
    if affine_status=='PASS':
        result['status']='PASS_AFFINE_AND_BOOT' if result['blank_boot']['status']=='PASS' else 'RUNTIME_PASS_BOOT_UNRESOLVED'
    else:
        result['status']='FAIL'
    result['seconds']=time.monotonic()-began
    if output is not None:
        Path(output).mkdir(parents=True,exist_ok=True)
        build.write_json(Path(output)/'existing-machine-audit.json',result)
    return result


def main():
    import json
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('table',type=Path)
    ap.add_argument('sites',type=Path)
    ap.add_argument('output',type=Path)
    ap.add_argument('--padding',type=int,default=64)
    ap.add_argument('--boot-limit',type=int,default=500000)
    args=ap.parse_args()
    result=audit_existing_machine(args.table,args.sites,args.padding,args.boot_limit,args.output)
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
