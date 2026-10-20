#!/usr/bin/env python3
"""Reproduce small transition-usage receipts for the generic and all-one spare frames.

The all-one specialization changes exactly two expressions in the pinned
symbolic runtime checker.  Its finite-list lemma then ranges over lists of
B(1), and the separately represented first spare is also B(1).  No new
induction rule is added.  This is a usage audit, not blank-run reachability.
"""
import argparse,importlib.util,hashlib,json,sys,time
import context as c

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--uniform',action='store_true');args=ap.parse_args()
    vendor=c.P/'runtime/vendor';sys.path.insert(0,str(vendor))
    original=vendor/'symbolic_runtime.py';source=original.read_text()
    if args.uniform:
        changes=[('lemmas={};certificates=[];v=var(2)','lemmas={};certificates=[];v=num(1)'),
                 ('atoms+=block(var(11))+[tail()]','atoms+=block(num(1))+[tail()]')]
        for old,new in changes:
            assert source.count(old)==1
            source=source.replace(old,new)
    out=c.OUT/'spare_usage';out.mkdir(exist_ok=True)
    modulefile=out/('uniform_runtime.py'if args.uniform else'generic_runtime.py')
    modulefile.write_text('# Adaptation of the pinned K221 symbolic checker; see package attribution.\n'+source)
    spec=importlib.util.spec_from_file_location('runtime_audit',modulefile)
    s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)
    ref=c.P/'runtime/reference_results'
    table=s.r.table(ref/'candidate.legacy.tm')
    sites=json.loads((ref/'sites.json').read_text())
    inv=json.loads((ref/'invariants.json').read_text())['states']
    lemmas,_=s.prove_blocks(table);used=set();first={};cases=0;started=time.monotonic()
    for i,site in enumerate(sites):
        if inv[i]is None:continue
        for positive in ((False,True)if site[1]=='CD'else(False,)):
            if site[1]=='CD' and not inv[i][site[2]]&(510 if positive else 1):continue
            ans=s.case(table,lemmas,site,positive);cases+=1
            for row in ans['rows']:
                r=tuple(row);used.add(r);first.setdefault(','.join(map(str,r)),[i,positive])
    missing=sorted(set(table)-used)
    result={'status':'SYMBOLIC_SOURCE_INTERFACE_USAGE_AUDIT','uniform_spares':args.uniform,
            'cases':cases,'used_transition_rows':len(used),'unused_transition_rows':missing,
            'baseline_runtime_sha256':hashlib.sha256(original.read_bytes()).hexdigest(),
            'first_symbolic_case_per_row':first,'seconds':time.monotonic()-started,
            'scope':'Rows appearing in the symbolic traces of the retained source-frame cases. These are not claims of exact initialized reachability.'}
    assert len(used)==442 and not missing
    dest=out/('uniform_receipt.json'if args.uniform else'generic_receipt.json')
    dest.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k!='first_symbolic_case_per_row'}),flush=True)

if __name__=='__main__':main()
