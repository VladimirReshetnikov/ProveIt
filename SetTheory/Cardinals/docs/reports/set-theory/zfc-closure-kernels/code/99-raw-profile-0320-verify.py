#!/usr/bin/env python3
"""Independent structural audits and optional literal-control rebuild.

Run without Python -O: the inherited checkers deliberately use assertions.
The quick default does not stand in for the optional whole-frame theorem.
"""
import argparse, hashlib, json, subprocess, sys, tempfile
from pathlib import Path

ROOT=Path(__file__).resolve().parent

def run(command):
    subprocess.run([str(x) for x in command],check=True)

def main():
    if not __debug__:
        raise SystemExit('Run with assertions enabled; do not use Python -O.')
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--build-control',action='store_true')
    p.add_argument('--whole-frame',action='store_true')
    p.add_argument('--output',type=Path)
    p.add_argument('--search',choices=['dne32','local024','masksATF','unambiguous','masks14','masks14_unlock'])
    p.add_argument('--seconds',type=float,default=60)
    p.add_argument('--iterations',type=int,default=0)
    args=p.parse_args()
    out=args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='joint-grammar-'))
    out.mkdir(parents=True,exist_ok=True)
    sys.path.insert(0,str(ROOT/'runtime/code'))
    from audit_fine_grammar import audit
    reports=[]
    for folder in sorted((ROOT/'experiments').iterdir()):
        if not (folder/'candidate.json').exists():continue
        for name in ['seed.json','candidate.json']:
            result=audit(folder/name,short_scan=True)
            assert result['working_states']>=245
            reports.append(dict(family=folder.name,input=name,status=result['status'],
                rules=result['grammar_states'],properties=result['search_AST_properties']))
    control=audit(ROOT/'control245/grammar.json',short_scan=True)
    assert control['working_states']==245 and control['grammar_states']==128
    # The rejected unlocked candidate has an exact finite witness followed by
    # a one-row induction; no long simulation cutoff is used for this result.
    bad=ROOT/'rejected245'
    trap_checked=False
    if (bad/'blank-ray-trap.json').exists():
        trap=json.loads((bad/'blank-ray-trap.json').read_text())
        table={}
        for line in (bad/'machine_old.tm').read_text().splitlines():
            if line and not line.startswith('#'):
                q,b,w,d,n=line.split();table[int(q),int(b)]=(int(w),d,int(n))
        q,head,ones=95,0,set()
        for _ in range(trap['prefix_steps']):
            w,d,n=table[q,int(head in ones)]
            if w:ones.add(head)
            else:ones.discard(head)
            head+=1 if d=='R' else -1;q=n
        assert (q,head,sorted(ones))==(trap['state'],trap['head'],trap['ones'])
        assert head>max(ones) and table[q,0]==(1,'R',q)
        trap_checked=True
    if args.build_control:
        run([sys.executable,'-B',ROOT/'runtime/code/build_source_machine.py',ROOT/'control245/grammar.json',
             out/'control245','--short-scan','--padding','64'])
        expected=json.loads((ROOT/'control245/machine-audit.json').read_text())
        actual=json.loads((out/'control245/machine-audit.json').read_text())
        for key in ['canonical_sha256','table_sha256','working_states','source_leaves','expected_guarded_cases']:
            assert actual[key]==expected[key],key
        assert actual['affine_all_cases']['status']=='PASS'
        assert actual['blank_boot']['blank_steps']==407995
    if args.whole_frame:
        run([sys.executable,'-B',ROOT/'code/whole_frame_dynamic.py','--runtime',ROOT/'runtime',
             '--table',ROOT/'control245/machine_old.tm','--sites',ROOT/'control245/sites_physical.json',
             '--source-reference',ROOT/'control245/modified_source.json','--padding','64',
             '--output',out/'whole-frame.json'])
        result=json.loads((out/'whole-frame.json').read_text())
        assert result['status']=='PASS' and result['expected_cases']==8269
    if args.search:
        folder=ROOT/'experiments'/args.search
        exe=out/'anneal_fine_lns'
        run(['c++','-O3','-std=c++17',ROOT/'code/anneal_fine_lns.cpp','-o',exe])
        seed=json.loads((folder/'candidate.json').read_text())['seed']
        locks=folder/('lock0.txt' if args.search.endswith('_unlock') else 'lock50.txt')
        run([exe,folder/'grammar.txt',folder/'constraints.txt',out/'search.json',args.seconds,
             seed,127,locks,folder/'resume.txt',args.iterations])
    result=dict(status='PASS_REQUESTED_CHECKS',structural_audits=reports,
        rebuilt_control=args.build_control,replayed_whole_frame=args.whole_frame,
        exact_rejected_blank_trap=trap_checked,
        scope='A structural audit does not prove a newly requested terminal orientation or the blank start of an uncompiled grammar.')
    (out/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status=result['status'],output=str(out),audits=len(reports)),indent=2))

if __name__=='__main__':main()
