#!/usr/bin/env python3
"""Offline replay of corrected context generation and bounded startup searches.

Default: corrected radius4 contexts, neutral candidates, historical any-frame
startup screen. --full additionally checks radius6, speculative box candidates,
the register abstraction, and both194-state companion compositions.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,sys,tempfile,time

HERE=Path(__file__).resolve().parent

def root_default():
    return next((p for p in HERE.parents if (p/'runtime193/runtime193.native.tm').is_file()
                 and (p/'reference/haz/vendor/symbolic_runtime.py').is_file()),None)

def summary(text):
    line=next(l for l in reversed(text.splitlines()) if l.startswith('DONE '))
    p=line.split();return {p[i]:int(p[i+1]) for i in range(1,len(p)-2,2)}

def run(args,**kw):
    p=subprocess.run(list(map(str,args)),capture_output=True,text=True,**kw)
    if p.returncode:raise RuntimeError(f'{args[0]} failed: {p.stdout}\n{p.stderr}')
    return p

def replay(ref,out,full):
    started=time.monotonic();out.mkdir(parents=True,exist_ok=True)
    env=dict(os.environ);env['PA_RESEARCH_REFERENCE_ROOT']=str(ref)
    table=ref/'runtime193/runtime193.native.tm';sites=ref/'runtime193/primary.sites.json';ins=ref/'runtime193/primary.instructions.json'
    receipt={'status':'PASS','scope':'Bounded research replay; no sub194 consistency machine claimed',
             'runtime193_sha256':hashlib.sha256(table.read_bytes()).hexdigest(),'checks':{}}
    for name in ['neutral_rows','search_startup']:
        run(['g++','-O3','-std=c++17',HERE/(name+'.cpp'),'-o',out/name])
    for radius,bound in [(4,100)]+([(6,180)] if full else []):
        patterns=out/f'corrected_patterns_k{radius}.txt'
        p=run([sys.executable,HERE/'collect_source_contexts.py',table,sites,ins,patterns,radius],env=env)
        data=json.loads(p.stdout);(out/f'contexts_k{radius}.json').write_text(p.stdout)
        recorded=HERE/'recorded'/f'runtime193_corrected_patterns_k{radius}.txt'
        assert patterns.read_bytes()==recorded.read_bytes(),'Context replay differs'
        p=run([out/'neutral_rows',table,radius,bound,patterns])
        (out/f'neutral_k{radius}.jsonl').write_text(p.stdout)
        expected=(HERE/'recorded'/f'runtime193_corrected_neutral_k{radius}.jsonl').read_text()
        assert p.stdout==expected,'Neutral candidate replay differs'
        data['neutral_candidate_count']=len(p.stdout.splitlines())
        receipt['checks'][f'corrected_radius{radius}']=data
    p=run([out/'search_startup',table,HERE/'inputs/runtime193_neutral_source.tsv',200000,0,100000,
           HERE/'inputs/startup_any_frame_templates.tsv'])
    (out/'any_frame_hits.jsonl').write_text(p.stdout);(out/'any_frame.log').write_text(p.stderr)
    actual=summary(p.stderr);expected=summary((HERE/'recorded/runtime193_any_frame.log').read_text())
    assert actual==expected and not p.stdout,(actual,expected)
    receipt['checks']['historical_any_frame_startup']=actual
    receipt['checks']['historical_any_frame_startup']['note']='Includes9 rejected boundary-only q35 candidates; any frame at pc25..44, arbitrary register values'
    if full:
        p=run([out/'search_startup',table,HERE/'inputs/runtime193_box_neutral_source.tsv',200000,0,100000,
               HERE/'inputs/startup_seed_templates.tsv'])
        (out/'box_hits.jsonl').write_text(p.stdout);(out/'box_startup.log').write_text(p.stderr)
        actual=summary(p.stderr);expected=summary((HERE/'recorded/runtime193_box_startup.log').read_text())
        assert actual==expected and not p.stdout
        receipt['checks']['speculative_box_startup']=actual
        receipt['checks']['speculative_box_startup']['note']='Screen only; no arithmetic-box equivalence asserted'
        p=run([sys.executable,HERE/'zero_interference.py',HERE/'inputs/HAZ.instructions.json',out/'zero_interference.json'])
        actual=json.loads((out/'zero_interference.json').read_text());expected=json.loads((HERE/'recorded/zero_interference.json').read_text())
        for key in ['sha256','reachable_abstract_states','reachable_sites','sites','pair_interference','known_zero_at_site','known_positive_at_site']:
            assert actual[key]==expected[key],key
        receipt['checks']['register_abstraction']={k:actual[k] for k in ['reachable_abstract_states','reachable_sites','sites']}
        p=run([sys.executable,HERE/'verify_companions.py','--reference-root',ref])
        receipt['checks']['194_companions']=json.loads(p.stdout)
    receipt['elapsed_seconds']=round(time.monotonic()-started,3)
    (out/'reproduction_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    return receipt

if __name__=='__main__':
    if not __debug__:raise SystemExit('Run with assertions enabled, without Python -O.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--reference-root',type=Path,default=root_default())
    ap.add_argument('--output',type=Path)
    ap.add_argument('--full',action='store_true');a=ap.parse_args()
    if a.reference_root is None:raise SystemExit('Use --reference-root to name the enclosing delivered package.')
    if a.output is None:
        with tempfile.TemporaryDirectory(prefix='pa_reduction_replay_') as td:
            result=replay(a.reference_root.resolve(),Path(td),a.full)
    else:result=replay(a.reference_root.resolve(),a.output.resolve(),a.full)
    print(json.dumps(result,indent=2))
