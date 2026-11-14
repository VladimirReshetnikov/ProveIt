"""Replay the invariant certificate and six completed local screens."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,tempfile
import modular_invariant as modular
import register_alias
HERE=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--derive-contexts',action='store_true')
    args=ap.parse_args();ins=json.loads((HERE/'inputs/instructions.json').read_text())
    frozen=json.loads((HERE/'mod4_verified.json').read_text())
    modular.verify(ins,frozen)
    assert frozen==[list(v) for v in modular.derive(ins)]
    aliases=register_alias.analyze(HERE/'inputs/instructions.json')
    assert all(p['violations']>0 for p in aliases['pairs'])
    table=HERE/'inputs/machine.native.tm'
    with tempfile.TemporaryDirectory(prefix='pa194-invariant-screen-')as tmp:
        work=Path(tmp);runs=[]
        for name in('action_merge_all','edge_bypass','marker_folds_all'):
            subprocess.run(['c++','-O3','-std=c++17',str(HERE/(name+'.cpp')),'-o',str(work/name)],check=True)
        for family,expected in(('zero_contexts',29479),('modular_contexts',24388)):
            patterns=HERE/family/'patterns_k5.txt'
            if args.derive_contexts:
                script='collect_zero_contexts.py'if family=='zero_contexts'else'collect_modular_contexts.py'
                subprocess.run([sys.executable,'-B',str(HERE/script),str(work/family)],check=True)
                assert patterns.read_bytes()==(work/family/'patterns_k5.txt').read_bytes()
            assert len(patterns.read_text().splitlines())==expected
            for name in('action_merge_all','edge_bypass','marker_folds_all'):
                cmd=[str(work/name),str(table)]
                if name!='marker_folds_all':cmd+=['5','300']
                result=subprocess.run(cmd+[str(patterns)],text=True,capture_output=True,check=True)
                assert not result.stdout.strip(),result.stdout
                runs.append(dict(contexts=family,screen=name,candidates=0))
        print(json.dumps(dict(invariant_checked=True,context_derivations_replayed=args.derive_contexts,runs=runs),indent=2))

if __name__=='__main__':
    if not __debug__:raise SystemExit('Assertions must be enabled.')
    main()
