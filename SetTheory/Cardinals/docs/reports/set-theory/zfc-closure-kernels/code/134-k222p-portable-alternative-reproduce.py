"""Offline conditional/G222 reconstruction, source proof, and optional full runtime.

The native conditional-K/ZFC calibration is explicitly inherited. This replay
establishes the local source/table/emitter/runtime parts; it is not a new
proof-assistant endpoint.
"""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,sys,time
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'helpers'))
import machine_tools as m

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output-dir',type=Path,required=True)
    ap.add_argument('--full',action='store_true')
    ap.add_argument('--baseline-archive',type=Path,default=HERE.parent/'vendor/K224_Construction_2026-10-20.zip')
    ap.add_argument('--runtime-dir',type=Path,default=HERE.parent/'runtime')
    args=ap.parse_args()
    assert __debug__ and not sys.flags.optimize
    out=args.output_dir.resolve();assert out!=HERE and HERE not in out.parents
    assert not out.exists() or not any(out.iterdir())
    out.mkdir(parents=True,exist_ok=True);(out/'logs').mkdir()
    start=time.monotonic();receipt={'status':'IN_PROGRESS','phases':[]}
    def write():
        receipt['seconds']=time.monotonic()-start
        (out/'replay.json').write_text(json.dumps(receipt,indent=2)+'\n')
    def run(name,script,*argv,env=None):
        log=out/'logs'/(name+'.log')
        with log.open('w') as f:
            p=subprocess.run([sys.executable,'-B',str(script),*map(str,argv)],stdout=f,stderr=subprocess.STDOUT,
                             env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1',**(env or {})})
        receipt['phases'].append({'name':name,'returncode':p.returncode,'log':str(log.relative_to(out))})
        write();assert p.returncode==0,f'Phase {name} failed; see {log}'
    def same(f):
        assert (out/f).read_bytes()==(HERE/'results'/f).read_bytes(),f'Bytes differ: {f}'
    try:
        pins=json.loads((HERE/'manifest.json').read_text())
        for name,h in pins.items():assert m.sha(HERE/name)==h,('Manifest mismatch',name)
        run('01_construct',HERE/'construct.py','--inputs',HERE/'inputs','--output',out)
        run('02_fold',HERE/'fold.py','--results',out)
        run('03_emitter',HERE/'check_emitter.py','--inputs',HERE/'inputs','--results',out,'--baseline-archive',args.baseline_archive)
        table,startstate,halt,states=m.parse(out/'candidate222.k.tm')
        assert (startstate,halt,len(states),len(table))==(0,254,222,444)
        canonical,cmap=m.canonical(table,0,254)
        assert set(cmap.values())==set(range(223))
        (out/'candidate222.tm').write_bytes(m.encode(canonical))
        (out/'canonical_map.json').write_text(json.dumps(cmap,indent=2)+'\n')
        raw=json.loads((HERE/'inputs/legacy_state_map.json').read_text())
        legacy={int(k):v for k,v in raw['k230_to_old'].items()};legacy[254]=254
        for k in cmap:
            if k not in legacy:legacy[k]=k+1000
        legacy={k:legacy[k] for k in cmap}
        assert len(set(legacy.values()))==len(legacy)
        lt={(legacy[k],b):(w,d,legacy[z]) for (k,b),(w,d,z) in table.items()}
        (out/'candidate222.legacy.tm').write_bytes(m.encode(lt,legacy[0]))
        (out/'legacy_map.json').write_text(json.dumps(legacy,indent=2)+'\n')
        boot=m.bootstrap(table);boot['canonical_state']=cmap[84]
        (out/'bootstrap222.json').write_text(json.dumps(boot,indent=2)+'\n')
        for f in ('sites.json','candidate222.k.tm','candidate222.tm','candidate222.legacy.tm','bootstrap222.json','emitter222.json'):
            same(f)
        stored=json.loads((HERE/'results/runtime222.json').read_text())
        cases=json.loads((HERE/'results/runtime222_cases.json').read_text())
        sites=json.loads((out/'sites.json').read_text())
        expected=[(i,pos) for i,s in enumerate(sites) for pos in ((False,True) if s[1]=='CD' else (False,))]
        assert [(c['site_index'],c['positive']) for c in cases]==expected
        assert stored['status']=='UNIVERSAL_MATHEMATICAL_PASS' and len(cases)==5956
        assert stored['table_sha256']==m.sha(out/'candidate222.legacy.tm')
        assert stored['sites_sha256']==m.sha(out/'sites.json')
        assert set(map(tuple,stored['directly_used_rows']))==set(lt)
        assert all(len(c['duration'])==13 and c['duration'][0]>0 and all(type(v)is int and v>=0 for v in c['duration']) for c in cases)
        assert sum(c['symbolic_steps'] for c in cases)==stored['symbolic_steps']==1443614
        if args.full:
            runtime=args.runtime_dir.resolve()
            assert m.sha(runtime/'symbolic_runtime.py')==stored['engine_sha256']
            assert m.sha(runtime/'independent_runtime.py')==stored['helper_sha256']
            run('04_unbounded_runtime',HERE/'helpers/check_literal_runtime.py',
                '--table',out/'candidate222.legacy.tm','--sites',out/'sites.json','--states','222',
                '--output',out/'runtime222.json',env={'PYTHONPATH':str(runtime)})
            same('runtime222_cases.json')
        receipt.update(status='FULL_CONDITIONAL222_REPLAY_PASS' if args.full else 'QUICK_CONDITIONAL222_REPLAY_PASS',
                       states=222,rows=444,guarded_cases=5956,all_runtime_rows=444,
                       canonical_sha256=m.sha(out/'candidate222.tm'),source_sha256=m.sha(out/'sites.json'),
                       source_proof='Exact conditional-core/G emission and complete guarded CFG; nine arbitrary-register macro contracts.',
                       inherited_premise='Published conditional-K223 native theory calibration, plus generic G equality/helper interderivation.',
                       proof_boundary='Executable ordinary mathematical certificates; no new Rocq or Lean endpoint.')
        write();print(json.dumps(receipt,indent=2))
    except Exception as e:
        receipt.update(status='FAILED',error=repr(e));write();raise

if __name__=='__main__':main()
