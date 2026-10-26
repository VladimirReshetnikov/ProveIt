#!/usr/bin/env python3
"""Replay candidates in a complete ProveIt environment; never apply patches.
prototypes: compile the supplied fresh-namespaced .lean files.
integration: require the already patched eight files, build their modules,
then run the project's focused checks. Use a disposable checkout.
"""
import argparse, hashlib, json, shutil, subprocess, time
from pathlib import Path

BUNDLE=Path(__file__).resolve().parents[1]
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,required=True)
    ap.add_argument('--mode',choices=['prototypes','integration'],default='prototypes')
    ap.add_argument('--timeout',type=int,default=600)
    ap.add_argument('--output',type=Path,default=Path('lean-replay-results'))
    args=ap.parse_args()
    repo=args.repo.resolve(); out=args.output.resolve(); out.mkdir(parents=True,exist_ok=True)
    rows=[]
    report={'mode':args.mode,'repo':str(repo),'status':'not_started','commands':rows}
    def save(): (out/'result.json').write_text(json.dumps(report,indent=2)+'\n')
    def run(cmd,label):
        start=time.monotonic()
        try:
            r=subprocess.run(cmd,cwd=repo,capture_output=True,text=True,timeout=args.timeout)
            log=r.stdout+r.stderr; rc=r.returncode
        except subprocess.TimeoutExpired as e:
            log='Command exceeded the requested timeout.\n'; rc=124
        (out/(label+'.log')).write_text(log)
        rows.append({'label':label,'argv':cmd,'exit_code':rc,'seconds':round(time.monotonic()-start,3)})
        save()
        return rc==0
    if not shutil.which('lake'):
        report['status']='blocked: lake unavailable';save();return 2
    if not (repo/'lean-toolchain').is_file() or (repo/'lean-toolchain').read_text().strip()!='leanprover/lean4:v4.32.0':
        report['status']='blocked: unexpected or missing pinned toolchain';save();return 2
    manifest_path=repo/'lake-manifest.json'
    if not manifest_path.is_file():
        report['status']='blocked: missing dependency manifest';save();return 2
    packages=json.loads(manifest_path.read_text()).get('packages',[])
    mathlib=[p for p in packages if p.get('name')=='mathlib']
    if len(mathlib)!=1 or mathlib[0].get('rev')!='81a5d257c8e410db227a6665ed08f64fea08e997':
        report['status']='blocked: unexpected pinned Mathlib revision';save();return 2
    if not run(['lake','env','lean','--version'],'toolchain'):
        report['status']='failed: toolchain';save();return 1
    if args.mode=='integration':
        manifest=json.loads((BUNDLE/'evidence/composed-source-validation.json').read_text())
        mismatches=[x['path'] for x in manifest['files'] if not (repo/x['path']).is_file() or digest(repo/x['path'])!=x['candidate_sha256']]
        if mismatches:
            report.update(status='blocked: candidate sources do not match',mismatches=mismatches);save();return 2
        names=['ObjectOmegaSemiring','ObjectNaturalDiscrete','ObjectPairingSurjective',
          'ObjectPairingInjective','ObjectDivision','SelectiveCoefficientBounds',
          'SplitCoefficientBounds','NativePellPower']
        commands=[(['lake','build','DiophantineConsistency.'+n],'build-'+n) for n in names]
        for n in [*names, 'ObjectSharpPairing']:
            p=repo/'Computability/DiophantineConsistency/Lean/checks'/f'{n}.lean'
            if p.exists(): commands.append((['lake','env','lean',str(p)],'check-'+n))
    else:
        commands=[(['lake','env','lean',str(p)],p.stem) for p in sorted((BUNDLE/'lean').glob('*.lean'))]
    for cmd,label in commands:
        if not run(cmd,label):
            report['status']='failed: '+label;save();return 1
    report['status']='passed: '+args.mode;save();return 0

if __name__=='__main__': raise SystemExit(main())
