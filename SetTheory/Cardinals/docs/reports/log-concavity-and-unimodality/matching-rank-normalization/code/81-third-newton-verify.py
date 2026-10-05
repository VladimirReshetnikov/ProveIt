#!/usr/bin/env python3
"""Portable exact verification driver. Run on an extracted working copy."""
from pathlib import Path
import argparse, json, subprocess, sys, time
ROOT=Path(__file__).resolve().parent
C=ROOT/'code'
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--mode',choices=('receipts','certificates','full'),default='certificates',help='receipts checks stored complete-replay records; certificates also recomputes all reduced certificates and matrix identities; full additionally reconstructs both large coefficient arrays')
args=parser.parse_args()
records=[]
def run(path,*extra):
    path=C/path
    start=time.monotonic()
    print('RUN',path.relative_to(ROOT),*extra,flush=True)
    subprocess.run([sys.executable,'-O',str(path),*map(str,extra)],cwd=path.parent,check=True)
    recorded_args=[str(Path(str(x)).relative_to(ROOT)) if str(x).startswith(str(ROOT)+'/') else str(x) for x in extra]
    records.append({'script':str(path.relative_to(ROOT)),'arguments':recorded_args,'seconds':round(time.monotonic()-start,3)})
br=Path('rank6_quartic_BR/independent_reconstruction')
bb=Path('rank6_quartic_truncation/root_reconstruction')
ba=Path('rank6_quartic_BB_audit')
p370=ba/'profile_370_independent'
if args.mode!='receipts':
    run('check_regular_matrix.py')
    run('check_fifth_truncation_barrier.py')
    run(br/'check_categories.py')
    run(br/'check_R_blocks.py')
    run(br/'reconstruct.py','endpoints')
    run(bb/'check_endpoints.py')
    run(bb/'check_kernels.py')
    run(ba/'check_factors.py')
    run(ba/'check_110.py')
    run(ba/'check_330.py')
    run('rank6_quartic_truncation/check_770_endpoints.py')
    run(ba/'verify_rayleigh_sos.py')
    repairs=sorted((C/'rank6_quartic_truncation').glob('Rayleigh_cone_*.json'))
    if len(repairs)!=60:raise RuntimeError(('Expected all 60 Rayleigh certificates',len(repairs)))
    run(ba/'verify_Rayleigh_repairs.py',*repairs)
    run('rank6_BB_nested/run_checks.py')
    run(p370/'check_scalar.py')
    for mode in ('zero0','h0','zero','g','h'):run(p370/'check_regions.py',mode)
if args.mode=='full':
    helper=C/bb/'independent_product'
    subprocess.run(['g++','-O3','-std=c++17',str(helper.with_suffix('.cpp')),'-lgmpxx','-lgmp','-o',str(helper)],check=True)
    run(br/'reconstruct.py')
    run(bb/'reconstruct.py')
# These finalizers compare complete stored/recomputed records and immutable inputs.
# They do not replace coefficient reconstruction when run in receipts mode.
run(br/'finalize.py')
run(bb/'finalize.py')
run(p370/'finalize.py')
result={'passed':True,'mode':args.mode,'large_arrays_freshly_reconstructed':args.mode=='full','steps':records}
(ROOT/f'verification_{args.mode}.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS:',args.mode,'mode.',flush=True)
if args.mode!='full':print('The two large arrays were validated through their complete saved records; use --mode full to regenerate every coefficient.',flush=True)
