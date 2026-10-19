#!/usr/bin/env python3
"""Reproduce positive certificates and explicitly rejected scanner controls.

No package inputs or frozen results are overwritten. Fresh logs/certificates
are written under --output (default verification/check-<UTC timestamp>).
Optional finite C++ searches use their declared bounds; they are not proofs
of the nonexistence of other sub-246 machines.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,os,shutil,subprocess,sys,time
ROOT=Path(__file__).resolve().parents[1]
CONTROLS=('commuted_seed246','reassociated246','commuted_reassociated246','normalized246')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path)
    ap.add_argument('--full-search',action='store_true',help='Also replay the bounded C++ state campaigns.')
    ap.add_argument('--check-hashes',action='store_true',help='Check the complete frozen SHA256SUMS before reproduction.')
    args=ap.parse_args()
    if not __debug__:ap.error('Run without -O: assertions are proof obligations.')
    stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    out=(args.output or ROOT/'verification'/('check-'+stamp)).resolve()
    out.mkdir(parents=True,exist_ok=True)
    env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1'
    env['ZFC_STATE_OUTPUT']=str(out/'state');(out/'state').mkdir(exist_ok=True)
    env['ZFC_LOGIC_OUTPUT']=str(out/'logic');(out/'logic').mkdir(exist_ok=True)
    records=[]
    def run(label,arguments,expected=0):
        began=time.monotonic()
        command=[sys.executable,*[str(a) for a in arguments]]
        result=subprocess.run(command,cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (out/(label+'.log')).write_text(result.stdout)
        if result.returncode!=expected:
            print(result.stdout);raise RuntimeError(f'{label}: exit {result.returncode}, expected {expected}')
        row=dict(check=label,status='PASS',expected_exit=expected,elapsed_seconds=time.monotonic()-began)
        records.append(row);print('PASS',label,flush=True)
    def require(path,status='PASS'):
        d=json.loads(path.read_text());assert d['status']==status,(path,d.get('status'));return d
    if args.check_hashes:
        for line in (ROOT/'SHA256SUMS').read_text().splitlines():
            digest,name=line.split('  ',1);p=ROOT/name
            assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==digest,name
        print('PASS complete frozen hashes',flush=True)
    # Exact source commutation followed by exact source/CFG transformations.
    run('source_commutation',['code/audit/check_commutation.py','machines/commuted_seed246.graph.json','--output',out/'source_commutation.json'])
    run('source_reassociation',['code/audit/check_candidate_graph.py','machines/reassociated246.graph.json','--output',out/'source_reassociation.json'])
    for name in ('commuted_reassociated246','normalized246'):
        run(name+'_source',['code/audit/check_reassociated_graph.py','machines/commuted_seed246.graph.json',f'machines/{name}.graph.json','--output',out/(name+'_source.json')])
    # Universal box/word derivations and complete literal bootstraps.
    for name in CONTROLS:
        run(name+'_runtime',['code/check_runtime.py','--table',f'machines/{name}_old.tm','--graph',f'machines/{name}.graph.json','--output',out/(name+'_runtime.json')])
        d=require(out/(name+'_runtime.json'));assert d['working_states']==246 and d['universally_verified_cases']==8391
        argv=['code/audit/check_candidate_boot.py',f'machines/{name}_old.tm','--output',out/(name+'_boot.json')]
        if name!='reassociated246':argv.append('--allow-changed-prefix-rows')
        run(name+'_boot',argv)
        run(name+'_canonical',['code/canonicalize.py',f'machines/{name}_old.tm','--output',out/(name+'.tm'),'--certificate',out/(name+'_renumbering.json')])
        assert (out/(name+'.tm')).read_bytes()==(ROOT/'machines'/(name+'.tm')).read_bytes()
    # Independent exact graph and invariant certificates.
    for label,script in [('quotient','check_root_quotient'),('fixtures','check_quotient_fixtures'),('affine','check_affine_certificates'),('incidence','check_increment_incidence')]:
        run(label,['code/audit/'+script+'.py','--output',out/(label+'.json')]);require(out/(label+'.json'))
    run('regenerate_quotient',['code/build_quotient.py','--output',out/'regenerated_quotient.json'])
    run('regenerated_quotient_audit',['code/audit/check_root_quotient.py','--certificate',out/'regenerated_quotient.json','--output',out/'regenerated_quotient_audit.json'])
    run('selector_symmetry',['code/state/check_selector_commutation.py'])
    # The deliberately shortened tables are negative controls, kept outside machines/.
    for name,expected_failures in [('reassociated246',25),('commuted_reassociated246',21),('normalized246',16)]:
        rows=[]
        for line in (ROOT/'machines'/(name+'_old.tm')).read_text().splitlines():
            if not line.strip() or line.startswith('#'):continue
            q,b,w,d,t=line.split()
            if int(q)==74:continue
            if (int(q),int(b))==(58,0):w,d,t='0','L','84'
            assert int(t)!=74
            rows.append(f'{q} {b} {w} {d} {t}')
        table=out/(name+'_rejected245.tm')
        table.write_text('# REJECTED 245-state scanner experiment; not a certified blank-input machine.\n'+'\n'.join(rows)+'\n')
        target=out/(name+'_rejected245.json')
        run(name+'_negative_scanner',['code/check_runtime.py','--table',table,'--graph',f'machines/{name}.graph.json','--scanner','8','--output',target],expected=1)
        d=require(target,'FAIL');assert d['working_states']==245 and len(d['failures'])==expected_failures
    run('principal_emission',['code/logic/replay_selected.py','--output',out/'emission.json'])
    run('retargeted_control_source',['code/audit/check_reassociated_graph.py','machines/commuted_seed246.graph.json','experiments/logic/controls/s10_best_004.json','--operational-controls','--output',out/'retargeted_control_source.json'])
    run('retargeted_control_runtime',['code/check_runtime.py','--table','experiments/logic/controls/s10_best_004.tm','--graph','experiments/logic/controls/s10_best_004.json','--output',out/'retargeted_control_runtime.json'])
    if args.full_search:
        run('finite_state_campaigns',['code/state/replay.py','--output',out/'state_full'])
    result=dict(status='PASS',checks=len(records),records=records,output_directory=str(out),
        certified_minimum_working_states=246,strict_sub246_goal_achieved=False,
        all_four_controls_have_universal_runtime_and_exact_bootstrap=True,
        expected_scanner_rejections={'reassociated246':25,'commuted_reassociated246':21,'normalized246':16},
        scope='Ordinary mathematical certificates and finite computations; no new proof-assistant endpoint.')
    (out/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(f'PASS {len(records)} checks. Certified controls: 246 states. No sub-246 result.\n{out}',flush=True)

if __name__=='__main__':main()
