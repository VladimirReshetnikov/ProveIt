#!/usr/bin/env python3
"""Replay the separate SYM/polarity evidence after a core K223 replay.

Default checks the supplied SYM proof, regenerates it from pinned sources,
checks its exact register source and fold, and checks its literal blank boot.
--full-symmetry additionally rederives all 6097 symbolic runtime cases.
Polarity formula fusion and the two logical-obstruction experiments are
separate claims; the 229-state specimen is not promoted by this driver.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, os, shutil, subprocess, sys, time

HERE=Path(__file__).resolve().parent

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--core-replay',type=Path,required=True)
    ap.add_argument('--output-dir',type=Path,required=True)
    ap.add_argument('--full-symmetry',action='store_true')
    a=ap.parse_args()
    if not __debug__ or sys.flags.optimize:raise ValueError('Keep assertions enabled')
    core=a.core_replay.resolve();out=a.output_dir.resolve()
    baseline=core/'baseline-input/K224_Construction_2026-10-20'
    parent=core/'baseline-replay/upstream/K225_Construction_2026-10-19/portable'
    if not baseline.is_dir() or not parent.is_dir():raise ValueError('Run the core K223 replay first')
    if HERE.parent==out or HERE.parent in out.parents:raise ValueError('Output must be outside the packet')
    if out.exists() and any(out.iterdir()):raise ValueError('Use a new empty output directory')
    out.mkdir(parents=True,exist_ok=True);(out/'logs').mkdir();start=time.monotonic();phases=[]
    def run(name,script,*args):
        log=out/'logs'/(name+'.log');begin=time.monotonic()
        print(name,flush=True)
        with log.open('w') as stream:
            p=subprocess.run([sys.executable,'-B',str(script),*map(str,args)],cwd=out,
                env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'},stdout=stream,stderr=subprocess.STDOUT)
        phases.append(dict(name=name,returncode=p.returncode,seconds=time.monotonic()-begin))
        if p.returncode:raise ValueError('Phase failed: '+name+'; see '+str(log))
    th=HERE/'theory';sym=HERE/'symmetry224';ver=sym/'verification';res=sym/'results'
    audits=HERE/'audits';portable=HERE.parent/'portable'
    run('A1_independent_K223_logic',audits/'audit_k223_logic.py',
        portable/'theory/merged_euclidean_helper_proofs.json','--output',out/'k223_logic_audit.json')
    run('A2_independent_K223_source',audits/'independent_k223_source_audit.py',
        '--baseline-root',baseline,'--upstream226',parent/'baseline226',
        '--sites',portable/'results/sites.json','--output',out/'k223_source_audit.json')
    run('A3_independent_K223_machine',audits/'independent_machine_audit.py',
        '--portable',portable,'--output',out/'k223_machine_audit.json')
    run('01_check_symmetry_proof',th/'check_symmetry_rel_helper.py',
        th/'evidence/symmetry_rel_helper_certificate.json','--output',out/'symmetry_proof_receipt.json')
    run('02_regenerate_symmetry_proof',th/'generate_symmetry_rel_helper.py',
        '--source116-proofs',baseline/'portable/theory/source116/proofs',
        '--output',out/'regenerated_symmetry_proof.json')
    if sha(out/'regenerated_symmetry_proof.json')!=sha(th/'evidence/symmetry_rel_helper_certificate.json'):
        raise ValueError('Regenerated symmetry proof bytes differ')
    run('03_exact_symmetry_source',ver/'check_symmetry_source.py',
        '--baseline-root',baseline,'--parent-root',parent,
        '--candidate-source',res/'sites.json','--output',out/'symmetry_source_receipt.json')
    run('04_symmetry_fold',ver/'prove_sym224_fold.py',
        '--parent',sym/'parent225/candidate.legacy.tm',
        '--candidate',res/'candidate.legacy.tm','--output',out/'symmetry_fold_receipt.json')
    spec=importlib.util.spec_from_file_location('core_literal_build',HERE.parent/'portable/build223.py')
    build=importlib.util.module_from_spec(spec);spec.loader.exec_module(build)
    table,initial,halt,states=build.parse(res/'candidate.k.tm')
    if (initial,halt,len(states))!=(0,254,224):raise ValueError('SYM table convention differs')
    boot=build.bootstrap(table)
    (out/'symmetry_bootstrap.json').write_text(json.dumps(boot,indent=2)+'\n')
    phases.append(dict(name='05_exact_symmetry_blank_boot',status='PASS'))
    run('06_polarity_rewrites',th/'check_polarity_fusion.py','--output-dir',out/'polarity')
    run('07_quantifier_obstruction',th/'check_t_replacement_obstruction.py','--output',out/'quantifier_obstruction.json')
    # This search writes beside its script, so run a copy outside the packet.
    search=out/'find_three_variable_l_matrices.py';shutil.copyfile(th/search.name,search)
    run('08_implicational_obstructions',search)
    if a.full_symmetry:
        run('09_unbounded_symmetry_runtime',ver/'check_literal_runtime.py',
            '--table',res/'candidate.legacy.tm','--sites',res/'sites.json',
            '--states','224','--output',out/'symmetry_runtime.json')
    receipt=dict(status='ADDITIONAL_RESEARCH_REPLAY_PASS',phases=phases,
        full_symmetry_runtime_rederived=a.full_symmetry,seconds=time.monotonic()-start,
        symmetry_table_sha256=sha(res/'candidate.legacy.tm'),
        symmetry_source_sha256=sha(res/'sites.json'),
        scope='Supplementary evidence. The canonical record table remains portable/results/candidate223.tm. No unbounded runtime claim for the 229-state polarity specimen.')
    (out/'replay.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
