"""Recover six batch144 deliveries outside the checkout and run their checks.

Delivered sources are never patched. Manifest-only checks are excluded under
our intake procedure; source05's mathematical/checker/compiler components are
run directly because its aggregate driver always checks a checksum manifest.
"""
from __future__ import annotations
import argparse
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from zipfile import ZipFile

ARRIVALS = (
    ('17d0f2eaa650901cda59764dfcc4661c199e49c8', 'zfc_machine_research.zip'),
    ('17d0f2eaa650901cda59764dfcc4661c199e49c8', 'zfc_subset_kernel_research.zip'),
    ('17d0f2eaa650901cda59764dfcc4661c199e49c8', 'zfc_subset_only_machine_research.zip'),
    ('17d0f2eaa650901cda59764dfcc4661c199e49c8', 'zfc_tm_pure_subset_research.zip'),
    ('39409c8c921cccdbd6162c8767c84cfb7df65df1', 'zfc_one_schema_research.zip'),
    ('83dec60c249ca0f9e1b2e5ee3cf18fd1ce58c373', 'zfc_machine_research (2).zip'),
)


def main():
    if not __debug__:
        raise SystemExit('Run without -O/PYTHONOPTIMIZE: delivered regressions use assertions.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepare-only', action='store_true')
    parser.add_argument('--sources', type=int, choices=range(1,7), nargs='+', default=list(range(1,7)))
    parser.add_argument('--engineering', action='store_true', help='also run source01 extended diagnostic searches')
    parser.add_argument('--rebuild-variants', action='store_true', help='also regenerate source06 and recheck its eleven folds')
    args = parser.parse_args()
    repo = next(p for p in Path(__file__).resolve().parents if (p/'.git').exists())
    scratch = Path(tempfile.mkdtemp(prefix='zfc-batch144-reproduce-'))
    baseline = repo/'lib/jeff-busy-beaver-zfc254/ZF/m254/machine/zfc_254.tm'
    records=[]
    def run(number, root, command):
        result = subprocess.run([sys.executable, *map(str,command)],cwd=root,capture_output=True,text=True)
        log=scratch/f'{number:02d}-{len(records)+1:02d}.log';log.write_text(result.stdout+result.stderr)
        records.append(dict(source=number,command=list(map(str,command)),returncode=result.returncode,log=str(log)))
        print(f'{number:02d}: {command[0]} exit {result.returncode}',flush=True)
        if result.returncode:
            print(result.stdout+result.stderr,file=sys.stderr);raise SystemExit(result.returncode)
    for number in args.sources:
        arrival,archive=ARRIVALS[number-1];dest=scratch/f'{number:02d}'
        raw=subprocess.check_output(['git','show',f'{arrival}:docs/incoming/{archive}'],cwd=repo)
        with ZipFile(io.BytesIO(raw)) as z:
            for name in z.namelist():
                p=Path(name)
                if p.is_absolute() or '..' in p.parts:raise ValueError(name)
            z.extractall(dest)
        roots=[p for p in dest.iterdir() if p.is_dir()];assert len(roots)==1
        root=roots[0];print(f'{number:02d}: {root}',flush=True)
        if args.prepare_only:continue
        if number==1:
            for command in [('code/verify_benchmarks.py','--out','results/benchmark_verification.json'),
                            ('code/kernel_reduction.py','--out','results/kernel_reduction.json'),
                            ('engineering/blank_start_certificate.py','--sources','machines','--output','engineering/blank_start_certificate.json')]:run(number,root,command)
            if args.engineering:
                sources=root/'engineering/sources';sources.mkdir()
                source_root=repo/'lib/jeff-busy-beaver-zfc254/ZF/m254'
                for name,rel in [('Prog254.v','coq/tm/Prog254.v'),('symexec.py','tools/tm/symexec.py')]:
                    (sources/name).write_bytes((source_root/rel).read_bytes())
                for name in ('zfc_254.tm','zfc_253.tm'):(sources/name).write_bytes((root/'machines'/name).read_bytes())
                for command in [('engineering/analyze_table.py',sources/'zfc_254.tm',sources/'zfc_253.tm','--output','engineering/structural_results.json'),
                                ('engineering/grammar_audit.py',sources/'Prog254.v','--output','engineering/grammar_results.json'),
                                ('engineering/context_search.py','--sources',sources,'--search','--all-noncore','--output','engineering/redirection_results.json'),
                                ('engineering/runtime252_audit.py','--sources',sources,'--output','engineering/runtime252_results.json'),
                                ('engineering/bootstrap_search.py','--sources',sources,'--fuel','2000000','--output','engineering/bootstrap_results.json')]:run(number,root,command)
        elif number==2:
            run(number,root,('reproduce.py','--table',baseline))
            run(number,root,('code/check_certificate.py','--file','examples/identity.json'))
            run(number,root,('code/check_certificate.py','--start','0','--count','10000'))
        elif number==3:
            run(number,root,('build.py','--tests','--skip-pdf','--table',baseline))
        elif number==4:
            run(number,root,('build.py','--tests','--skip-pdf'))
            for example in ('identity.json','schema_example.json'):run(number,root,('code/checker.py','data/'+example))
        elif number==5:
            generated=scratch/'generated269'
            run(number,root,('machine/rebracket_axioms.py','--inputs','machine/inputs','--output',generated))
            expected=root/'machine/results'
            for p in expected.iterdir():
                if p.is_file() and p.read_bytes()!=(generated/p.name).read_bytes():raise ValueError('Regenerated artifact differs: '+p.name)
            run(number,root,('machine/verify_rm_certificate.py','--source','machine/inputs/source_dag.json','--candidate',generated/'rebracketed_dag.json','--certificate',generated/'rm_bisimulation.json'))
            kernel=scratch/'pinned-kernel-metrics.py'
            kernel.write_bytes(subprocess.check_output(['git','show','6594795e9db81637c30959e42b3bcfc9eb77722f:Computability/BusyBeaver/Research/ZFC/kernel_metrics.py'],cwd=repo))
            run(number,root/'proof_checker',('validate.py','--upstream-kernel',kernel))
            finite=scratch/'finite-saturation.json'
            run(number,root,('code/finite_saturation.py','--output',finite))
            assert finite.read_bytes()==(root/'data/finite_saturation_results.json').read_bytes()
        else:
            run(number,root,('verify.py','--no-integrity'))
            if args.rebuild_variants:run(number,root,('machine/build_variants.py',))
    (scratch/'reproduction.json').write_text(json.dumps(records,indent=2)+'\n')
    print(f'Evidence retained in {scratch}')

if __name__=='__main__':main()
