"""Paired compiler/solver measurements; no unknown answer is scored a decision."""
import argparse
import json
from pathlib import Path
from statistics import median
import sys
from time import perf_counter

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from fastunknot.diagram import Diagram
from fastunknot.compressed_words import WordArena
from fastunknot.su2 import compile_bridge,compile_diagram_presentation,compile_slp,solve_formula


def timed(operation):
    start=perf_counter(); result=operation()
    return perf_counter()-start,result


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=ROOT/'results/su2_benchmark.json')
    parser.add_argument('--repeats',type=int,default=3)
    parser.add_argument('--seconds',type=float,default=0.25)
    args=parser.parse_args()
    cases=[('unknot',Diagram.from_braid(1,[])),
           ('trefoil',Diagram.from_braid(2,[1]*3)),
           ('figure_eight',Diagram.from_braid(3,[1,-2]*2)),
           ('torus_2_5',Diagram.from_braid(2,[1]*5)),
           ('torus_2_9',Diagram.from_braid(2,[1]*9)),
           ('coxeter_9',Diagram.from_braid(10,list(range(1,10)))),
           ('cancelled_unknot',Diagram.from_braid(3,[1,2,-2,1,-1,2]))]
    # Identical A/A controls estimate timing variation, not algorithm speedup.
    records=[]
    for name,d in cases:
        for mode in ('wirtinger','bridge','tietze'):
            compile_times=[];solve_times=[];statuses=[];controls=[]
            for repeat in range(args.repeats):
                operation=(lambda:compile_bridge(d)) if mode=='bridge' else (
                    lambda:compile_diagram_presentation(d,simplify=mode=='tietze')[0])
                elapsed,f=timed(operation); compile_times.append(elapsed)
                control,_=timed(operation);controls.append(control)
                answer=solve_formula(f,seconds=args.seconds,trace_zero_probe=True)
                solve_times.append(answer.get('seconds',args.seconds))
                statuses.append(answer['status'])
            records.append(dict(case=name,mode=mode,crossings=d.crossings,
                summary=f.summary(),compile_seconds=compile_times,identical_control_seconds=controls,
                solver_seconds=solve_times,statuses=statuses,
                median_compile_seconds=median(compile_times),
                median_solver_seconds=median(solve_times)))
    powers=[]
    for bits in (8,32,128,512,2048):
        arena=WordArena(max_nodes=10000,max_work=100000)
        root=arena.power(arena.letter(1),1<<bits)
        times=[]
        for _ in range(args.repeats):
            elapsed,f=timed(lambda:compile_slp([1,2],arena,[root]))
            times.append(elapsed)
        powers.append(dict(exponent_power_of_two=bits,expanded_letters_description=f'2^{bits}',
                           summary=f.summary(),compile_seconds=times,
                           median_compile_seconds=median(times)))
    output=dict(repeats=args.repeats,solver_allowance=args.seconds,
                scope='Formula construction and exact query timings, not whole-pipeline speedups',
                cases=records,binary_powers=powers)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(output,indent=2)+'\n')
    for r in records:
        print(r['case'],r['mode'],r['summary']['real_variables'],
              r['summary']['max_equation_degree'],round(1000*r['median_compile_seconds'],3),
              round(1000*r['median_solver_seconds'],3),r['statuses'])
    print('binary power compiler:',[(r['exponent_power_of_two'],r['summary']['polynomial_terms'],
                                   r['median_compile_seconds']) for r in powers])


if __name__=='__main__':
    main()
