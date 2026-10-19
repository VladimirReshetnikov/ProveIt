#!/usr/bin/env python3
"""Diagnostic source controls; none is claimed to be a ZFC consistency machine.

Run in this research directory with --repo /path/to/ProveIt.
The four pinned compiler inputs are included under reference/. The unchanged
repo helper modules perform DAG reconstruction and AX RPN lowering.
"""
from __future__ import annotations
import argparse, ast, hashlib, importlib, json, sys
from pathlib import Path

HERE=Path(__file__).resolve().parent

def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,required=True)
    p.add_argument('--out',type=Path,default=HERE/'controls')
    args=p.parse_args();out=args.out.resolve();out.mkdir(exist_ok=True,parents=True)
    core=args.repo.resolve()/'Computability/BusyBeaver/Research/ZFC'
    sys.path[:0]=[str(core),str(HERE/'reference')]
    import recover_wade_dag as rec
    import theory_backend_experiment as emit
    import TMBuilder as backend
    for name,path in [('TMBuilder.py','ZF/generator/TMBuilder.py'),('tm.py','ZF/generator/tm.py'),('tmdb.py','ZF/generator/tmdb.py'),('LICENSE.wade','ZF/generator/LICENSE.wade'),('Dag254.v','ZF/m254/coq/prog/Dag254.v')]:
        assert digest(HERE/'reference'/name)==rec.SOURCE_SHA256[path]
    spec_path=HERE/'reference/spec.py'
    assert digest(spec_path)=='7d96deff6994315b714579c74d10efeb65374694d476c802c727356e258578e9'
    tree=ast.parse(spec_path.read_text())
    funcs=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name not in ('_code','enum_step')]
    spec={'F':1,'_code':lambda tag,a,b:(('imp','rel','all','eq')[tag],a,b)}
    exec(compile(ast.Module(body=funcs,type_ignores=[]),str(spec_path),'exec'),spec)
    emit.published_spec=lambda:(spec,digest(spec_path))
    nodes,names=rec.parse_dag((HERE/'reference/Dag254.v').read_text())
    old,logical,contract=emit.old_contract(nodes)
    rows=spec['ax_rows']('a','h','b','c','u');bundle=spec['bundle']('a','b','c')
    choices={'original':'u','u_a':'a','u_b':'b','u_c':'c','u_Truth':0,'u_F':1,
             'u_a_imp_b':emit.Imp('a','b'),'u_b_imp_a':emit.Imp('b','a'),
             'u_neg_b':emit.Not('b')}
    results=[]
    for name,u in choices.items():
        newrows=rows.copy();newrows[1]=spec['rho8_L']('a','b','c',u)
        program=[166,121,180,176]+[m for row in newrows[1:] for m in emit.emit(row)]+emit.emit(bundle)+emit.TAIL
        actual,events=emit.symbolic(program)
        assert actual==['old_top']+newrows+[bundle]
        if name=='original': assert program==old
        for shared in (False,True):
            b=rec.builder_from_dag(backend,nodes,names)
            b.sequence_lookup={s.seq:i for i,s in enumerate(b.sequences)}
            emit.lower_program(b,nodes,program,name,shared=shared)
            b.generate();b.tm.gc()
            states={q for q,_ in b.tm.states}
            filename=name+('_shared' if shared else '')+'.tm'
            target=out/filename;b.tm.save(str(target))
            result={'variant':name,'common_subsequence_pass':shared,'AX_macros':len(program),
              'rho8_macros':len(emit.emit(newrows[1])), 'source_RPN':program,
              'working_states':len(states),'framework_states':sum(q[0].isdigit() for q in states),
              'decision_states':sum(not q[0].isdigit() for q in states),'transition_rows':len(b.tm.states),
              'missing_rows':[[q,bit] for q in sorted(states) for bit in ('0','1') if (q,bit) not in b.tm.states],
              'table_file':filename,'table_sha256':digest(target),
              'read_u_occurrences':program.count(158),'symbolic_AX_roundtrip':True}
            results.append(result)
    report={'status':'Diagnostic complete-source controls; no new consistency-machine claim.',
      'upstream_commit':rec.COMMIT,'ProveIt_baseline_commit':'13ec39ed43148b1807f51ed6e6528e1c84659562',
      'reference_sha256':{x.name:digest(x) for x in sorted((HERE/'reference').iterdir()) if x.is_file()},
      'repo_helper_sha256':{n:digest(core/n) for n in ('recover_wade_dag.py','theory_backend_experiment.py','pairing_backend_experiment.py')},
      'old_contract':contract,'variants':results,
      'compiler_note':'Public Wade backend, not the optimized current 240-state interpreter. A state delta here is not transferable to 240 without a rebuilt table.',
      'calculus_note':'The theorem proves logical-basis nonderivability. CP and GIC might supply additional strength; neither candidate is calibrated.'}
    (out/'specialization_costs.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps([{k:r[k] for k in ('variant','common_subsequence_pass','AX_macros','rho8_macros','working_states','decision_states','framework_states','read_u_occurrences')} for r in results],indent=2))
if __name__=='__main__':main()
