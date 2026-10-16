"""Reproduce REJECTED reduced-logic EPSC/PSC compiler experiments.

The report proves the intended abstract proof search never reaches its target.
The state count is not a ZFC-consistency bound.
"""
from pathlib import Path
import sys, json, itertools, importlib, hashlib, argparse

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT / 'ProveIt'

def load_sources(repo):
    global t, builder_from_dag, REGISTERS, parse_dag, git_bytes
    sys.path.insert(0, str(repo/'Computability/BusyBeaver/Research/ZFC'))
    import theory_backend_experiment as t
    from recover_wade_dag import builder_from_dag, REGISTERS, parse_dag, git_bytes

def psc(kernel='subset', support_first=False):
    I,A,E,N,O,R = t.Imp,t.All,t.Ex,t.And,t.Or,t.Rel
    c='c'; phi=c
    sb=A(0,E(c,A(1,I(phi,A(0,I(R(0,1),R(0,c)))))))
    seed=A(c,I(R(c,0),R(c,1))) if kernel=='subset' else A(c,t.Not(R(c,0)))
    closed=A(0,I(O(seed,R(0,c)),A(1,I(phi,R(1,c)))))
    support=A(1,I(R(1,c),E(0,phi)))
    conjunction=N(support,closed) if support_first else N(closed,support)
    body=E(c,conjunction)
    return I(sb,A(1,body) if kernel=='subset' else body)

def program(builder, order, dual, grouped=False, kernel='subset', support_first=False, vacuity_first=False):
    spec,_=t.published_spec()
    rows=spec['ax_rows']('a','h','b','c','u')
    if dual: rows[3]=t.Imp('b',t.All('a',t.Ex('a','b')))
    logical=[166,121,180,176]
    for i in order: logical+=t.emit(rows[i])
    theory=psc(kernel,support_first)
    vacuity=t.Imp(t.Rel('a','b'),t.All('c',t.Rel('a','b')))
    if grouped:
        bundle=t.And(vacuity,theory) if vacuity_first else t.And(theory,vacuity)
        return logical+t.emit(bundle)+t.TAIL
    r=[builder.reg(n) for n in REGISTERS]
    copy_restore=[192,builder.while_decnz(r[7],r[3].inc)]
    clear=builder.while_decnz(r[1],())
    gate=[copy_restore,builder.if_not_decnz(r[6],clear),
          builder.if_not_decnz(r[6],clear),builder.while_decnz(r[6],())]
    return logical+t.emit(theory)+gate+t.emit(vacuity)+t.TAIL

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--search',action='store_true')
    ap.add_argument('--repo',type=Path,default=REPO)
    ap.add_argument('--scratch',type=Path,default=ROOT/'work/psc_compiled')
    ap.add_argument('--grouped',action='store_true')
    ap.add_argument('--kernel',choices=('subset','empty'),default='subset')
    args=ap.parse_args()
    repo=args.repo.resolve();out=args.scratch.resolve()
    if out==repo or repo in out.parents:
        ap.error('scratch must be outside the input checkout')
    if not (repo/'Computability/BusyBeaver/Research/ZFC/theory_backend_experiment.py').is_file():
        ap.error('provide the pinned ProveIt checkout with --repo')
    load_sources(repo)
    out.mkdir(parents=True,exist_ok=True)
    for name in ('TMBuilder.py','tm.py','tmdb.py','LICENSE.wade'):
        (out/name).write_bytes(git_bytes(None,'ZF/generator/'+name))
    nodes,names=parse_dag(git_bytes(None,'ZF/m254/coq/prog/Dag254.v').decode())
    sys.path.insert(0,str(out));backend=importlib.import_module('TMBuilder')
    results=[]
    orders=list(itertools.permutations((1,3,5,7))) if args.search else [(1,7,5,3)]
    arrangements=list(itertools.product((False,True),(False,True))) if args.search else [(False,False)]
    for dual,order,(support_first,vacuity_first) in itertools.product((False,True),orders,arrangements):
        b=builder_from_dag(backend,nodes,names)
        b.sequence_lookup={s.seq:i for i,s in enumerate(b.sequences)}
        prog=program(b,order,dual,args.grouped,args.kernel,support_first,vacuity_first)
        name=args.kernel+'_'+('grouped_' if args.grouped else 'gated_')+('dual_' if dual else 'old_')+''.join(map(str,order))+f'_{int(support_first)}{int(vacuity_first)}'
        t.lower_program(b,nodes,prog,name,shared=True,base3=True)
        b.generate();b.tm.gc()
        states={q for q,_ in b.tm.states}
        path=out/(name+'.tm');b.tm.save(str(path))
        results.append({'name':name,'working_states':len(states),'rows':len(b.tm.states),
             'framework':sum(q[0].isdigit() for q in states),
             'theory_macros':len(t.emit(psc(args.kernel,support_first))),
             'rho_order':[9-i for i in order], 'dual':dual,
             'support_first':support_first,'vacuity_first':vacuity_first,
             'sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
    evidence={'status':'REJECTED: Boolean obstruction proves abstract nonhalting','results':results,
              'minimum':min(r['working_states'] for r in results)}
    (out/(args.kernel+'_results.json')).write_text(json.dumps(evidence,indent=2)+'\n')
    best=[r for r in results if r['working_states']==evidence['minimum']]
    print(json.dumps({'minimum':evidence['minimum'],'cases':len(results),'minimizers':best},indent=2))

if __name__=='__main__':main()
