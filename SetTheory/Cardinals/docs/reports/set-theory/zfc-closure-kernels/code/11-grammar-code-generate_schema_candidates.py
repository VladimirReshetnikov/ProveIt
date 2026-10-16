#!/usr/bin/env python3
"""Reproduce the schema-permuted candidates, optionally rebracketed to 248 states.

Usage:
  python generate_schema_candidates.py --repo /path/to/ProveIt --output /tmp/schema-candidates

Optionally add --rebracket-dir /path/to/zfc_one_schema_research/machine to
apply the incoming report's hash-pinned Re-Pair method to both new AX words.

Use ProveIt commit 17d0f2eaa650901cda59764dfcc4661c199e49c8. The selected
research files and the attributed upstream inputs are checked by SHA-256.
Only the output directory is written. This experiment does not establish a
ZFC-consistency bound; the equality-free calibration remains open, and the
dual-rho6 variant has an additional relative-falsity calibration obligation.
"""
from pathlib import Path
import argparse, hashlib, importlib, json, sys

SOURCE_PIN = '17d0f2eaa650901cda59764dfcc4661c199e49c8'
UPSTREAM_PIN = '297ab8df7e5de329605c3875b4934643b371a5e3'
THEORY_SHA256 = '37043e71a02fba57337040100d79e8f92cba5e2ac5efead816b1522b8663a2e1'
RESEARCH_SHA256 = {
    'theory_backend_experiment.py': THEORY_SHA256,
    'recover_wade_dag.py': 'caa4996be46f9201991dba07f81d4673f14e874ac682226c29fce9e0cea851f1',
    'pairing_backend_experiment.py': '18f6cf1a50514581834daecd542d9855d07d6c522d4d70f906241de035423572',
    'audit_raw_candidate.py': 'cb029edc99925b359bc79ebb6605f109f452292fbcd1e0d6d52b259c8193d41d',
}
# This companion is used for the separately reported finite table audits.
# It is checked here for reproducibility, but is not executed by this generator.
VALIDATION_SHA256 = {
    'audit_tm.py': '40e55849aaa1f40c3ef70e0b23fb8b7b1fa3d0742cc0ea6006d27e84d931291f',
}
REBRACKET_SHA256 = 'bdbf5a84ab1a2914e351e917d7ff3994fec5729bddbe33971678cd51c2839119'
PRIOR_VERIFIER_SHA256 = '30fbd95b7a2a61004422558cfab4419de5239b67b88bc9ed19b7de8fcf585f18'

def builder_dag(builder,register_names):
    reachable=set(builder.reachable());root=builder.find_seq('main().0')
    order=[root]+sorted(reachable-{root});ids={q:i for i,q in enumerate(order)}
    def edge(x):
        if isinstance(x,int):return f'ENode {ids[x]}'
        if x=='halt':return 'EHalt'
        if x.startswith('_'):
            return ('EBreak ' if x.startswith('_break.') else 'EContinue ')+x.rsplit('.',1)[1]
        _,reg,op=x.split('.')
        return ('EInc ' if op=='inc' else 'EDecnz ')+str(register_names.index(reg))
    return {ids[q]:tuple(edge(x) for x in builder.sequences[q].seq) for q in order}, {ids[q]:builder.sequences[q].name for q in order}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--rebracket-dir',type=Path)
    args=ap.parse_args()
    repo=args.repo.resolve();out=args.output.resolve()
    if out==repo or repo in out.parents:
        ap.error('output must be outside the supplied repository')
    research=repo/'Computability/BusyBeaver/Research/ZFC'
    for filename,digest in (RESEARCH_SHA256 | VALIDATION_SHA256).items():
        if hashlib.sha256((research/filename).read_bytes()).hexdigest()!=digest:
            raise ValueError(filename+' differs from the source pin')
    out.mkdir(parents=True,exist_ok=True)
    work=out/'backend';work.mkdir(exist_ok=True)
    sys.path.insert(0,str(research))
    import recover_wade_dag as r
    import theory_backend_experiment as t
    from audit_raw_candidate import normalize_named
    for name in ('TMBuilder.py','tm.py','tmdb.py','LICENSE.wade'):
        (work/name).write_bytes(r.git_bytes(None,'ZF/generator/'+name))
    sys.path.insert(0,str(work))
    backend=importlib.import_module('TMBuilder')
    grammar=None
    if args.rebracket_dir:
        prior=args.rebracket_dir.resolve()
        for filename,digest in {'rebracket_axioms.py':REBRACKET_SHA256,
                               'verify_rm_certificate.py':PRIOR_VERIFIER_SHA256}.items():
            if hashlib.sha256((prior/filename).read_bytes()).hexdigest()!=digest:
                raise ValueError(filename+' differs from the incoming report pin')
        sys.path.insert(0,str(prior))
        grammar=importlib.import_module('rebracket_axioms')
    nodes,names=r.parse_dag(r.git_bytes(None,'ZF/m254/coq/prog/Dag254.v').decode())
    _,_,baseline_contract=t.old_contract(nodes)
    spec,spec_digest=t.published_spec()
    old=spec['ax_rows']('a','h','b','c','u')
    permutation={'a':'b','b':'u','c':'a','u':'c'}
    inverse={'a':'c','b':'a','c':'u','u':'b'}

    def rename(f,p):
        if isinstance(f,tuple):return (f[0],*(rename(x,p) for x in f[1:]))
        return p.get(f,f)

    lukasiewicz=rename(old[1],permutation)
    assert rename(lukasiewicz,inverse)==old[1]
    # It is an exact permutation of four arbitrary schema parameters.
    # No logical equivalence, quantifier change, or falsity assumption is used.
    assert lukasiewicz == t.Imp(t.Imp(t.Imp('a','c'),'b'),t.Imp(t.Imp('b','a'),t.Imp('u','a')))
    C=spec['bundle_C']('a','b','c');G=spec['bundle_G']('a','b','c')
    V=t.Imp(t.Rel('a','b'),t.All('c',t.Rel('a','b')))
    bundle=t.And(V,t.And(C,G))
    results=[]
    for variant in ('dual_rho6','old_rho6'):
        rho6=t.Imp('b',t.All('a',t.Ex('a','b'))) if variant=='dual_rho6' else old[3]
        forms=[lukasiewicz,old[7],old[5],rho6]
        program=[166,121,180,176]
        for f in forms:program+=t.emit(f)
        program+=t.emit(bundle)+t.TAIL
        decoded,events=t.symbolic(program)
        assert decoded==['old_top',t.All('a','h'),*forms,bundle]
        assert program.count(158)==1
        b=r.builder_from_dag(backend,nodes,names)
        b.sequence_lookup={s.seq:i for i,s in enumerate(b.sequences)}
        t.lower_program(b,nodes,program,'schema_extended',shared=True,base3=True)
        b.generate();b.tm.gc()
        machine=b.tm
        grammar_metadata={}
        if grammar is not None:
            # This reuses the prior report's algorithm, not its original word.
            # Its helper bodies are unchanged except the already selected
            # multiply-three formula scaler, also present in the reference.
            original=nodes.copy()
            if original[118][0]!='ENode 156':raise ValueError('unexpected scaler source')
            original[118]=('ENode 157',original[118][1])
            if not all(grammar.bounder(original)(f'ENode {q}')==(0,0) for q in set(program)):
                raise ValueError('an AX word helper can escape its control scope')
            seed=39 if variant=='dual_rho6' else 122
            residual,productions=grammar.repair(program,seed,2)
            newnodes,newnames,axroot=grammar.transform(original,names,residual,productions)
            reference,reference_names=builder_dag(b,r.REGISTERS)
            grammar.reextract(machine,reference,reference_names)
            certificate,stats=grammar.bisimulation(reference,newnodes)
            machine=grammar.compile_dag(backend,newnodes,newnames)
            grammar.reextract(machine,newnodes,newnames)
            for suffix,payload in (
                ('reference-dag',{'root':0,'nodes':reference,'names':reference_names}),
                ('dag',{'root':0,'nodes':newnodes,'names':newnames,'axioms_root':axroot}),
                ('rm-bisimulation',certificate)):
                (out/f'{variant}-{suffix}.json').write_text(json.dumps(payload,indent=2,sort_keys=True)+'\n')
            grammar_metadata={'prior_rebracketing_algorithm_sha256':REBRACKET_SHA256,
                              'rebracketing_seed':seed,'rebracketing_alpha':2,
                              'grammar_productions':len(productions),'residual_word_length':len(residual),
                              'all_AX_helpers_break_continue_closed':True,
                              'rm_bisimulation':stats,'finite_RM_certificate_not_kernel_proof':True}
        named=out/f'{variant}-named.tm';machine.save(str(named))
        numeric,labels,metadata=normalize_named(named.read_bytes())
        n=metadata['working_states']
        machine_path=out/f'raw-candidate-{variant}-{n}.tm';machine_path.write_bytes(numeric)
        (out/f'{variant}-labels.json').write_text(json.dumps(labels,indent=2,sort_keys=True)+'\n')
        states={q for q,_ in machine.states}
        metadata.update({'variant':variant,'working_states':n,
                         'decision_states':sum(not q[0].isdigit() for q in states),
                         'framework_states':sum(q[0].isdigit() for q in states),
                         'numeric_filename':machine_path.name,'named_filename':named.name,
                         'symbolic_AX_formula_stack_exact':True,
                         'fourth_parameter_read_count':program.count(158),
                         'lukasiewicz_schema_bijective_permutation':permutation,
                         'lukasiewicz_inverse_parameter_permutation':inverse,
                         'schema_permutation_inverse_checked_as_syntax':True,
                         'logical_row_order':['rho8','rho2','rho4',variant],
                         'bundle':'V AND (C AND G)',
                         'formula_code':'Imp=3P, Rel=3P+1, All=3P+2',
                         'unchanged_original_freshness_gate':True,
                         'formal_compiler_and_ZFC_calibration':False})
        metadata.update(grammar_metadata)
        results.append(metadata)
    result={'ProveIt_source_commit':SOURCE_PIN,'upstream_source_commit':UPSTREAM_PIN,
            'theory_backend_experiment_sha256':THEORY_SHA256,
            'executed_research_source_sha256':RESEARCH_SHA256,
            'companion_auditor_sha256_checked_not_executed':VALIDATION_SHA256,
            'executed_backend_source_sha256':{name:digest for name,digest in r.SOURCE_SHA256.items()
                                              if name.endswith('.py')},
            'pinned_program_and_spec_sha256':{
                'ZF/m254/coq/prog/Dag254.v':r.SOURCE_SHA256['ZF/m254/coq/prog/Dag254.v'],
                'ZF/m254/tools/logic/spec.py':spec_digest},
            'prior_rebracketing_algorithm_sha256':REBRACKET_SHA256 if grammar else None,
            'companion_independent_engine_sha256_checked_not_executed':PRIOR_VERIFIER_SHA256 if grammar else None,
            'baseline_symbolic_contract':baseline_contract,'candidates':results,
            'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'claim':'Uncalibrated raw proof-search candidates; no new proved ZFC-consistency state bound.'}
    (out/'schema-candidates.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':main()
