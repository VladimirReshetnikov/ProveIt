#!/usr/bin/env python3
"""Reproduce the finite-kernel and 252-state research evidence offline.

Default: complete machine replay, independent 100,000-candidate order audit,
all reference tests and all two/three-object local EPSC cases. --quick skips
only the three-object EPSC census. This is not a proof-assistant endpoint.
"""
from pathlib import Path
import argparse
import copy
import hashlib
import importlib.util
import json
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/'code'))
import represented_epsc_kernel as G
import clause_codec as C
import check_epsc_block as E
import check_drop_barrier as B
import check_box_transport as X
from ground_resolution import equality_axioms, freeze, validate_term
from representation_and_audit import class_term, parameter_assignment, exists, nand, atom


def read(path):
    return json.loads(path.read_text())


def json_form(obj):
    return json.loads(json.dumps(obj))


def source_checks():
    bridge=ROOT/'provenance/inherited_bridge'
    rows=read(bridge/'source_manifest.json')
    for row in rows:
        raw=(bridge/row['local_path']).read_bytes()
        assert len(raw)==row['bytes']
        assert hashlib.sha256(raw).hexdigest()==row['sha256']
        prefix=('blob '+str(len(raw))+chr(0)).encode()
        assert hashlib.sha1(prefix+raw).hexdigest()==row['git_blob_sha1']
    original=ROOT/'machine/vendor/busy-beaver/ZF/m254/coq/tm/Prog254.v'
    assert (bridge/'coq/tm/Prog254.v').read_bytes()==original.read_bytes()
    earlier=ROOT/'provenance/earlier_enumerator'
    files=read(earlier/'source_manifest.json')['files']
    for row in files:
        raw=(earlier/row['local_path']).read_bytes()
        assert len(raw)==row['bytes']
        assert hashlib.sha256(raw).hexdigest()==row['sha256']
    return {'bridge_files':len(rows),'earlier_enumerator_files':len(files),
            'decoder_source_identical_to_machine_package':True}


def original_baseline():
    path=ROOT/'provenance/fak12_original_generator.py'
    spec=importlib.util.spec_from_file_location('prior_fak12',path)
    old=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(old)
    raw=json_form({'signature':old.SIG,'relations':old.RELS,
                   'universally_closed_clauses':old.CLAUSES})
    assert raw==read(ROOT/'provenance/fak12_original_clauses.json')
    fs=raw['signature']
    def term(t):
        return '?'+t[0] if len(t)==1 and t[0] not in fs else [t[0],*(term(a) for a in t[1:])]
    return {'name':'FAK12 prior reference, faithful format conversion',
            'functions':fs,'predicates':{('eq' if p=='=' else p):a for p,a in raw['relations'].items()},
            'clauses':[{'name':f'prior{i}_'+row['source'],
                        'literals':[{'positive':l[0],'predicate':'eq' if l[1]=='=' else l[1],
                                     'args':[term(t) for t in l[2:]]} for l in row['literals']]}
                       for i,row in enumerate(raw['universally_closed_clauses'])]}


def payload_checks():
    variants={'fak12_baseline_clauses.json':original_baseline(),
              'fak5_clauses.json':G.kernel(),
              'fak5_shared_clauses.json':G.shared_kernel(),
              'fak5_named_selector_clauses.json':G.named_selector_kernel(),
              'fec16b_compressed_clauses.json':G.commutative_nand_kernel()}
    term=G.commutative_nand_kernel('term')
    term['name']='FEC native predicate branch, term selector, commutative NAND'
    variants['fec15b_compressed_clauses.json']=term
    for selector in ('term','defined','distinct'):
        variants['fec_predicate_gate_'+selector+'_clauses.json']=G.predicate_gate_kernel(selector)
    expected={x['file']:x for x in read(ROOT/'evidence/codec_comparison.json')}
    result=[]
    for fn,k in sorted(variants.items()):
        path=ROOT/'data'/fn
        assert k==read(path),fn
        raw,m=C.encode(k);decoded,n=C.decode(raw)
        assert decoded==C.canonical(k) and n==m['meaningful_bits']
        assert raw==path.with_suffix('.bin').read_bytes()
        assert m==read(path.with_suffix('.codec.json'))==expected[fn]['native']
        ke=dict(k,clauses=k['clauses']+equality_axioms(k['functions'],k['predicates']))
        eraw,em=C.encode(ke);ed,en=C.decode(eraw)
        assert ed==C.canonical(ke) and en==em['meaningful_bits']
        assert em==expected[fn]['explicit_equality']
        result.append({'file':fn,'native_bits':n,'explicit_equality_bits':en,'sha256':m['sha256']})
    return result


def formula_checks():
    formula=exists(2,nand(atom(0,2),nand(atom(2,1),atom(3,2))))
    rows=[]
    for mode,fn in [('term','fec15b_compressed_clauses.json'),('named','fec16b_compressed_clauses.json')]:
        k=read(ROOT/'data'/fn)
        selectors=[G.selector_term(i,mode) for i in range(6)]
        ct=class_term(formula,mode)
        assignment=parameter_assignment({2:'?p2',3:'?p3'},mode)
        for t in selectors+[ct]:
            assert not G.term_vars(t)
            validate_term(freeze(t),k['functions'],ground=True)
        validate_term(freeze(assignment),k['functions'])
        assert selectors[1]==(['N',['o'],['o']] if mode=='term' else ['q'])
        rows.append(dict(selector_mode=mode,kernel=fn,formula=formula,class_term=ct,
                         parameter_assignment=assignment,selectors=selectors,term_nodes=G.term_nodes(ct)))
    assert json_form(rows)==read(ROOT/'evidence/formula_compiler_modes.json')
    return {'modes':['term','named'],'expanded_examples_match':True}


def clause_checks(full):
    result={}
    for fn in ['fak5_shared_clauses.json','fec15b_compressed_clauses.json','fec16b_compressed_clauses.json']:
        k=read(ROOT/'data'/fn)
        two=E.exhaustive_two(k)
        assert two==read(ROOT/'evidence/epsc_block_independent.json')['two']
        result[fn]={'two':two}
    final=read(ROOT/'data/fec16b_compressed_clauses.json')
    if full:
        three=E.constructed_three(final)
        assert three==read(ROOT/'evidence/epsc_block_independent.json')['three']
        result['fec16b_compressed_clauses.json']['three']=three
    rejected=[]
    for name,index in [('unbounded_output',0),('empty_closure',0),('support',2)]:
        bad=copy.deepcopy(final)
        row=next(c for c in bad['clauses'] if c['name']==name)
        row['literals'][index]['positive']=not row['literals'][index]['positive']
        try:
            E.exhaustive_two(bad)
        except AssertionError:
            rejected.append(name)
        else:
            raise AssertionError('Mutated EPSC clause was not rejected')
    result['mutated_clauses_rejected']=rejected
    return result


def command(cmd,cwd=None):
    p=subprocess.run(cmd,cwd=cwd or ROOT,text=True,capture_output=True)
    if p.returncode:
        raise RuntimeError('Command failed:\n'+' '.join(map(str,cmd))+'\n'+p.stdout+p.stderr)
    return p.stdout+p.stderr


def main():
    if not __debug__:
        raise SystemExit('Run without -O: assertions verify the research evidence.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--quick',action='store_true')
    ap.add_argument('--output',type=Path,default=ROOT/'replay-results.json')
    ap.add_argument('--lean',type=Path,help='Optionally check all four standalone Lean modules')
    args=ap.parse_args()
    started=time.monotonic()
    result={'scope':'Reproducible finite certificates and local checks; see report for ordinary proofs and formalization limits.',
            'quick':args.quick,'source_provenance':source_checks(),
            'payloads':payload_checks(),'formula_compiler':formula_checks()}
    print('PASS: all nine payloads, exact binary formats, equality costs and formula modes.',flush=True)
    result['reference_tests']=command([sys.executable,'-m','unittest','discover','-s','code','-p','test_reference.py','-v'])
    print('PASS: reference refuter, 512 clause sets, certificates, equality and malformed inputs.',flush=True)
    result['closure_checks']=clause_checks(not args.quick)
    print('PASS: independent EPSC witnesses and clause mutations.',flush=True)
    order=B.audit(100000)
    assert json_form(order)==read(ROOT/'evidence/drop_barrier_check.json')
    result['drop_barrier']=order
    print('PASS: 100,000 candidate codes and every marked pop/push image.',flush=True)
    boxes=X.check(ROOT/'machine')
    assert json_form(boxes)==read(ROOT/'evidence/box_transport_check.json')
    result['box_transport']=boxes
    print('PASS: independent complete-tape register-box transport controls.',flush=True)
    with tempfile.TemporaryDirectory(prefix='zfc252-replay-') as td:
        replay=Path(td)/'machine'
        result['machine_log']=command([sys.executable,str(ROOT/'machine/code/reproduce.py'),'--output',str(replay)])
        result['machine']=read(replay/'summary.json')
    print('PASS: complete 252-state blank prefix, root frame and all 33,564 uniform runtime cases.',flush=True)
    if args.lean:
        result['lean']={p.name:command([str(args.lean.resolve()),str(p)])
                        for p in sorted((ROOT/'formal').glob('*.lean'))}
        print('PASS: four standalone Lean modules.',flush=True)
    result['elapsed_seconds']=round(time.monotonic()-started,3)
    args.output.resolve().write_text(json.dumps(result,indent=2)+'\n')
    print('All requested checks passed; result:',args.output.resolve(),flush=True)


if __name__=='__main__':
    main()
