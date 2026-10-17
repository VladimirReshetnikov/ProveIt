#!/usr/bin/env python3
"""Measure a binder-free E7 proof generator with the public Wade backend.

This is an experimental compiler-cost measurement, not a ZFC consistency
machine. All generated tables stay in external scratch. The control source
retains the old exhaustive candidate/DROP/NIP/cache shell, replacing AX and MP
with ground-equational proof generation. Query code1 means q(c)=c and is a
placeholder. The actual ZFC target/writer and binary startup/runtime proofs
are absent. The generic Wade boot is counted, but is not verified here to
establish the new register invariant.

Example:
  python3 -B equational_generator_cost.py --seeds 32 --scratch /tmp/e7-cost \
    --output results/equational-generator-cost.json
"""
from __future__ import annotations
import argparse
import collections
import copy
import hashlib
import importlib
import io
import json
from pathlib import Path
import platform
import subprocess
import sys
import tempfile
import time
from zipfile import ZipFile

import recover_wade_dag as recover
from pairing_backend_experiment import execute_helper
from full_grammar_experiment import safe_repair, expand, normalize

ROOT=Path(__file__).resolve().parents[4]
ARRIVAL='61e77836565f63582561f54745f633d50efd9c7d'
ARCHIVE='docs/incoming/zfc_consistency_research_20261016.zip'
MEMBER='zfc_consistency_research_20261016/experiments/equational/basis.json'


def read_basis(repo,work):
    archive=subprocess.check_output(['git','show',f'{ARRIVAL}:{ARCHIVE}'],cwd=repo)
    with ZipFile(io.BytesIO(archive)) as z:
        raw=z.read(MEMBER)
    (work/'basis.json').write_bytes(raw)
    basis=json.loads(raw)
    assert basis['equations_total']==7 and basis['symbols_total']==88
    assert basis['signature']=={'c':0,'n':2,'q':1,'r':1}
    assert [e['name'] for e in basis['equations']]==['Sh1','Rhom','R3','Qext','Qadd','Qcomp','Qrot']
    return basis,{'arrival_commit':ARRIVAL,'archive':ARCHIVE,'member':MEMBER,
                  'archive_sha256':hashlib.sha256(archive).hexdigest(),
                  'basis_sha256':hashlib.sha256(raw).hexdigest(),'basis_bytes':len(raw)}


def run(args):
    repo=args.repo.resolve()
    work=args.scratch.resolve() if args.scratch else Path(tempfile.mkdtemp(prefix='zfc-equational-generator-'))
    if work==repo or repo in work.parents or work==Path('/'):
        raise ValueError('scratch must be outside the repository and not filesystem root')
    work.mkdir(parents=True,exist_ok=True)
    recover.SNAPSHOT=repo/'lib/jeff-busy-beaver-zfc254'
    inputs=[]
    for name in ('TMBuilder.py','tm.py','tmdb.py','LICENSE.wade'):
        relative='ZF/generator/'+name
        data=recover.git_bytes(None,relative);(work/name).write_bytes(data)
        inputs.append({'path':'lib/jeff-busy-beaver-zfc254/'+relative,
                       'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()})
    raw=recover.git_bytes(None,'ZF/m254/coq/prog/Dag254.v')
    inputs.append({'path':'lib/jeff-busy-beaver-zfc254/ZF/m254/coq/prog/Dag254.v',
                   'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()})
    nodes,names=recover.parse_dag(raw.decode())
    basis,basis_provenance=read_basis(repo,work)
    sys.path.insert(0,str(work));backend=importlib.import_module('TMBuilder')
    b=recover.builder_from_dag(backend,nodes,names)
    b.sequence_lookup={s.seq:i for i,s in enumerate(b.sequences)}
    regs=[b.reg(n) for n in recover.REGISTERS]
    def seq(items,name):
     q=b.add_sequence(tuple(items))
     if isinstance(q,int) and b.sequences[q].name is None:b.sequences[q].name=name+'.0'
     return q
    triple=seq([regs[1].inc]*3,'triple')
    loop=seq([regs[6].decnz,seq([triple,'_continue.2'],'mul3body')],'mul3loop')
    scale=seq([216,loop],'mul3top')
    q=seq([scale,regs[1].inc],'Q')
    r=seq([scale,regs[1].inc,regs[1].inc],'R')
    # Only old formula-pair scaler changes4→3; Cantor stack pairing is untouched.
    assert b.sequences[118].seq[0]==156
    b.sequences[118].seq=(157,b.sequences[118].seq[1])
    n=seq([119,triple],'NAND')
    pairmove=seq([regs[7].decnz,seq([regs[1].inc,'_continue.2'],'pairmoveloop')],'pairmovetest')
    eq=seq([160,162,pairmove],'EQpair')
    macros={'x':166,'y':121,'z':168,'q':q,'r':r,'n':n}
    def emit(t):
     if isinstance(t,str):return [macros[t]]
     return [x for a in t[1:] for x in emit(a)]+[macros[t[0]]]
    words=[emit(e['left'])+emit(e['right'])+[eq] for e in basis['equations']]
    word=[x for w in words for x in w]
    def move(i,j):
     return seq([regs[i].decnz,seq([regs[j].inc,'_continue.2'],'movebody')],'move')
    def clear(i):return seq([regs[i].decnz,'_continue.1'],'clear')
    def times3(i,j):
     return seq([regs[i].decnz,seq([seq([regs[j].inc]*3,'threeincs'),'_continue.2'],'times3body')],'times3')
    untop=seq([regs[1].decnz,154],'unpair_top')
    uncache=seq([regs[5].decnz,154],'unpair_cache')
    sym=seq([untop,208,211,162,pairmove],'symmetry')
    mapq=seq([untop,times3(6,1),regs[1].inc,216,times3(7,1),regs[1].inc,162,pairmove],'mapQ')
    mapr=seq([untop,times3(6,1),regs[1].inc,regs[1].inc,216,times3(7,1),regs[1].inc,regs[1].inc,162,pairmove],'mapR')
    nrev=seq([160,move(1,7),208,211,162,117,triple],'NANDreverse')
    def coord(constructor):
     return seq([clear(5),untop,208,move(7,5),166,constructor,121,166,constructor,eq,clear(5)],'congruence')
    nleft=coord(n)
    nright=coord(nrev)
    success=seq([pairmove,eq],'trans_success')
    failure=seq([clear(7),160,clear(6)],'trans_failure')
    conditional=seq([seq([123,seq([success,'_break.1'],'trans_done')],'trans_equal'),failure],'trans_conditional')
    trans=seq([clear(4),untop,move(7,4),208,171,uncache,197,conditional],'transitivity')
    # New field only for former MP: operation0=trans,1=sym,2=Q,3=R,4=NAND-left,>=5=NAND-right.
    def switch(choices,default):
     if not choices:return default
     return seq([seq([regs[3].decnz,seq([switch(choices[1:],default),'_break.1'],'switch_escape')],'switch_test'),choices[0]],'switch')
    dispatch=switch([trans,sym,mapq,mapr,nleft],nright)
    b.sequences[150].seq=(174,seq([dispatch,clear(3)],'inference_tail'))
    # AX has x=param1, y=cache+nextfield, z=axiomcode. It pushes all7 valid instances.
    emitter=seq(word,'basis7')
    b.sequences[1].seq=(176,seq([emitter,clear(3),clear(4),clear(5)],'axioms_tail'))
    roots={'Qterm':q,'Rterm':r,'NANDterm':n,'raw_pair':eq,
           'sym':sym,'Q':mapq,'R':mapr,'left':nleft,'right':nright,'trans':trans,
           'dispatch':b.sequences[150].seq[1]}
    source_builder=copy.deepcopy(b)
    b.reduce_to_cons();b.name_sequences()
    P=lambda a,c:(a+c)*(a+c+1)//2+c
    checks=collections.Counter()
    # Exact AST execution of all88 constructor calls, independently of counters.
    inv={166:'x',121:'y',168:'z',q:'q',r:'r',n:'n',eq:'eq'}
    stack=['oldtop']
    for token in word:
        op=inv[token]
        if op in ('x','y','z'):stack.append(op)
        elif op in ('q','r'):stack[-1]=(op,stack[-1])
        else:
            rightterm,leftterm=stack.pop(),stack.pop()
            stack.append((op,leftterm,rightterm))
    ast=lambda t:tuple(ast(v) for v in t) if isinstance(t,list) else t
    assert stack==['oldtop']+[('eq',ast(e['left']),ast(e['right'])) for e in basis['equations']]
    checks['literal_basis_AST_endpoints']=14
    for value in range(33):
        for root,expected in ((q,3*value+1),(r,3*value+2)):
            for oldstack in (0,1,5):
                v=[7,value,oldstack,11,13,17,0,0,19]
                assert execute_helper(b,root,v)==('normal',)
                assert v==[7,expected,oldstack,11,13,17,0,0,19]
                checks['constructor_register_runs']+=1
    for a in range(7):
        for c in range(7):
            for oldstack in (0,1,5):
                for root,expected in ((n,3*P(a,c)+3),(eq,P(a,c))):
                    v=[7,c,P(a,oldstack),11,13,17,0,0,19]
                    assert execute_helper(b,root,v)==('normal',)
                    assert v==[7,expected,oldstack,11,13,17,0,0,19]
                    checks['constructor_register_runs']+=1
    for a in range(4):
        for c in range(4):
            for d in range(4):
                for e in range(4):
                    v=[7,P(a,c),5,0,11,P(d,e),0,0,19]
                    assert execute_helper(b,trans,v)==('normal',)
                    assert v==[7,P(a,e) if c==d else 0,5,0,0,0,0,0,19]
                    checks['transitivity_register_runs']+=1
    for a in range(4):
        for c in range(4):
            for term in range(4):
                cases=[(sym,P(c,a),P(2,3)),(mapq,P(3*a+1,3*c+1),P(2,3)),
                       (mapr,P(3*a+2,3*c+2),P(2,3)),
                       (nleft,P(3*P(a,term)+3,3*P(c,term)+3),0),
                       (nright,P(3*P(term,a)+3,3*P(term,c)+3),0)]
                for root,wantedtop,cache in cases:
                    if root in (nleft,nright) and max(a,c,term)>1:continue
                    v=[7,P(a,c),5,0,term,P(2,3),0,0,19]
                    assert execute_helper(b,root,v,fuel=20000000)==('normal',)
                    assert v==[7,wantedtop,5,0,term,cache,0,0,19]
                    checks['other_inference_register_runs']+=1
    # Test dispatch including opcode aliases>=5, then actual old main() field reads.
    expected=[P(0,0),P(1,0),P(1,4),P(2,5),P(3,6),P(3,9)]
    for operation in range(8):
        op=min(operation,5)
        v=[7,P(0,1),0,operation,0,P(1,0),0,0,0]
        assert execute_helper(b,roots['dispatch'],v)==('normal',)
        assert v==[7,expected[op],0,0,0,0 if op in (0,4,5) else 1,0,0,0]
        checks['dispatch_register_runs']+=1
    for operation in range(6):
        packed=P(0,P(0,P(operation,0)))
        v=[7,P(0,1),0,0,0,P(1,0),0,0,packed+1]
        assert execute_helper(b,0,v,fuel=20000000)==('normal',)
        assert v==[7,expected[operation],0,0,0,0 if operation in (0,4,5) else 1,0,0,0]
        checks['main_field_read_register_runs']+=1
    print('Finite checks',dict(checks),flush=True)
    records=[];best={}
    for mode in ('emitter','control'):
        for seed in [None,*range(args.seeds)]:
            b=copy.deepcopy(source_builder)
            if seed is None:
                residual,productions=word,[]
            else:
                residual,productions,_=safe_repair(word,seed,2.0)
                assert expand(residual,productions)==word
            ids={}
            for i,ab in enumerate(productions):
                ids[300+i]=seq([ids.get(v,v) for v in ab],'grammar'+str(i))
            emitterroot=seq([ids.get(v,v) for v in residual],'basis7_grammar')
            if mode=='emitter':b.sequences[0].seq=(emitterroot,'halt')
            else:b.sequences[1].seq=(176,seq([emitterroot,clear(3),clear(4),clear(5)],'axioms_grammar_tail'))
            b.reduce_to_cons();b.name_sequences();b.generate();b.tm.gc()
            live=list(b.reachable())
            regids={name:i for i,name in enumerate(recover.REGISTERS)}
            def edge(value):
                if isinstance(value,int):return 'ENode '+str(value)
                if value=='halt':return 'EHalt'
                if value.startswith('_break.'):return 'EBreak '+value.split('.')[-1]
                if value.startswith('_continue.'):return 'EContinue '+value.split('.')[-1]
                _,name,kind=value.split('.')
                return ('EInc ' if kind=='inc' else 'EDecnz ')+str(regids[name])
            candidate_nodes={i:tuple(edge(e) for e in b.sequences[i].seq) for i in live}
            candidate_names={i:b.sequences[i].name for i in live}
            recover.reextract(b.tm,candidate_nodes,candidate_names)
            table,labels,missing=normalize(b.tm)
            working={q for q,_ in b.tm.states}
            frame={q for q in working if q[0].isdigit()}
            tag=mode+('-unshared' if seed is None else'-seed'+str(seed))
            artifact=work/(tag+'.tm');artifact.write_bytes(table)
            (work/(tag+'-labels.json')).write_text(json.dumps(labels,indent=2)+'\n')
            (work/(tag+'-dag.json')).write_text(json.dumps({'root':0,'nodes':candidate_nodes,'names':candidate_names},indent=2)+'\n')
            record={'mode':mode,'seed':seed,'working_states':len(working),
                    'decision_states':len(working-frame),'framework_states':len(frame),
                    'total_rows':2*len(working),'residual_tokens':len(residual),'productions':len(productions),
                    'decision_edges_reextracted_exact':True,'table':str(artifact),
                    'table_sha256':hashlib.sha256(table).hexdigest()}
            records.append(record)
            if mode not in best or record['working_states']<best[mode]['working_states']:
                best[mode]=record
    result={'scope':'Experimental E7 ground-equational proof-generator control source; no ZFC target, consistency calibration or binary startup/runtime proof.',
            'upstream_commit':recover.COMMIT,'attribution':'Mira-Cult/Jeff/Wade pinned program/arithmetic/framework; E7 basis from attributed new research arrival.',
            'basis_source':basis_provenance,'backend_inputs':inputs,'command':[sys.executable,*sys.argv],
            'python':platform.python_version(),'scratch':str(work),'finite_checks':dict(checks),
            'basis_postfix_calls':len(word),'raw_eq_record':'P(a,b)',
            'term_codes':{'c':0,'q':'3n+1','r':'3n+2','NAND':'3P(a,b)+3'},
            'query_placeholder':'cached code1=P(1,0), namely q(c)=c; actual ZFC query and writer absent',
            'totalization':'Sole undefined1.inc/read1 filled write1,R,halt; no extra working state',
            'verification_limit':'0..3 NAND grid was interrupted in the initial scratch prototype because nested unary Cantor stacks grew too large. The completed suite uses0..1 NAND inputs; other cases are stated in source.',
            'startup_limit':'Generic Wade boot is included in counts. Its establishment of the new proof invariant is not proved or assumed here.',
            'best':best,'runs':records}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'best':best,'evidence':str(args.output)},indent=2),flush=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo',type=Path,default=ROOT)
    parser.add_argument('--scratch',type=Path)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--seeds',type=int,default=32)
    args=parser.parse_args()
    if not __debug__:parser.error('Assertions must remain enabled')
    if args.seeds<0:parser.error('seeds must be nonnegative')
    run(args)

if __name__=='__main__':main()
