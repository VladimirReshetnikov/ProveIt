"""Untrusted, named-proof serializer for predecessor-computation packets.

This adapts the attributed generated-assumptions example producer. It is
not imported by any checker. The only changed primitive packet supplies
the predecessor iterator rather than a claimed successor iterator.
"""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parent / 'reference/initialized_producer.py'
spec = importlib.util.spec_from_file_location('inherited_named_producer', SOURCE)
p = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p)


class Emitter(p.Emitter):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.box_count = 0

    def emit(self, proof, context):
        if proof['rule'] != 'Computation':
            return super().emit(proof, context)
        goal = self.formula(proof['goal'])
        if goal in context:
            self.trace.append({'rule':'Hyp', 'goal':goal, 'floor':self.floor, 'instruction':None})
            return
        _, source, rhs = proof['goal']
        assert p.compute(source)['goal'] == proof['goal']
        _, counter, seed, state, update = source
        if counter != 0 and counter[1] == 0:
            # The literal predecessor zero is falsy. Name a proved zero
            # with a syntactically nonempty I0 term, generate its IS
            # equation, then transport the entire equation along z=0.
            self.box_count += 1
            name = '__counter_zero_' + str(self.box_count)
            zero = p.I(0, 0, name + '_state', 0)
            z_proof = p.compute(zero)
            def instance(v):
                recursive = p.I(v, seed, state, update)
                return p.Eq(p.I(p.S(v), seed, state, update),
                            p.substitute(update, state, recursive))
            boxed = p.compute(p.I(p.S(zero), seed, state, update))
            expanded = p.transport(z_proof, name, instance(p.V(name)), boxed,
                                   role='literal_zero_predecessor')
            assert expanded['goal'] == proof['goal']
            return self.emit(expanded, context)
        position = len(self.instructions)
        self.trace.append({'rule':'Computation', 'goal':goal, 'floor':self.floor,
                           'instruction':position, 'mode':None})
        predecessor = counter if counter == 0 else counter[1]
        source_packet = p.I(predecessor, seed, state, update)
        self.instructions.append([0, self.term(source_packet), 0, 0])
        self.allocate()
        self.trace.append({'rule':'InsertedHyp','goal':goal,'floor':self.floor,'instruction':None})


def build():
    cases=[]
    for case in p.build_cases():
        if 'proof_tree' not in case:
            continue
        emitter = Emitter(allow_forbidden_compound_progress=not case['accept'])
        packet=emitter.packet(case['proof_tree'])
        cases.append({'name':case['name'], 'accept':case['accept'],
                      'packet':packet,'trace':emitter.trace,'boxes':emitter.box_count})
    explicit = [
        ('literal_zero_step_state',p.compute(p.I(p.ONE,p.TWO,'e_u',p.S(p.V('e_u'))))),
        ('literal_zero_step_constant',p.compute(p.I(p.ONE,p.TWO,'e_u',p.ONE))),
        ('literal_zero_step_zero',p.compute(p.I(p.ONE,p.TWO,'e_u',0))),
    ]
    for name,proof in explicit:
        emitter=Emitter()
        cases.append({'name':name,'accept':True,'packet':emitter.packet(proof),
                      'trace':emitter.trace,'boxes':emitter.box_count})
    # Additional successful aliases under the explicit erased-tree decoder.
    for name,predecessor in [('binary_zero_predecessor',[0,0]),
                             ('unary_mapping_predecessor',{'':[-999]}),
                             ('empty_mapping_predecessor',{}),
                             ('empty_string_predecessor','')]:
        source=[predecessor,0,[0]]
        counter=[predecessor] if predecessor else predecessor
        expected=[0] if predecessor else 0
        packet=[[0,source,0,0],[[counter,0,[0]],expected]]
        cases.append({'name':name,'accept':True,'packet':packet})
        wrong=0 if predecessor else [0]
        cases.append({'name':name+'_wrong','accept':False,
                      'packet':[[0,source,0,0],[[counter,0,[0]],wrong]]})
    # Each generic boundary below concerns the NEW protocol.
    def raw(name,packet):
        cases.append({'name':name,'accept':False,'packet':packet})
    source=[0,0,0]
    raw('false_zero_equals_one',[[0,source,0,0],[0,[0]]])
    raw('unallocated_goal_name',[[0,source,0,0],[-1,-1]])
    raw('malformed_source_arity',[[0,[0,0,0,0],0,0],[source,0]])
    raw('missing_seed',[[0,[[0],None,0],0,0],[source,0]])
    raw('nonempty_string_predecessor',[[0,['x',0,0],0,0],[source,0]])
    raw('nonempty_key_mapping_predecessor',[[0,[{'x':0},0,0],0,0],[source,0]])
    raw('future_seed_capture',[[0,[0,-1,0],0,0],[0,[0]]])
    # Mutate freshly emitted proofs rather than old packet formats.
    for name,base,rule,field,value in [
        ('unallocated_witness','nonvacuous_witness_DE_roundtrip','DI',3,-999),
        ('unallocated_specialization','Q_arbitrary_term_specialization','QE',2,-999),
        ('base_replacing_induction_hypothesis','atomic_progress_closure','DI',0,[]),
    ]:
        case=next(c for c in cases if c['name']==base)
        event=next(e for e in case['trace'] if e['rule']==rule)
        packet=copy.deepcopy(case['packet']);packet[event['packet_index']][field]=value
        raw(name,packet)
    return cases


def main():
    cases=build()
    (ROOT/'joint_cases.json').write_text(json.dumps(cases,indent=2)+'\n')
    fixtures=ROOT/'joint_fixtures';fixtures.mkdir(exist_ok=True)
    for c in cases:
        (fixtures/(c['name']+'.json')).write_text(json.dumps(c['packet'])+'\n')
    programs=['checker_joint.py','checker_joint_readable.py']
    records=[]
    for name in programs:
        if not (ROOT.parent/'code'/name).exists():
            continue
        for optimized in [False,True]:
            for case in cases:
                args=[sys.executable]+(['-O'] if optimized else [])+[str(ROOT.parent/'code'/name)]
                r=subprocess.run(args,input=json.dumps(case['packet']),text=True,capture_output=True,timeout=15)
                accepted=r.returncode==0 and r.stdout.strip()=='ACCEPT'
                passed=accepted==case['accept']
                records.append({'program':name,'optimized':optimized,'case':case['name'],
                                'expected':case['accept'],'accepted':accepted,'passed':passed,
                                'returncode':r.returncode})
                if not passed:
                    print(name, optimized, case['name'], r.stdout, r.stderr[-1000:])
    result={'case_count':len(cases),'runs':len(records),'passed':sum(r['passed'] for r in records),'records':records}
    (ROOT.parent/'evidence/joint_verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='records'},indent=2))
    if not all(r['passed'] for r in records):
        raise SystemExit(1)

if __name__=='__main__':
    main()
