import json
from pathlib import Path
from five_binary import Machine, BinaryCA
from frontend import Frontend


def run():
    machine=Machine({'start':['ADD',0,'test'], 'test':['SUB',0,'HALT','bad'],
                     'bad':['ADD',1,'bad']},'start','HALT')
    ca=BinaryCA(machine)
    checked=0
    for real in (False,True):
        for a,b in ((0,0),(0,5),(1,0),(8,7)):
            for clock in (False,True):
                f=Frontend(ca,2,initial_counters=(a,b),clock=clock,nonnegative_real=real)
                w=f.witness()
                assert w is not None and f.evaluate(w)==0
                for i in range(len(w)):
                    altered=w.copy();altered[i]+=1
                    assert f.evaluate(altered)>0,(i,f.names[i])
                assert f.ledger()['witness_variables']==2*(f.B+2)+clock
                assert f.ledger()['squared_residual_slots']==2*(4+1+real)+1+clock
                checked+=1
        for h in (0,1,3,4):
            assert Frontend(ca,h,nonnegative_real=real).witness() is None
        assert Frontend(ca,0,initial_state='HALT',nonnegative_real=real).witness() == [0]
        # Explicit zero old counter cannot take DEC with nonnegative postvalue.
        f=Frontend(ca,1,initial_state='test',initial_counters=(0,3),nonnegative_real=real)
        w=[0]*len(f.names)
        j=next(j for j,x in enumerate(f.branches) if x.source=='test' and x.op=='DEC')
        w[f.selectors[0][j]]=1;w[f.counter_variables[0][1]]=3
        assert dict(f.residual_values(w))['0.counter0']==1
    example=Frontend(ca,2,initial_counters=(0,3))
    example.export(Path(__file__).with_name('example_frontend.json'))
    Path(__file__).with_name('example_witness.json').write_text(json.dumps(example.witness())+'\n')
    data=json.loads((Path(__file__).parent/'source-replay/source/literal2.json').read_text())
    uni=BinaryCA(Machine(data['rows'],data['entry'],data['halt']))
    f=Frontend(uni,1,initial_counters=(1,0))
    assert f.ledger()['witness_variables']==10751
    assert f.ledger()['squared_residual_slots']==2346
    f.export(Path(__file__).with_name('universal_h1_frontend.json'))
    out=dict(status='passed',mutation_tested_accepting_instances=checked,
             example=example.ledger(),universal_h1=f.ledger())
    Path(__file__).with_name('frontend_checks.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':
    run()
