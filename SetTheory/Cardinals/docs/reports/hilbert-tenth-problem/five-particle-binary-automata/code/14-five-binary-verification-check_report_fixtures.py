"""Recreate every numerical report fixture from the exact released compiler."""
from pathlib import Path
import hashlib,json,sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'compiler'))
from five_binary import Machine,BinaryCA
from frontend import Frontend

def fixture():
    rows={'start':['ADD',0,'test'],'test':['SUB',0,'HALT','bad'],'bad':['ADD',1,'bad']}
    ca=BinaryCA(Machine(rows,'start','HALT'))
    x=ca.encode('start',0,3); trace=[sorted(x)]; boundaries=[{'t':0,'q':'start','a':0,'b':3}]
    q,a,b='start',0,3
    total=0
    while q!='HALT':
        duration=ca.duration(q,a,b)
        for _ in range(duration):
            x=ca.step(x);trace.append(sorted(x))
            assert len(x)==5
        total+=duration
        q,a,b=ca.machine.step(q,a,b)
        assert x==ca.encode(q,a,b)
        boundaries.append({'t':total,'q':q,'a':a,'b':b})
    assert total==472
    assert [t for t,v in enumerate(trace) if tuple(int(i in v) for i in range(ca.E))==ca.halt_pattern()]==[472]
    assert ca.step(x)==x
    f=Frontend(ca,2,initial_counters=(0,3)); w=f.witness()
    assert w==json.loads((ROOT/'compiler/example_witness.json').read_text())
    assert f.evaluate(w)==0
    from tempfile import TemporaryDirectory
    with TemporaryDirectory() as td:
        path=Path(td)/'example.json';f.export(path)
        assert path.read_bytes()==(ROOT/'compiler/example_frontend.json').read_bytes()
    data=json.loads((ROOT/'compiler/source-replay/source/literal2.json').read_text())
    uni=BinaryCA(Machine(data['rows'],data['entry'],data['halt']))
    f1=Frontend(uni,1,initial_counters=(1,0))
    assert f1.witness() is None
    with TemporaryDirectory() as td:
        path=Path(td)/'universal.json';f1.export(path)
        assert path.read_bytes()==(ROOT/'compiler/universal_h1_frontend.json').read_bytes()
    kappas=[ca.duration(q,0 if r[0]=='ADD' else 1,0 if r[0]=='ADD' else 1)- (0 if r[0]=='ADD' else 2) for q,r in rows.items()]
    u_kappas=[]
    for q,r in uni.machine.rows.items():
        u_kappas.append(3+2*uni.Z+(1 if r[0]=='ADD' else -1)-2*uni.K-2*uni.C-uni.codes['O',q]-uni.codes['I',q])
    assert uni.ledger()==json.loads((ROOT/'compiler/checks.json').read_text())['universal']
    tex=(ROOT/'report/five-particle-binary-compiler.tex').read_text()
    for token in ('756,787','50,452','1,272,679,260','10,750h','2,344h+1','512,938','529,754','472'):
        assert token in tex, ('missing report fixture value',token)
    for name in ('five_binary.py','frontend.py'):
        assert hashlib.sha256((ROOT/'compiler'/name).read_bytes()).hexdigest() in tex
    return dict(status='passed',small=dict(rows=rows,codes={role+':'+q:d for (role,q),d in ca.codes.items()},ledger=ca.ledger(),boundaries=boundaries,trace=trace,witness=w,frontend=f.ledger()),universal=dict(ledger=uni.ledger(),kappa_min=min(u_kappas),kappa_max=max(u_kappas),h1_accepts=False,h1_ledger=f1.ledger()),source_sha256=hashlib.sha256((ROOT/'compiler/source-replay/source/literal2.json').read_bytes()).hexdigest())

if __name__=='__main__':
    data=fixture()
    dest=ROOT/'report/figures/verified_trace.json'
    encoded=json.dumps(data,indent=2)+'\n'
    if '--write' in sys.argv:dest.write_text(encoded)
    else:assert dest.read_text()==encoded,'report fixture mismatch'
    print(json.dumps({k:v for k,v in data.items() if k!='small'},indent=2))
