"""Protect actual intermediate decoder states needed by retained source roles."""
from pathlib import Path
import sys,json
sys.dont_write_bytecode=True
P=Path('/tmp/k218-qs-span-dp');sys.path.insert(0,str(P))
import source_language as s,build221 as b,global_allocator_v2 as g
O=Path(__file__).resolve().parent
seed=Path(json.loads((P/'input.json').read_text())['seed'])
old=s.tree(json.loads((seed/'sites218.json').read_text()))
new=s.tree(json.loads((P/'verified/candidate000/sites.json').read_text()))
T=b.read_table((seed/'k218.native.tm').read_bytes())
groups,paths=b.decoder_map(T,old)
live=set()
def visit(n):
    if s.leaf(n) or n in live:return
    live.add(n);visit(n[0]);visit(n[1])
visit(new)
protected=set();witnesses=[]
for q, pp in paths.items():
    for p in pp:
        n=s.subtree(old,p)
        if n not in live:continue
        for bit in (0,1):
            if s.leaf(n[bit]):continue
            tape={i:int(v)for i,v in enumerate(p+str(bit))};tape[-1]=1
            before=dict(tape);h=len(p);state=q;trace=[]
            for tick in range(100):
                if h==len(p)+1:break
                assert h in tape
                row=T[state,tape[h]];trace.append([state,h,tape[h],list(row)])
                if tick:protected.add(state)
                w,d,state=row;tape[h]=w;h+=d
            assert h==len(p)+1 and tape==before
            if len(trace)>1:witnesses.append({'state':q,'prefix':p,'bit':bit,'trace':trace})
result={'protected_states':sorted(protected),'old_live_helper_witnesses':witnesses,
        'scope':'Old retained-role internal prefix helpers only; no primitive-runtime or startup proof.'}
try:
    U,r=g.compile_tree(s,b,T,old,new,protected_states=frozenset(protected))
    result['status']='PREFIX_BINDING_PASS';result['receipt']=r
    (O/'protected.tm').write_bytes(b.table_bytes(U))
except (ValueError,AssertionError,KeyError)as e:
    result['status']='REJECTED';result['error']=repr(e)
(O/'protected-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k!='old_live_helper_witnesses'}))
