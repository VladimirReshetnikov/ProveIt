#!/usr/bin/env python3
"""Independent source binding and free-constructor-algebra emitter audit.

This parser, expansion, and symbolic stack evaluator do not import the
construction compiler. The primitive macro semantics remain attributed
mathematical interfaces, not a newly formalized arithmetic proof.
"""
from pathlib import Path
from functools import lru_cache
import argparse,collections,hashlib,json,re,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'reference'))
import source_language as sl
if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Assertions must be enabled; do not use -O.')

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def tuples(x):return tuple(map(tuples,x))if isinstance(x,list)else x
def parse_program():
    definitions={}
    for line in (HERE/'inputs/Program.lean').read_text().splitlines():
        m=re.fullmatch(r'def ((?:node|x)\d+) : Tree := (.+)',line)
        if not m:continue
        ts=collections.deque(re.findall(r'\(|\)|\.[A-Za-z]+|(?:node|x)\d+|\d+',m[2]))
        def parse():
            t=ts.popleft()
            if t=='(':
                answer=parse();assert ts.popleft()==')';return answer
            if t=='.node':return(parse(),parse())
            if t=='.leaf':return parse()
            if t in('.inc','.dec','.continueTo','.breakTo','.halt'):
                return('leaf',t[1:],None if t=='.halt'else int(ts.popleft()))
            assert t in definitions
            return t
        definitions[m[1]]=parse();assert not ts
    assert len(definitions)==159
    return definitions

def grammar(path):
    g=json.loads(path.read_text())
    def expand(t):
        if isinstance(t,list):return tuples(t)
        if t in g['rules']:return tuple(expand(x)for x in g['rules'][t])
        return t
    return expand(g['root'])

def source(definitions,ax,k):
    ns=dict(definitions);inc=('leaf','inc',1)
    triple=(inc,'node60')
    ns['node61']=(triple,'node60'if k==5 else triple)
    ns['x67']=ax
    @lru_cache(None)
    def expand(t):
        if isinstance(t,str):return expand(ns[t])
        if len(t)==3 and t[0]=='leaf':
            return({'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}[t[1]],t[2])
        return(expand(t[0]),expand(t[1]))
    tree=expand('node172')
    return tree,sl.sites(tree),ns

def words(t):
    if isinstance(t,tuple)and len(t)==2:return words(t[0])+words(t[1])
    if t=='node60':return[('leaf','inc',1)]*2
    assert t!='node61','Coefficient body may not occur as a literal formula tag.'
    return[t]

def emitter(ax,k,exchange):
    zero=('zero',);one=('succ',zero)
    succ=lambda x:('succ',x)
    I=lambda a,b:('I',k,a,b)
    M=lambda a,b:succ(I(a,b))
    U=lambda a,b:succ(succ(I(b,a)))
    E=lambda a,b:succ(succ(succ(I(a,b))))
    N=lambda a:I(a,one)
    And=lambda a,b:N(I(a,N(b)))
    Ex=lambda a,b:N(U(a,N(b)))
    t,a,d,h,x,y=(('atom',v)for v in('t','a','d','h','x','y'))
    A,D,H,T=a,d,h,t;stack=[];fields=collections.deque([y,x])
    ww=words(ax)
    assert len(ww)==190
    assert ww[-3:]==['node142','node150',('leaf','breakTo',1)]
    for op in ww[:-3]:
        if op=='node49':stack.append(T);T=zero
        elif op in('node55','node58','node70'):
            stack.append(T);T={'node55':D,'node58':H,'node70':A}[op]
        elif op=='node65':T=I(stack.pop(),T)
        elif op==('leaf','inc',1):T=succ(T)
        elif op=='node72':H=('add',H,fields.popleft())
        elif op=='node75':D=('add',D,fields.popleft());T=I(T,D)
        else:raise AssertionError(op)
    assert not fields
    heads=[I(Ex(D,U(D,H)),H),I(U(D,U(A,H)),U(A,U(D,H))),
           I(M(H,D),I(E(H,A),M(A,D))),I(E(H,D),I(M(A,H),M(A,D))),
           Ex(D,E(H,D))]
    old=I(U(D,A),I(U(D,I(A,H)),U(D,H)))
    new=I(U(D,I(A,H)),I(U(D,A),U(D,H)))
    heads.append(new if exchange else old)
    rho=I(I(I(H,d),D),I(I(D,H),I(A,H)))
    gamma=I(A,U(A,A));v=I(M(H,D),U(A,M(H,D)))
    point=I(A,M(A,D))
    S=U(D,And(I(M(H,D),point),I(M(A,D),A)))
    Q=U(A,I(S,N(point)))
    assert stack==[t,U(d,h),rho]+heads+[gamma]
    assert T==N(I(v,Q))
    return dict(macro_tokens=len(ww),pushed_items=len(stack),quantifier_distribution_exchange=exchange,
                stack=stack,unguarded_top=T,guard='A=D or A=H returns truth; A,D,H are cleared by the unchanged guard',
                scope='Exact free-constructor-algebra expansion, with attributed primitive macro contracts.')

def audit(machine,output):
    meta=json.loads((machine/'receipt.json').read_text());k=meta['radix'];assert k in(5,6)
    manifest=json.loads((HERE/'inputs/provenance.json').read_text())
    for name,data in manifest.items():assert sha(HERE/'inputs'/name)==data['sha256']
    definitions=parse_program()
    qg=grammar(HERE/'inputs/q_grammar.json');pg=grammar(HERE/'inputs/primary_grammar.json')
    tree,sites,ns=source(definitions,qg,k)
    parent_tree,parent_sites,parent_ns=source(definitions,pg,k)
    reported=[]
    names={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
    for p,op,arg in json.loads((machine/'sites.json').read_text()):
        if not isinstance(p,str):p=''.join(map(str,p))
        reported.append([p,names[op],arg])
    assert reported==sites
    supplied={key:tuples(value)for key,value in json.loads((machine/'nodes.json').read_text()).items()}
    assert supplied=={**definitions,'node61':ns['node61']}
    qgraph,_=sl.graph_arithmetic(sites);pgraph,_=sl.graph_arithmetic(parent_sites)
    assert qgraph==sl.graph_intervals(sites)and pgraph==sl.graph_intervals(parent_sites)
    # The literal outer command/fetch/shift/MP tree is identical. Only AX
    # descendants can change; instruction ordinals agree because sizes do.
    axprefix='10101001'
    qi=[i for i,(p,_,_)in enumerate(sites)if p.startswith(axprefix)]
    pi=[i for i,(p,_,_)in enumerate(parent_sites)if p.startswith(axprefix)]
    assert qi==pi and qi==list(range(qi[0],qi[-1]+1))
    outside=[i for i in range(len(sites))if i not in set(qi)]
    for i in outside:
        assert sites[i]==parent_sites[i]
        assert qgraph[i]==pgraph[i]
    assert len(sites)==3673+61*(k-4)
    prior=emitter(pg,k,False);new=emitter(qg,k,True)
    changed=[i for i,(a,b)in enumerate(zip(prior['stack'],new['stack']))if a!=b]
    assert changed==[8]and prior['unguarded_top']==new['unguarded_top']
    # Both candidates keep the original MP/Shift (including successful-MP
    # dummy-zero push); they are not the cache-changing PA194Q source.
    assert ns['node163']==('node6','node55')
    assert ns['node168']==('node37','node57')
    assert ns['node170']==('node36','node169')
    assert ns['node171']==('node170','node23')
    out=output/machine.name;out.mkdir(parents=True,exist_ok=True)
    (out/'emitter.json').write_text(json.dumps({'old':prior,'new':new},indent=2)+'\n')
    receipt=dict(status='PASS',radix=k,source_sites=len(sites),source_matches_independent_expansion=True,
        resolved_by_two_independent_algorithms=True,outer_source_sites_unchanged=len(outside),
        AX_range=[qi[0],qi[-1]],pushed_entries=10,only_changed_pushed_entry_zero_based=8,
        modified_schema='U(D,I(A,H)) -> (U(D,A) -> U(D,H))',
        unchanged_guard_and_top=True,original_MP_and_Shift=True,
        source_sha256=sha(machine/'sites.json'),machine_sha256=sha(machine/'machine.tm'),
        scope='Independent exact source and emitter binding. Logical equivalence uses the propositional exchange theorem; no end-to-end proof-assistant endpoint is asserted.')
    (out/'source_audit.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt),flush=True)
    return receipt

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('machines',nargs='+',type=Path)
    parser.add_argument('--output',type=Path,default=HERE/'results')
    args=parser.parse_args()
    for path in args.machines:audit(path,args.output)
