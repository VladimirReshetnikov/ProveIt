import sys as _assertion_sys
if not __debug__ or _assertion_sys.flags.optimize:
    raise RuntimeError("Assertions must be enabled; do not use -O or PYTHONOPTIMIZE.")
"""Independently written shifted binary pairing source experiment.
Downloaded code is parsed only as mathematical DAG data. No imports from repo.
"""
from pathlib import Path
import re,json,hashlib,functools,collections,time
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'generated'
OUT.mkdir(parents=True,exist_ok=True)
SRC=ROOT/'inputs/Dag254.v'
if hashlib.sha256(SRC.read_bytes()).hexdigest()!='538ddaddd932058c2b319011126579d77783231f54331772377c05848a0599e3':
    raise ValueError('Pinned Dag254.v hash mismatch; run code/fetch_inputs.py')
N,T,W,A,D,H,X,Y,L=range(9)
def I(r): return ('I',r)
def Dn(r): return ('D',r)
def B(k): return ('B',k)
def C(k): return ('C',k)
def node(a,b): return ('N',a,b)
def seq(*xs):
    assert xs
    return xs[0] if len(xs)==1 else node(xs[0],seq(*xs[1:]))
def resolve(t,label,z=0,o=0):
    if t[0]=='N': return node(resolve(t[1],label,z+1,o),resolve(t[2],label,z,o+1))
    if t[0]=='b' and t[1]==label: return B(z)
    if t[0]=='c' and t[1]==label: return C(o)
    return t
def loop(r,*body,label='loop'):
    return resolve(seq(Dn(r),*body,('c',label)),label)
def transfer(s,t): return loop(s,I(t))
def pair_shifted():
    # (X,T,Y)=(a,b,0) -> (0,0,2^a(2b+1)-1).
    double_t=loop(T,I(Y),I(Y))
    double_y=loop(Y,I(T),I(T))
    outer=loop(X,double_y,transfer(T,Y),I(Y))
    return seq(double_t,outer)
def unpair_shifted(s):
    # First failed decrement recognizes even; second failed decrement odd.
    even=resolve(node(node(Dn(s),('b','test')),('b','outer')),'test')
    half=resolve(seq(even,Dn(s),I(Y),('c','half')),'half')
    return resolve(seq(half,I(X),transfer(Y,s),('c','outer')),'outer')
def read_source():
    text=SRC.read_text(); entries={}; names={}
    for m in re.finditer(r'\| (\d+) => \((E\w+(?: \d+)?), (E\w+(?: \d+)?)\)\s+\(\* (.*?) \*\)',text):
        q=int(m[1]);names[q]=m[4]
        def edge(s):
            p=s.split();k={'ENode':'ref','EInc':'I','EDecnz':'D','EBreak':'B','EContinue':'C','EHalt':'H'}[p[0]]
            return (k,int(p[1])) if len(p)>1 else(k,)
        entries[q]=node(edge(m[2]),edge(m[3]))
    assert len(entries)==219
    return entries,names
ENTRIES,NAMES=read_source()
def expand(replacements={}):
    @functools.cache
    def visit(t):
        if t[0]=='ref': return replacements[t[1]] if t[1] in replacements else visit(ENTRIES[t[1]])
        if t[0]=='N': return node(visit(t[1]),visit(t[2]))
        return t
    return visit(('ref',0)),visit

def run(tree,values,fuel=2000000):
    steps=0
    def exe(t):
        nonlocal steps
        steps+=1
        if steps>fuel:raise RuntimeError('fuel')
        if t[0]=='N':
            while True:
                action=exe(t[1])
                if action[0]=='B':return ('ok',) if action[1]==1 else B(action[1]-1)
                if action[0]!='ok':return action
                action=exe(t[2])
                if action[0]=='C':
                    if action[1]==1:continue
                    return C(action[1]-1)
                return action
        k=t[0]
        if k=='I':values[t[1]]+=1;return('ok',)
        if k=='D':
            if values[t[1]]:values[t[1]]-=1;return('ok',)
            return B(1)
        return t
    result=exe(tree)
    return result,steps

def sizes(t):
    nodes=set(); leaves=[]; paths=[]
    def go(t,path):
        if t[0]=='N':nodes.add(t);go(t[1],path+'0');go(t[2],path+'1')
        else:leaves.append(t);paths.append(path)
    go(t,'')
    return {'primitive_leaves':len(leaves),'hashcons_binary_nodes':len(nodes),'max_depth':max(map(len,paths)),
            'max_zero_run':max(len(z)for p in paths for z in p.split('1')),
            'primitive_occurrences':{str(k):v for k,v in sorted(collections.Counter(leaves).items())}}

def serialize(t):
    nodes=[];known={}
    def enc(t):
        if t[0]!='N':return list(t)
        if t not in known:known[t]=len(nodes);nodes.append(None);nodes[known[t]]=[enc(t[1]),enc(t[2])]
        return ['ref',known[t]]
    root=enc(t);return {'root':root,'nodes':nodes}

def entry_contract_abstraction(replacements={}):
    """Sound zero/nonzero collecting abstraction over all main-loop iterations.
    Dec of a positive natural has two abstract successors. Every root exit loops.
    The analysis may overapproximate, never exclude a concrete reachable state.
    """
    leaves=[];paths=[];markers={};nodepaths={}
    def walk_ref(t,path):
        if t[0]=='ref':
            q=t[1]
            start=len(leaves)
            nodepaths[path]=start
            walk_ref(replacements.get(q,ENTRIES[q]),path)
            if q in (115,116,162):markers[path]=(q,start,len(leaves))
            return
        if t[0]=='N':
            nodepaths[path]=len(leaves);walk_ref(t[1],path+'0');walk_ref(t[2],path+'1')
        else:nodepaths[path]=len(leaves);paths.append(path);leaves.append(t)
    walk_ref(('ref',0),'')
    def nxt(p):
        i=p.rfind('0')
        return nodepaths[p[:i]+'1'] if i>=0 else 0
    def brk(p,k):
        for _ in range(k):
            i=p.rfind('0')
            if i<0:return 0
            p=p[:i]
        return nxt(p)
    def cont(p,k):
        for _ in range(k):
            i=p.rfind('1')
            if i<0:return 0
            p=p[:i]
        return nodepaths[p]
    normal=[nxt(p)for p in paths]
    zero=[brk(p,1)for p in paths]
    jump=[brk(p,t[1]) if t[0]=='B' else cont(p,t[1]) if t[0]=='C' else 0 for p,t in zip(paths,leaves)]
    entry=collections.defaultdict(list)
    for p,(q,start,end) in markers.items():entry[start].append((q,end))
    observed=collections.defaultdict(set)
    # bit set means positive, absent means zero.
    seed=(1<<N)|(1<<D)
    reached=[set()for _ in leaves];todo=collections.deque([(0,seed,-1)]);states=0
    while todo:
        pc,mask,previous=todo.popleft()
        for q,end in entry.get(pc,[]):
            if not pc<=previous<end:observed[q].add(mask)
        if mask in reached[pc]:continue
        reached[pc].add(mask);states+=1
        t=leaves[pc];k=t[0]
        if k=='I':todo.append((normal[pc],mask|1<<t[1],pc))
        elif k=='D':
            bit=1<<t[1]
            if mask&bit:
                todo.append((normal[pc],mask,pc));todo.append((normal[pc],mask&~bit,pc))
            else:todo.append((zero[pc],mask,pc))
        elif k in ('B','C'):todo.append((jump[pc],mask,pc))
        elif k=='H':pass
        else:raise ValueError(t)
    return {'abstract_states':states,'source_leaf_sites':len(leaves),'marker_site_count':len(markers),
      'entry_masks':{str(q):sorted(ms)for q,ms in observed.items()},
      'unpair_scratch_clean':all(not m&((1<<X)|(1<<Y))for q in(115,116)for m in observed[q]),
      'pair_output_clean':all(not m&(1<<Y)for m in observed[162]),
      'soundness_note':'Finite inductive zero/nonzero overapproximation; positive decrements split into zero and positive; root overflow returns to root.'}

def main():
    original,_=expand();new,visit=expand({115:unpair_shifted(L),116:unpair_shifted(W),162:pair_shifted()})
    pairs=unpairs=0;maxsteps=0
    for a in range(9):
      for b in range(12):
        values=[13,0,17,19,23,29,0,0,31];values[X]=a;values[T]=b;expected=values.copy();expected[X]=expected[T]=0;expected[Y]=(1<<a)*(2*b+1)-1
        result,steps=run(pair_shifted(),values);assert result==('ok',)and values==expected,(a,b,result,values,expected)
        pairs+=1;maxsteps=max(maxsteps,steps)
    for s in(L,W):
      for n in range(2049):
        values=[13,17,19,23,29,31,0,0,37];values[s]=n;expected=values.copy();q=n;a=0
        while q&1:a+=1;q>>=1
        expected[s]=0;expected[X]=a;expected[Y]=q//2
        result,steps=run(unpair_shifted(s),values);assert result==('ok',)and values==expected,(s,n,result,values,expected)
        unpairs+=1;maxsteps=max(maxsteps,steps)
    result={'source_sha256':hashlib.sha256(SRC.read_bytes()).hexdigest(),'original_source':sizes(original),'shifted_source':sizes(new),
      'helpers':{name:sizes(t)for name,t in [('pair_original',expand()[1](('ref',162))),('pair_shifted',pair_shifted()),('unpair_original',expand()[1](('ref',115))),('unpair_shifted',unpair_shifted(L))]},
      'tests':{'pair_contract_cases':pairs,'unpair_contract_cases':unpairs,'largest_interpreter_steps':maxsteps},
      'contracts':{'pair':'X=a,T=b,Y=0 -> X=T=0,Y=E(a,b); all other registers unchanged',
                   'unpair':'source=n,X=Y=0 -> source=0,X=v2(n+1),Y=((n+1)/2^X-1)/2; all other registers unchanged'},
      'clean_entry_audit':entry_contract_abstraction(),
      'status':'REGISTER_SOURCE_ONLY; NO_BINARY_MACHINE_OR_ZFC_CALIBRATION_CLAIM'}
    (OUT/'shifted-source.json').write_text(json.dumps(serialize(new),indent=2)+'\n')
    (OUT/'helpers.json').write_text(json.dumps({k:serialize(v)for k,v in {'pair':pair_shifted(),'unpairL':unpair_shifted(L),'unpairW':unpair_shifted(W)}.items()},indent=2)+'\n')
    assert result['clean_entry_audit']['unpair_scratch_clean'] and result['clean_entry_audit']['pair_output_clean']
    audit=entry_contract_abstraction({115:unpair_shifted(L),116:unpair_shifted(W),162:pair_shifted()})
    assert audit['unpair_scratch_clean'] and audit['pair_output_clean']
    (OUT/'shifted-clean-entry-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
    (OUT/'shifted-source-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
