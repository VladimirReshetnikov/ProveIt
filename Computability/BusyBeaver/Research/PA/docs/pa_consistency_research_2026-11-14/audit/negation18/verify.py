#!/usr/bin/env python3
"""Portable source/CFG and polynomial-loop certificate for NEG18.

No optimizer or supplied source compiler is imported.  The universal core
argument checks its exact primitive CFG, four terminating loop summaries, and
the polynomial identities connecting the summaries.  Numeric replays are
additional controls, not the universal argument.  This is not a Lean theorem
or a proof of any complete smaller physical Turing machine.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,ast,hashlib,json,re

HERE=Path(__file__).resolve().parent
def require(p,msg):
    if not p:raise ValueError(msg)

def parse_source(path):
    nodes={}
    for line in path.read_text().splitlines():
        m=re.fullmatch(r'def (\w+) : Tree := (.*)',line)
        if not m:continue
        toks=re.findall(r'\.[A-Za-z]+|[A-Za-z_]\w*|\d+|[()]',m[2]);pos=0
        def rec():
            nonlocal pos
            t=toks[pos];pos+=1
            if t=='(':
                result=rec();require(toks[pos]==')','unclosed expression');pos+=1;return result
            if t=='.node':return (rec(),rec())
            if t=='.leaf':
                require(toks[pos]=='(','leaf operand');pos+=1
                op=toks[pos][1:];pos+=1
                arg=None if toks[pos]==')'else int(toks[pos])
                if arg is not None:pos+=1
                require(toks[pos]==')','unclosed leaf');pos+=1
                return ('leaf',op,arg)
            require(t in nodes,'forward or unknown node');return nodes[t]
        nodes[m[1]]=rec();require(pos==len(toks),'unparsed source token')
    return nodes

def leaves(tree,p=''):
    if tree[0]=='leaf':return [(p,tree[1],tree[2])]
    return leaves(tree[0],p+'0')+leaves(tree[1],p+'1')

def resolve(tree):
    ls=leaves(tree);intervals={}
    for i,(p,_,_)in enumerate(ls):
        for n in range(len(p)+1):
            prefix=p[:n]
            if prefix not in intervals:intervals[prefix]=[i,i]
            else:intervals[prefix][1]=i
    def ancestor(p,bit,n):
        at=[i for i,b in enumerate(p)if b==str(bit)]
        require(0<n<=len(at),'control transfer depends on external context')
        return p[:at[-n]]
    out=[]
    for i,(p,op,a)in enumerate(ls):
        if op=='inc':ins=('inc',a,i+1)
        elif op=='dec':ins=('dec',a,intervals[ancestor(p,0,1)][1]+1,i+1)
        elif op=='continueTo':ins=('jump',intervals[ancestor(p,1,a)][0])
        elif op=='breakTo':ins=('jump',intervals[ancestor(p,0,a)][1]+1)
        elif op=='halt':ins=('halt',)
        else:raise ValueError(op)
        out.append(ins)
    return out

def resolve_structural(tree):
    """Second resolver: recursive loop-context stacks, no paths or intervals."""
    def size(t):return 1 if t[0]=='leaf'else size(t[0])+size(t[1])
    out=[]
    def emit(t,start,breaks,continues):
        if t[0]!='leaf':
            split=start+size(t[0]);end=split+size(t[1])
            emit(t[0],start,breaks+[end],continues)
            emit(t[1],split,breaks,continues+[start]);return
        require(start==len(out),'structural source order');_,op,a=t
        if op=='inc':ins=('inc',a,start+1)
        elif op=='dec':require(breaks,'unbound structural dec');ins=('dec',a,breaks[-1],start+1)
        elif op=='continueTo':require(0<a<=len(continues),'unbound structural continue');ins=('jump',continues[-a])
        elif op=='breakTo':require(0<a<=len(breaks),'unbound structural break');ins=('jump',breaks[-a])
        elif op=='halt':ins=('halt',)
        else:raise ValueError(op)
        out.append(ins)
    emit(tree,0,[],[]);return out

CORE=[('dec',1,4,1),('inc',7,2),('inc',6,3),('jump',0),
      ('dec',6,10,5),('inc',7,6),('dec',6,9,7),('inc',1,8),
      ('jump',6),('jump',0),('dec',7,16,11),('inc',1,12),
      ('inc',1,13),('inc',1,14),('inc',1,15),('jump',10)]

class P:
    """Exact rational multivariate polynomials in T,S,Y."""
    def __init__(self,x=0):
        if isinstance(x,P):self.d=dict(x.d)
        elif isinstance(x,dict):self.d={m:F(c)for m,c in x.items()if c}
        else:self.d={}if x==0 else{(0,0,0):F(x)}
    def __add__(self,other):
        d=dict(self.d)
        for m,c in P(other).d.items():d[m]=d.get(m,0)+c
        return P(d)
    __radd__=__add__
    def __neg__(self):return P({m:-c for m,c in self.d.items()})
    def __sub__(self,other):return self+-P(other)
    def __rsub__(self,other):return P(other)+-self
    def __mul__(self,other):
        d={}
        for m,c in self.d.items():
            for n,e in P(other).d.items():
                k=tuple(a+b for a,b in zip(m,n));d[k]=d.get(k,0)+c*e
        return P(d)
    __rmul__=__mul__
    def __pow__(self,n):
        out=P(1)
        for _ in range(n):out=out*self
        return out
    def __eq__(self,other):return self.d==P(other).d
    def sub(self,values):
        out=P()
        for powers,c in self.d.items():
            term=P(c)
            for x,n in zip(values,powers):term=term*(x**n)
            out=out+term
        return out

T=P({(1,0,0):1});S=P({(0,1,0):1});Y=P({(0,0,1):1})
ZERO=P();V=[T,S,Y];REGISTER={1:0,6:1,7:2}
def tri(x):return x*(x+1)*F(1,2)
def pair(a,b):return tri(a+b)+b

def symbolic_trace(cfg,path,initial=V):
    v=list(initial)
    for k,pc in enumerate(path[:-1]):
        ins=cfg[pc];target=path[k+1]
        if ins[0]=='inc':v[REGISTER[ins[1]]]+=1;require(target==ins[2],'bad inc edge')
        elif ins[0]=='jump':require(target==ins[1],'bad jump edge')
        else:
            require(ins[0]=='dec'and target==ins[3],'symbolic trace must specify positive branch')
            v[REGISTER[ins[1]]]-=1
    return v

def loop_certificate(cfg):
    require(cfg==CORE,'raw node64 differs from the declared CFG')
    # These cycles have a single tested counter. Their positive guard makes the
    # unique decrement safe, their variants fall by one, and no other guard is
    # crossed before returning. All non-counter updates are nonnegative.
    cycles=[(0,1,[0,1,2,3,0],[T-1,S+1,Y+1],4),
            (6,6,[6,7,8,6],[T+1,S-1,Y],9),
            (10,7,[10,11,12,13,14,15,10],[T+4,S,Y-1],16)]
    for pc,r,path,expect,exitpc in cycles:
        require(cfg[pc][0:2]==('dec',r)and cfg[pc][2]==exitpc,'cycle guard/exit')
        require(sum(cfg[i][0]=='dec'for i in path[:-1])==1,'hidden cycle guard')
        require(symbolic_trace(cfg,path)==expect,'cycle affine effect')
        require(expect[REGISTER[r]]==V[REGISTER[r]]-1,'natural variant')
    dt=[ZERO,S+T,Y+T];ds=[T+S,ZERO,Y];dy=[T+4*Y,S,ZERO]
    # Verify each summary is invariant under a positive body and equals the
    # unchanged store after taking its zero exit.
    for counter,summary,body in [(0,dt,cycles[0][3]),(1,ds,cycles[1][3]),(2,dy,cycles[2][3])]:
        require([p.sub(body)for p in summary]==summary,'drain summary induction')
        zero=list(V);zero[counter]=ZERO
        require([p.sub(zero)for p in summary]==zero,'drain summary base')
    # Outer loop at pc4, T=0. Positive S is decremented at4, Y incremented at5,
    # then the proved S-drain, jump9, and proved T-drain return to pc4.
    require(cfg[4]==('dec',6,10,5)and cfg[5]==('inc',7,6)and cfg[9]==('jump',0),'outer CFG')
    after_prefix=symbolic_trace(cfg,[4,5,6],[ZERO,S,Y])
    after_ds=[p.sub(after_prefix)for p in ds]
    body=[p.sub(after_ds)for p in dt]
    require(body==[ZERO,S-1,Y+S],'outer body effect')
    require(body[1]==S-1,'outer natural variant')
    invariant=Y+tri(S)
    require(invariant.sub(body)==invariant,'triangular outer invariant')
    require(invariant.sub([ZERO,ZERO,Y])==Y,'outer invariant base')
    # Compose entry drain, the terminating outer loop, and the Y-times-four drain.
    outer=[ZERO,ZERO,Y+tri(S)]
    after_outer=[p.sub(dt)for p in outer]
    require(after_outer==[ZERO,ZERO,Y+pair(S,T)],'general initial Y pairing identity')
    final=[p.sub(after_outer)for p in dy]
    require(final==[4*(Y+pair(S,T)),ZERO,ZERO],'full core identity')
    # NEG18: preload Y twice, apply the general core at S=Y=0.
    target=4*pair(T,P(1));neg18=final[0].sub([T,ZERO,P(2)])
    require(neg18==target==2*T*T+6*T+8,'NEG18 polynomial identity')
    # NEG21: preload once, apply the same core, then increment T four times.
    require(final[0].sub([T,ZERO,P(1)])+4==target,'NEG21 polynomial identity')
    # Exact loop counts satisfy their base cases and positive-step recurrences.
    outer_count=1+7*tri(S)-2*S
    require(outer_count.sub([T,ZERO,Y])==1,'outer count base')
    require(outer_count==outer_count.sub([T,S-1,Y])+7*S-2,'outer count recurrence')
    composed_count=4*T+1+outer_count.sub([T,S+T,Y])+6*(Y+pair(S,T))+1
    core_count=10*T+13*tri(S+T)-2*(S+T)+6*Y+3
    require(composed_count==core_count,'core count composition')
    require(core_count.sub([T,ZERO,P(2)])+2==13*tri(T)+8*T+17,'NEG18 count composition')
    return {'primitive_cfg_exact':True,'simple_drain_loops':3,
      'outer_loop_invariant':'Y + S*(S+1)/2; T=0 at outer header',
      'terminating_natural_variants':['T at pc0','S at pc6','S at pc4','Y at pc10'],
      'general_core_contract':'(T,S,Y)=(t,s,y) -> (4*(y+p(s,t)),0,0)',
      'frame':'All registers other than 1,6,7 are preserved because no primitive writes them.',
      'neg18_contract':'With registers 6=7=0, INC7;INC7;node64 sends T to 4*p(T,1) and restores registers 6=7=0.',
      'exact_transition_count_recurrences_verified':True}

def run(cfg,registers):
    r=list(registers);pc=0;steps=0
    while pc!=len(cfg):
        require(0<=pc<len(cfg),'escaped source block');steps+=1;require(steps<2000000,'replay bound')
        ins=cfg[pc]
        if ins[0]=='inc':r[ins[1]]+=1;pc=ins[2]
        elif ins[0]=='jump':pc=ins[1]
        elif ins[0]=='dec':
            if r[ins[1]]==0:pc=ins[2]
            else:r[ins[1]]-=1;pc=ins[3]
        else:raise ValueError('unexpected halt')
    return r,steps

def sequence(items):
    result=items[0]
    for t in items[1:]:result=(result,t)
    return result

def dense_native(directory):
    labels=ast.literal_eval(re.search(r'def labels : List Nat := (\[[^\n]+\])',(directory/'Conjugacy.lean').read_text())[1])
    table={}
    for line in(directory/'pa196.tm').read_text().splitlines():
        q,b,w,d,n=line.split();table[labels[int(q)],int(b)]=(int(w),1 if d=='R'else-1,labels[int(n)])
    return table

def entry_states(nodes,table):
    targets={'node64':nodes['node64'],'INC7':('leaf','inc',7)};paths={k:[]for k in targets}
    def visit(t,p=''):
        for name,want in targets.items():
            if t==want:paths[name].append(p)
        if t[0]!='leaf':visit(t[0],p+'0');visit(t[1],p+'1')
    visit(nodes['node172']);result={}
    for name,ps in paths.items():
        states=set()
        for p in ps:
            tape=[1]+list(map(int,p));old=list(tape);q=84;pos=1;end=len(tape)
            for _ in range(500):
                if pos==end:break
                require(0<=pos<end,'decoder accessed unknown cell')
                w,d,q=table[q,tape[pos]];tape[pos]=w;pos+=d
            require(pos==end and tape==old,'decoder failed to restore exact prefix')
            states.add(q)
        require(states==({106}if name=='node64'else{82}),'unexpected native macro entry')
        result[name]={'native_state':next(iter(states)),'source_occurrences_checked':len(ps)}
    return result

def candidate_source_binding(nodes,grammar_path,sites_path,neg18):
    """Independently bind NEG18 to the supplied 197-state seed's full source."""
    grammar=json.loads(grammar_path.read_text());rules=grammar['rules'];memo={};active=set()
    def expand(x):
        if isinstance(x,list):
            require(len(x)==3 and x[0]=='leaf','unexpected candidate leaf');return tuple(x)
        if x in nodes:return nodes[x]
        require(x in rules and x not in active,'unknown or cyclic candidate grammar')
        if x in memo:return memo[x]
        active.add(x);pair=rules[x];require(len(pair)==2,'nonbinary candidate rule')
        result=(expand(pair[0]),expand(pair[1]));active.remove(x);memo[x]=result;return result
    replacement=expand(grammar['root']);count=0
    def replace(t):
        nonlocal count
        if t==nodes['x67']:count+=1;return replacement
        return t if t[0]=='leaf'else(replace(t[0]),replace(t[1]))
    tree=replace(nodes['node172']);require(count==1,'candidate AX occurrence binding')
    supplied=[(''.join(map(str,p)),op,arg)for p,op,arg in json.loads(sites_path.read_text())]
    require(leaves(tree)==supplied,'candidate grammar does not reconstruct exact source sites')
    cfg=resolve(tree);require(cfg==resolve_structural(tree),'candidate independent CFG resolver mismatch')
    def local(ins,i):
        if ins[0]=='inc':return(ins[0],ins[1],ins[2]-i)
        if ins[0]=='dec':return(ins[0],ins[1],ins[2]-i,ins[3]-i)
        if ins[0]=='jump':return(ins[0],ins[1]-i)
        return ins
    entries=[i for i in range(len(cfg)-len(neg18)+1)if [local(x,i)for x in cfg[i:i+len(neg18)]]==neg18]
    require(len(entries)==8,'expected eight exactly bound NEG18 CFG blocks')
    # A mask records exactly which logical registers are positive.  Positive
    # decrement splits into zero/positive outcomes; all other edges are exact.
    # Exhaustive closure is therefore an inductive overapproximation for all
    # natural register values represented by the initial abstract state.
    seen=[0]*len(cfg);seen[25]=1<<1;queue=[(25,1)];cursor=0
    while cursor<len(queue):
        pc,mask=queue[cursor];cursor+=1;ins=cfg[pc];successors=[]
        if ins[0]=='inc':successors=[(ins[2],mask|(1<<ins[1]))]
        elif ins[0]=='jump':successors=[(ins[1],mask)]
        elif ins[0]=='dec':
            bit=1<<ins[1]
            successors=[(ins[3],mask),(ins[3],mask^bit)]if mask&bit else[(ins[2],mask)]
        else:require(ins[0]=='halt','unsupported abstract instruction')
        for nextpc,m in successors:
            require(0<=nextpc<len(cfg),'candidate source exits whole program')
            if not(seen[nextpc]>>m)&1:seen[nextpc]|=1<<m;queue.append((nextpc,m))
    bound=[]
    for pc in entries:
        masks=[m for m in range(512)if(seen[pc]>>m)&1]
        require(masks and all((m&192)==0 for m in masks),'NEG18 clean entry invariant')
        bound.append({'site':pc,'mask_count':len(masks),'registers6_and7_forced_zero':True})
    return {'grammar_sha256':hashlib.sha256(grammar_path.read_bytes()).hexdigest(),
      'sites_sha256':hashlib.sha256(sites_path.read_bytes()).hexdigest(),'source_sites':len(cfg),
      'exact_grammar_source_reconstruction':True,'both_CFG_resolvers_agree':True,
      'exact_NEG18_blocks':bound,'abstract_initial_state':{'source_pc':25,'positive_registers':[0]},
      'inductive_joint_zero_positive_pairs':len(queue),
      'joint_pair_sha256':hashlib.sha256(json.dumps(sorted(queue),separators=(',',':')).encode()).hexdigest(),
      'scope':'The full candidate source is reconstructed independently, every 18-site block has the proved CFG, and a sound finite abstraction proves clean scratch at all its entries from the stated source initial condition. The associated TM runtime and concrete blank startup are certified separately.'}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--source-dir',type=Path,default=HERE/'reference');ap.add_argument('--out',type=Path,default=HERE/'receipt.json');args=ap.parse_args()
    nodes=parse_source(args.source_dir/'Program.lean');core=resolve(nodes['node64']);symbolic=loop_certificate(core)
    require(core==resolve_structural(nodes['node64']),'independent core CFG resolver mismatch')
    full_cfg=resolve(nodes['node172']);require(full_cfg==resolve_structural(nodes['node172']),'independent complete reference CFG resolver mismatch')
    inc1=('leaf','inc',1);inc7=('leaf','inc',7)
    spellings=[('old47',[nodes['node49'],inc1,nodes['node65']],47),
      ('move20',[nodes['node37'],inc1,nodes['node64']],20),
      ('plus8_24',[nodes['node64'],nodes['node61'],nodes['node61']],24),
      ('preload2_18',[inc7,inc7,nodes['node64']],18),
      ('preload1_plus4_21',[inc7,nodes['node64'],nodes['node61']],21)]
    cfgs={}
    for name,seq,n in spellings:
        tree=sequence(seq);cfg=resolve(tree);require(len(cfg)==n,'primitive site count')
        require(cfg==resolve_structural(tree),'independent macro CFG resolver mismatch');cfgs[name]=cfg
    require(cfgs['preload2_18'][:2]==[('inc',7,1),('inc',7,2)],'NEG18 preload CFG')
    shifted=[]
    for ins in CORE:
        if ins[0]=='inc':shifted.append((ins[0],ins[1],ins[2]+2))
        elif ins[0]=='dec':shifted.append((ins[0],ins[1],ins[2]+2,ins[3]+2))
        else:shifted.append((ins[0],ins[1]+2))
    require(cfgs['preload2_18'][2:]==shifted,'NEG18 core CFG binding')
    move=resolve(nodes['node37']);require(move==[('dec',1,3,1),('inc',6,2),('jump',0)],'move macro CFG')
    move_body=symbolic_trace(move,[0,1,2,0]);require(move_body==[T-1,S+1,Y],'move cycle')
    move_summary=[ZERO,S+T,Y]
    require([p.sub(move_body)for p in move_summary]==move_summary,'move summary induction')
    require([p.sub([ZERO,S,Y])for p in move_summary]==[ZERO,S,Y],'move summary base')
    after_move=[p.sub([T,ZERO,ZERO])for p in move_summary];after_move[0]+=1
    require(4*(after_move[2]+pair(after_move[1],after_move[0]))==4*pair(T,P(1)),'move20 clean-store formula')
    p=lambda a,b:(a+b)*(a+b+1)//2+b
    core_cases=0
    for t in range(13):
      for s in range(9):
       for y in range(7):
        rs=[17, t, 19,23,29,31,s,y,37];got,n=run(core,rs);want=list(rs);want[1]=4*(y+p(s,t));want[6]=want[7]=0
        require(got==want,'arbitrary-Y core finite control');m=s+t
        require(n==10*t+13*m*(m+1)//2-2*m+6*y+3,'core transition-count control');core_cases+=1
    neg_cases=0
    for t in range(13):
      for w in range(7):
       rs=[17,t,w,23,29,31,0,0,37];want=list(rs);want[1]=4*p(t,1)
       for name,cfg in cfgs.items():
        got,n=run(cfg,rs);require(got==want,'five-spelling full-frame finite control')
        if name=='preload2_18':require(n==13*t*(t+1)//2+8*t+17,'NEG18 transition-count control')
        neg_cases+=1
    result={'source_sha256':{n:hashlib.sha256((args.source_dir/n).read_bytes()).hexdigest()for n in('Program.lean','Conjugacy.lean','pa196.tm')},
      'symbolic_loop_certificate':symbolic,'independent_cfg_resolvers':{'algorithms':['leaf-path subtree intervals','recursive loop-context stacks'],'reference_source_sites':len(full_cfg),'five_negation_macros_agree':True},'macro_entries':entry_states(nodes,dense_native(args.source_dir)),
      'exact_primitive_cfgs':cfgs,'arbitrary_Y_core_replay_cases':core_cases,'five_spelling_replay_cases':neg_cases,
      'core_transition_count':'10*t + 13*triangle(s+t) - 2*(s+t) + 6*y + 3',
      'neg18_transition_count':'13*triangle(t) + 8*t + 17',
      'scope':'Universal source-core/NEG18 argument via exact CFG plus terminating natural-counter loop invariants checked symbolically. Finite replays are additional controls. Native entry bindings use complete known source prefixes in the upstream table. Physical runtime and blank startup are separate certificates; no sub196 machine is claimed.'}
    result['seed197_source_binding']=candidate_source_binding(nodes,args.source_dir/'seed18_197.grammar.json',args.source_dir/'seed18_197.sites.json',cfgs['preload2_18'])
    args.out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k!='exact_primitive_cfgs'},indent=2))
if __name__=='__main__':main()
