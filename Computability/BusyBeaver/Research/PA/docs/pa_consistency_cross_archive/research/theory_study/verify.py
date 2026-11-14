#!/usr/bin/env python3
"""Reconstruct and check the new 197-state composition, without search.

Symbolic primitive checking uses inherited arithmetic-engine interfaces.
It is not a new Lean/Rocq proof of the PA consistency biconditional.
"""
from pathlib import Path
import json,hashlib,re,itertools
import construction as C
c=C.c
HERE=Path(__file__).resolve().parent
P=HERE/'direct_negation_diagonal197'
def require(v,msg):
    if not v:raise ValueError(msg)
def table(path):
    r={}
    for ln in path.read_text().splitlines():
        q,b,w,d,n=ln.split();q,b,w,n=map(int,(q,b,w,n))
        require((q,b)not in r and b in(0,1)and w in(0,1)and d in('L','R'),'bad row')
        r[q,b]=w,d=='R',n
    return r
def pin_check():
    pins=json.loads((HERE/'PROVENANCE.json').read_text())
    for name,digest in pins['vendor_sha256'].items():
        require(hashlib.sha256((HERE/name).read_bytes()).hexdigest()==digest,'vendor pin:'+name)
    return len(pins['vendor_sha256'])
def source_binding(t,sites,ins):
    oldsites,oldins=c.program()
    text=(HERE/'vendor/reference/PA196/Source/AXProgram.lean').read_text().split('def program')[0]
    blocks=[(op,int(a),int(b))for op,a,b in re.findall(r'\(\.(\w+), (\d+), (\d+)\)',text)]
    expected={}
    for op,a,b in blocks:expected.setdefault(op,(a,b))
    names={'node49':'push','node55':'copyD','node58':'copyH','node70':'copyA','node65':'cons','node72':'readH','node75':'readDCons','node142':'copyGuard','node150':'compareGuard',C.INC:'incT',C.BREAK:'close'}
    prefix=tuple(map(int,'10101001'))
    oldout=[s for s in oldsites if s[0][:8]!=prefix]
    newout=[s for s in sites if s[0][:8]!=prefix]
    require(oldout==newout and len(oldout)==169,'unchanged exterior')
    def norm(code,start,end,ss):
        if code[0]=='halt':return code
        narg=1 if code[0]=='jump'else 2
        def dest(j):
            if start<=j<end:return('internal',j-start)
            if j==end:return('next',)
            return('external',ss[j][0])
        return tuple(code[:narg])+tuple(dest(j)for j in code[narg:])
    # node65=(node17,node64); node17 has eleven leaves and node64 sixteen.
    acons,bcons=expected['cons'];a64=acons+11
    require(bcons-a64==16,'node64 reference span')
    cursor=50;newcount=0
    for token in C.word(t):
        if token=='N':
            length=18;newcount+=1
            require(ins[cursor]==('inc',7,cursor+1)and ins[cursor+1]==('inc',7,cursor+2),'N prelude')
            for j in range(16):
                require(sites[cursor+j+2][1:]==oldsites[a64+j][1:],'N inherited primitive')
                require(norm(ins[cursor+j+2],cursor,cursor+18,sites)==norm(oldins[a64+j],a64-2,bcons,oldsites),'N inherited graph')
        else:
            a,b=expected[names[token]];length=b-a
            for j in range(length):
                require(sites[cursor+j][1:]==oldsites[a+j][1:],'macro primitive identity')
                require(norm(ins[cursor+j],cursor,cursor+length,sites)==norm(oldins[a+j],a,b,oldsites),'macro graph identity')
        cursor+=length
    require(newcount==8 and cursor-50==len(sites)-169,'complete AX binding')
    oldpaths={p:i for i,(p,op,arg)in enumerate(oldsites)}
    newpaths={p:i for i,(p,op,arg)in enumerate(sites)}
    for p,op,arg in newout:
        ni,oi=newpaths[p],oldpaths[p];nc,oc=ins[ni],oldins[oi]
        narg=1 if nc[0]=='jump'else 2
        require(nc[:narg]==oc[:narg],'exterior opcode')
        if nc[0]=='halt':continue
        for nn,oo in zip(nc[narg:],oc[narg:]):
            if oldsites[oo][0][:8]==prefix:require(nn==oo==50,'AX entry')
            else:require(sites[nn][0]==oldsites[oo][0],'exterior successor')
    return {'macro_items':len(C.word(t)),'new_N_blocks':newcount,'exterior_sites':169,'exact_relative_CFG':True}
def emitter(t):
    Z=('zero',);succ=lambda x:('succ',x);O=succ(Z)
    I=lambda a,b:('im',a,b)
    M=lambda a,b:succ(I(a,b))
    U=lambda a,b:succ(succ(I(b,a)))
    E=lambda a,b:succ(succ(succ(I(a,b))))
    N=lambda a:I(a,O)
    And=lambda a,b:N(I(a,N(b)))
    Ex=lambda a,b:N(U(a,N(b)))
    oldt,A,d,h,Y,X=map(lambda z:('atom',z),['t','a','d','h','y','x'])
    T=oldt;D=d;H=h;stack=[];fields=[Y,X]
    w=C.word(t)
    for op in w[:-3]:
        if op=='node49':stack.append(T);T=Z
        elif op in('node55','node58','node70'):
            stack.append(T);T={'node55':D,'node58':H,'node70':A}[op]
        elif op=='node65':T=I(stack.pop(),T)
        elif op==C.INC:T=succ(T)
        elif op=='node72':H=('add',H,fields.pop(0))
        elif op=='node75':D=('add',D,fields.pop(0));T=I(T,D)
        elif op=='N':T=N(T)
        else:raise ValueError(op)
    heads=[I(Ex(D,U(D,H)),H),I(U(D,U(A,H)),U(A,U(D,H))),I(M(H,D),I(E(H,A),M(A,D))),I(E(H,D),I(M(A,H),M(A,D))),Ex(D,E(H,D)),I(U(D,A),I(U(D,I(A,H)),U(D,H)))]
    rho=I(I(I(H,d),D),I(I(D,H),I(A,H)))
    gamma=I(A,U(A,A));v=I(M(H,D),U(A,M(H,D)))
    point=I(A,M(A,D));sep=U(D,And(I(M(H,D),point),I(M(A,D),A)))
    q=U(A,I(sep,N(point)))
    require(T==N(I(gamma,I(v,q)))and stack==[oldt,U(d,h),rho]+heads,'free algebra AX identity')
    require(w[-3:]==['node142','node150',C.BREAK]and not fields,'guard/field identity')
    return {'constructor_identity':True,'pushed_items':len(stack),'same_diagonal_gate':True}
def startup(rows):
    q=74;head=0;ones=set()
    for k in range(58154):
        w,d,q=rows[q,int(head in ones)]
        (ones.add if w else ones.discard)(head);head+=1 if d else-1
    physical=[0,0,0,0,0,0,2,0,0]+[1]*26
    target={head-1,head};pos=head+48;target.add(pos);pos+=1
    for v in physical:pos+=1;target.update(range(pos,pos+v+1));pos+=v+1
    require((q,head)==(84,-2)and ones==target,'complete startup')
    return {'steps':58154,'head':head,'one_cells':len(ones),'complete_tape':True}
def padding_checks():
    pair=lambda a,b:(a+b)*(a+b+1)//2+b
    I=lambda a,b:4*pair(a,b)
    count=0
    for d,h,a in itertools.product(range(24),repeat=3):
        k=I(d+1,I(h,d+1));p=I(k,a)
        require(p>d and p>h,'fresh padding bound');count+=1
    require(I(I(0,I(0,0)),0)==0,'unshifted zero alias witness')
    imp=lambda a,b:(not a)or b
    for d,h,a in itertools.product([False,True],repeat=3):
        k=imp(d,imp(h,d));require(k and imp(k,a)==a,'K padding truth table')
    return {'numeric_samples':count,'boolean_cases':8,'unshifted_zero_alias':0,'unbounded_proof':'theory_results.tex','calculus_completeness':'not proved'}
def main():
    pins=pin_check();t=c.read_grammar(P/'grammar.json');raw,index,shape=C.build(t)
    chosen=json.loads((P/'folds.json').read_text());rows,alias=C.fold(raw,chosen)
    require(rows==table(P/'machine.native.tm'),'reconstructed table')
    require(len(rows)==394 and len(shape)==68 and len(chosen)==5,'state census')
    C.check_local_folds(raw,rows,alias,chosen)
    labels=json.loads((P/'labels.json').read_text());dense=table(P/'machine.tm')
    require(labels[0]==74 and labels[-1]==254 and len(labels)==198,'dense start/halt')
    require({(labels[q],b):(w,d,labels[n])for(q,b),(w,d,n)in dense.items()}==rows,'dense relabel')
    sites,ins,cs=c.source(t);require(len(sites)==3468,'site count')
    serialized=[[''.join(map(str,p)),{'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}[op],arg]for p,op,arg in sites]
    require(serialized==json.loads((P/'sites.json').read_text()),'serialized source')
    binding=source_binding(t,sites,ins);formulas=emitter(t)
    runtime=c.validate(rows,cs);require(runtime['ok'],'symbolic primitive contracts')
    require(runtime==json.loads((P/'check.json').read_text()),'runtime receipt')
    receipt={'status':'PASS','vendor_pins':pins,'working_states':197,'rows':394,'source_sites':len(sites),'source_binding':binding,'emitter':formulas,'runtime':runtime,'startup':startup(rows),'padding':padding_checks(),'formal_scope':'new executable checks using inherited engine interfaces; no new proof-assistant or PA endpoint'}
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
