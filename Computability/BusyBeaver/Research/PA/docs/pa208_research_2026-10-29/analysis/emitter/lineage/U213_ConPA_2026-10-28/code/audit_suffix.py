#!/usr/bin/env python3
"""Bind the U213 interior AX suffix to all-natural arithmetic macro lemmas.

Standard-library-only finite audit. It checks source/control identities and
symbolic constructor expressions, not finite samples of arithmetic contracts.
Those contracts are the named ProgLibPerm.v lemmas retained from the parent.
The ordinary proof in startup_suffix.tex supplies their mathematical use.
"""
from pathlib import Path
import argparse, hashlib, json, re

SOURCE_SHA = '7b6539dc67b66ff73f22554018d7af5985d85574460a73fea5f025103c523d00'
DAG_SHA = 'ba2b28487ae978bd27b0d804e9b2bde6d9adcd1dd575de55572465c050b86aa1'
LEMMAS = {119:'cons119',121:'par121',166:'par166',168:'par168',
          175:'read175',176:'read176',180:'wal180',181:'wel181',182:'weq182',
          183:'wex183',218:'wn218',192:'w192',131:'ifeq131',211:'w211',197:'w197'}
CONSTRUCTORS = (166,121,168,119,180,181,182,218,183,175,176)

def need(p, message):
    if not p:
        raise ValueError(message)

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def cfg(rows):
    """Resolve primitive source addresses by ancestor interval boundaries."""
    bounds = {}
    for i,(p,op,arg) in enumerate(rows):
        for j in range(len(p)+1):
            q=p[:j]
            if q not in bounds: bounds[q]=[i,i+1]
            else: bounds[q][1]=i+1
    result=[]
    for i,(p,op,arg) in enumerate(rows):
        if op=='CI': dest=(i+1,)
        elif op=='CH': dest=()
        else:
            bit='1' if op=='CC' else '0'
            level=1 if op=='CD' else arg
            positions=[j for j,b in enumerate(p) if b==bit]
            need(level<=len(positions),('escaping branch',i,p,op,arg))
            ancestor=p[:positions[-level]]
            target=bounds[ancestor][0 if op=='CC' else 1]
            dest=(target,i+1) if op=='CD' else (target,)
        result.append((op,arg,dest))
    return result

def unfold_dag(raw):
    edge=r'(?:ENode|EInc|EDecnz|EBreak|EContinue)\s+\d+|EHalt'
    pattern=r'^\s*\|\s*(\d+)\s*=>\s*\(('+edge+r'),\s*('+edge+r')\)\s*$'
    nodes={int(i):(a,b) for i,a,b in re.findall(pattern,raw.decode(),re.M)}
    need(len(nodes)==487,'wrong DAG node count')
    def unfold(e,p='',anc=frozenset()):
        x=e.split();kind=x[0]
        if kind=='ENode':
            n=int(x[1]);need(n in nodes and n not in anc,'missing or cyclic DAG node')
            a,b=nodes[n]
            return unfold(a,p+'0',anc|{n})+unfold(b,p+'1',anc|{n})
        op={'EInc':'CI','EDecnz':'CD','EBreak':'CB','EContinue':'CC','EHalt':'CH'}[kind]
        return [[p,op,None if kind=='EHalt' else int(x[1])]]
    return {n:cfg(unfold('ENode '+str(n))) for n in LEMMAS}

def binding(whole,proof,lo):
    actual=[(o,a,tuple(t-lo for t in ds)) for o,a,ds in whole[lo:lo+len(proof)]]
    if len(actual)!=len(proof): return None
    if [x[2] for x in actual]!=[x[2] for x in proof]: return None
    if any(not 0<=q<=len(proof) for _,_,ds in actual for q in ds): return None
    edits=[];i=0
    while i<len(proof):
        o,a,ds=actual[i];po,pa,pds=proof[i]
        if (o,a,ds)==(po,pa,pds): i+=1;continue
        if o==po and o in ('CB','CC'):
            edits.append({'kind':'identical resolved jump','site':i,'source_depth':a,'proof_depth':pa})
            i+=1;continue
        if o==po=='CI' and i+1<len(proof):
            o2,a2,ds2=actual[i+1];po2,pa2,pds2=proof[i+1]
            if not (o2==po2=='CI' and a==pa2 and a2==pa): return None
            if not (ds==(i+1,) and ds2==(i+2,)): return None
            if any(i+1 in dst for j,(_,_,dst) in enumerate(actual) if j!=i): return None
            if any(lo+i+1 in dst for j,(_,_,dst) in enumerate(whole) if j!=lo+i): return None
            edits.append({'kind':'commuting consecutive increments','sites':[i,i+1],
                          'source_registers':[a,a2],'proof_registers':[pa,pa2]})
            i+=2;continue
        return None
    return edits

def audit(source,dag):
    raw=source.read_bytes();dagraw=dag.read_bytes()
    need(digest(raw)==SOURCE_SHA,'unexpected source bytes')
    need(digest(dagraw)==DAG_SHA,'unexpected arithmetic DAG bytes')
    rows=json.loads(raw);whole=cfg(rows);macros=unfold_dag(dagraw)
    calls=[];p=106
    while p<3732:
        matches=[]
        for n in CONSTRUCTORS:
            edits=binding(whole,macros[n],p)
            if edits is not None:matches.append((n,edits))
        need(matches,('unbound construction macro at',p))
        n,edits=max(matches,key=lambda x:len(macros[x[0]]))
        calls.append({'start':p,'stop':p+len(macros[n]),'dag_node':n,
                      'lemma':'ProgLibPerm.'+LEMMAS[n],'normalizations':edits})
        p+=len(macros[n])
    need(p==3732,'wrong end of constructor sequence')
    gate=[]
    for lo,n in [(3732,192),(3736,131),(3748,211),(3751,197),(3754,131)]:
        edits=binding(whole,macros[n],lo)
        need(edits is not None,('unbound gate macro',lo,n))
        gate.append({'start':lo,'stop':lo+len(macros[n]),'dag_node':n,
                     'lemma':'ProgLibPerm.'+LEMMAS[n],'normalizations':edits})
    need([x['stop'] for x in gate]==[3736,3748,3751,3754,3766],'gate partition')
    need(whole[3766]==('CB',1,(3873,)),'AX return differs')
    need(whole[3873]==('CC',3,(0,)),'scheduler return differs')
    I=lambda x,y:('I',x,y);Q=lambda x,y:('Q',x,y)
    R=lambda x,y:('R',x,y);E=lambda x,y:('E',x,y)
    neg=lambda x:I(x,1);ex=lambda x,y:neg(Q(x,neg(y)))
    top='z';stack=[];a='u';b='h';c='c';pointer='P(y,P(x,l))'
    snapshots=[];min_depth=0
    for call in calls:
        n=call['dag_node']
        if n in (166,121,168):
            stack.insert(0,top);top={166:a,121:b,168:c}[n]
        elif n in (119,180,181,182,183):
            need(stack,('opaque tail popped',call['start']))
            head=stack.pop(0);top={119:I,180:Q,181:R,182:E,183:ex}[n](head,top)
        elif n==218:top=neg(top)
        elif n==176:
            need(pointer=='P(y,P(x,l))','wrong first field read');b='b';pointer='P(x,l)'
        elif n==175:
            need(pointer=='P(x,l)','wrong second field read');a='a';pointer='l'
        else:raise ValueError(n)
        min_depth=min(min_depth,len(stack))
        if call['stop'] in (158,172,199,213,478,887,1170,1466,1765,2061,2411,2642,2884,3658,3732):
            snapshots.append({'ordinal':call['stop'],'top':top,'stack':list(stack),
                              'A':'c','D':a,'H':b,'L':pointer,'N':'n','X':0,'Y':0})
    a,b,c,u='a','b','c','u'
    r1=ex(a,E(a,b))
    r2=I(Q(a,I(b,c)),I(Q(a,b),Q(a,c)))
    r3=I(E(a,b),I(R(c,a),R(c,b)))
    r4=I(Q(a,Q(b,c)),Q(b,Q(a,c)))
    r5=I(E(c,a),I(R(c,b),R(a,b)))
    r6=I(ex(a,Q(a,c)),c)
    r7=I(E(c,a),I(E(c,b),Q(R(a,b),E(a,b))))
    dominated=I(I(I(c,u),a),I(I(a,c),I(b,c)))
    e=R(c,a);g=Q(a,I(R(a,c),R(a,b)))
    uc=Q(c,I(e,a));lc=Q(c,I(a,I(g,e)));hc=Q(a,I(uc,I(lc,1)))
    v=I(R(a,b),Q(c,R(a,b)));bundle=neg(I(v,hc))
    need(stack==[r1,r2,r3,r4,r5,r6,r7,dominated,'z'],'nine-head symbolic stack mismatch')
    need(top==bundle,'role-a bundle mismatch')
    need(pointer=='l','wrong final pointer')
    nwrites=[i for i in range(106,3766) if rows[i][1] in ('CI','CD') and rows[i][2]==0]
    lwrites=[i for i in range(106,3766) if rows[i][1] in ('CI','CD') and rows[i][2]==8]
    need(nwrites==[] and lwrites==[158,167,199,208],'scheduler register access mismatch')
    return {'status':'AX_SUFFIX_UNIVERSAL_MACRO_BINDING_AND_SYMBOLIC_STACK_PASS',
            'source_sha256':digest(raw),'dag_sha256':digest(dagraw),
            'source_interval':[106,3766],'constructor_macro_calls':len(calls),
            'constructor_calls':calls,'gate_calls':gate,'symbolic_snapshots':snapshots,
            'generic_input':{'N':'n','T':'z','W':'J','A':'c','D':'u','H':'h','X':0,'Y':0,'L':'P(y,P(x,l))'},
            'generic_parameters':{'a':'u+x','b':'h+y','dominance':'u<=a'},
            'generic_output':{'N':'n','T':'0 if c=a or c=b, otherwise B*(a,b,c)',
                              'W':'[r1(a,b,c),...,r7(a,b,c),Ldom(a,b,c,u),z;J]',
                              'A':0,'D':0,'H':0,'X':0,'Y':0,'L':'l'},
            'symbolic_stack':stack,'symbolic_top_before_gate':top,
            'minimum_explicit_temporary_stack_depth':min_depth,'opaque_tail_never_popped':True,
            'writes_N':nwrites,'writes_L':lwrites,
            'actual_seed':{'ordinal':106,'registers':[1,0,4,0,0,1,0,0,1]},
            'actual_parameters':{'u':0,'h':1,'x':0,'y':1,'a':0,'b':2,'c':0,'z':0,'J':4,'l':0},
            'actual_root':{'ordinal':0,'N':1,'T':0,'W':'[r1(0,2,0),...,r7(0,2,0),Ldom(0,2,0,0),0;4]',
                           'A':0,'D':0,'H':0,'X':0,'Y':0,'L':0,
                           'explicit_theorem_heads':9,'required_protected_credit':2,'permanent_margin':7},
            'scope':'Finite source/DAG binding and symbolic expression audit. All-natural termination/effects follow from the named inherited arithmetic lemmas and their ordinary natural-induction proofs. The literal binary bootstrap, runtime, and U/PA calibration are separate checks; no new kernel endpoint is claimed.'}

if __name__=='__main__':
    root=Path(__file__).resolve().parent.parent
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,default=root/'machine/sites.json')
    p.add_argument('--dag',type=Path,default=root/'inputs/DagPerm.v')
    p.add_argument('--output',type=Path,default=root/'evidence/suffix.json')
    a=p.parse_args();r=audit(a.source,a.dag)
    a.output.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps({k:r[k] for k in ('status','source_sha256','constructor_macro_calls','writes_N','writes_L','actual_parameters','actual_root')},indent=2))
