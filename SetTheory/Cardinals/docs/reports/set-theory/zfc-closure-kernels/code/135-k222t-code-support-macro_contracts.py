"""Bind the arithmetic emitter macros to pinned Dag230 by all-register proofs.

These local finite register-program bisimulations quantify over every initial
register value. The inherited ProgLib230 lemmas identify the pinned programs'
arithmetic meaning; this module checks that exactly those programs are used.
"""
from functools import cache
import re,hashlib
import source_language as s
from local_bisimulation import check
from tm_tools import sole

DAG_SHA='7f44c6bc6cb2e5a7a30c1267738c8df7bfd8e036987721ac0bb6bdc326e54eaf'
PROG_SHA='6af4a13b2034b867054f5b74e7635a305172b6a45f58db91dffe63ae57d50dbb'

def sequence(nodes):
    assert nodes
    out=nodes[-1]
    for n in reversed(nodes[:-1]):out=n,out
    return out

def I(x,y):return 'I',x,y
def R(x,y):return 'R',x,y
def Q(x,y):return 'Q',x,y
def E(x,y):return 'E',x,y
def N(x):return I(x,1)
def And(x,y):return N(I(x,N(y)))

def word(expression):
    if expression in ('a','b','c',1):return [{'a':166,'b':121,'c':168,1:177}[expression]]
    op,x,y=expression
    if op=='I' and y==1:return word(x)+[218]
    return word(x)+word(y)+[{'I':119,'Q':180,'R':181,'E':182}[op]]

def execute(tokens):
    top='previous_top';stack=['arbitrary_older_stack']
    for q in tokens:
        if q in (166,121,168,177):stack.append(top);top={166:'a',121:'b',168:'c',177:1}[q]
        elif q==218:top=N(top)
        else:
            assert q in (119,180,181,182) and len(stack)>=2
            top={119:I,180:Q,181:R,182:E}[q](stack.pop(),top)
    assert stack==['arbitrary_older_stack','previous_top']
    return top

def bind(groups,dag_raw,prog_raw):
    assert hashlib.sha256(dag_raw).hexdigest()==DAG_SHA
    assert hashlib.sha256(prog_raw).hexdigest()==PROG_SHA
    dag={int(q):(a,b) for q,a,b in re.findall(r'\| (\d+) => \((E\w+(?: \d+)?), (E\w+(?: \d+)?)\)',dag_raw.decode())}
    @cache
    def expand(q):
        def edge(text):
            if text=='EHalt':return 'CH',None
            kind,arg=text.split();arg=int(arg)
            if kind=='ENode':return expand(arg)
            return {'EInc':'CI','EDecnz':'CD','EBreak':'CB','EContinue':'CC'}[kind],arg
        return tuple(edge(text) for text in dag[q])
    inc=('CI',1);imp=sole(groups,90);neg=sole(groups,184);one=neg[0]
    assert neg==(one,imp)
    macros={166:sole(groups,98),121:sole(groups,12),168:sole(groups,166),177:one,
        119:imp,180:(imp,(inc,inc)),181:(imp,inc),182:(imp,((inc,inc),inc)),218:neg}
    receipts={}
    for q,m in macros.items():
        assert s.boundary(m)==(0,0,False)
        receipts[str(q)]=check(expand(q),m)
    # Independent source graph resolvers also check the compound macro shapes.
    for m in macros.values():
        assert s.graph_arithmetic(s.sites(m))[0]==s.graph_intervals(s.sites(m))
    return macros,receipts

def flat_word(macros,tokens):
    return tuple((op,arg) for q in tokens for p,op,arg in s.sites(macros[q]))
