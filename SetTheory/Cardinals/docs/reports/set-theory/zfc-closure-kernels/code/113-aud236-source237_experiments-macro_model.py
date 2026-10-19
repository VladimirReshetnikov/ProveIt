"""Pure AX stack-expression model, extracted from ProveIt's attributed
theory_backend_experiment.py. Register implementation is supplied separately
by the exact current-source macro-word comparison in price_ksp.py.
"""
TAIL=[192,131,211,197,131]
def Imp(a,b):return ('imp',a,b)
def Rel(a,b):return ('rel',a,b)
def Eq(a,b):return ('eq',a,b)
def All(a,b):return ('all',a,b)
def Not(a):return Imp(a,1)
def And(a,b):return Not(Imp(a,Not(b)))
def Ex(a,b):return Not(All(a,Not(b)))

def symbolic(program,initial_b='h'):
    stack,b,u,events=['old_top'],initial_b,None,[]
    constructors={119:Imp,181:Rel,182:Eq,180:All,178:And,183:Ex}
    for m in program:
        if m in (166,121,168,171,177):stack.append({166:'a',121:b,168:'c',171:0,177:1}[m])
        elif m in constructors:
            right,left=stack.pop(),stack.pop();stack.append(constructors[m](left,right))
        elif m==218:stack[-1]=Not(stack[-1])
        elif m==176:events.append(('read_b',len(stack)));b='b'
        elif m==158:u='u'
        elif m==208:
            assert stack[-1]==0 and u=='u'
            stack[-1],u=u,None
        elif m in TAIL:events.append((m,len(stack)))
        else:raise ValueError(m)
    return stack,events

def emit(f):
    if f=='a':return [166]
    if f=='b':return [121]
    if f=='c':return [168]
    if f=='u':return [171,158,208]
    if f==0:return [171]
    if f==1:return [177]
    if isinstance(f,tuple)and f[0]=='imp'and f[2]==1:
        inner=f[1]
        if isinstance(inner,tuple)and inner[0]in ('imp','all')and isinstance(inner[2],tuple)and inner[2][0]=='imp'and inner[2][2]==1:
            return emit(inner[1])+emit(inner[2][1])+[178 if inner[0]=='imp'else 183]
        return emit(inner)+[218]
    op,a,b=f
    return emit(a)+emit(b)+[{'imp':119,'rel':181,'eq':182,'all':180}[op]]
