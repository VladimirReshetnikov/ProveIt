"""Held actual-TeX compact recipe parser. No imports or execution released.

This module is stdlib-only and performs no top-level I/O. The entry point is
called only by the fully authenticated wrapper. No machine program is run.
"""
from collections import defaultdict
from fractions import Fraction
import re


def need(ok, message):
    if not ok:
        raise ValueError(message)


class RecipeContextError(ValueError):
    pass


def split_top(text, delimiter):
    """Split at a literal delimiter outside all braces and parentheses."""
    out=[];start=0;depth=0;p=0
    while p<len(text):
        if depth==0 and text.startswith(delimiter,p):
            out.append(text[start:p]);p+=len(delimiter);start=p;continue
        if text[p] in '({':depth+=1
        elif text[p] in ')}':
            depth-=1;need(depth>=0,'balanced recipe delimiters')
        p+=1
    need(depth==0,'closed recipe delimiters')
    out.append(text[start:]);return out


def tokens(text):
    commands={r'\mathcal A':'A',r'\mathcal S':'S',r'\nu':'nu',r'\sigma':'sigma',
              r'\tau':'tau',r'\fl':'floor',r'\bmod':'mod',r'\sum':'sum',
              r'\cap':'cap',r'\rg':'range',r'\le':'<=',r'\in':'in'}
    text=text.replace(r'\quad',' ').replace(r'\\',' ').replace('\\ ',' ')
    out=[];p=0
    while p<len(text):
        c=text[p]
        if c.isspace():p+=1;continue
        command=next((s for s in commands if text.startswith(s,p)),None)
        if command is not None:
            out.append(commands[command]);p+=len(command);continue
        if c.isdigit():
            m=re.match(r'\d+',text[p:]);out.append(int(m[0]));p+=len(m[0]);continue
        if c in 'AbqjkwndestahurvNTEFmDF' or c in '+-*/^(){}_,=|<>:':
            out.append(c);p+=1;continue
        raise ValueError('unconsumed actual recipe token '+text[p:])
    return out


def parse(text):
    stream=tokens(text);p=0
    def take(value=None):
        nonlocal p
        need(p<len(stream),'complete actual recipe operand')
        token=stream[p];p+=1
        need(value is None or value==token,'actual recipe delimiter '+str(value))
        return token
    def index():
        take('_');return primary()
    def primary():
        token=take()
        if type(token) is int:return ('n',token)
        if token in ['(','{']:
            node=expression();take(')' if token=='(' else '}');return node
        if token=='floor':
            take('{');node=expression();take('}');return ('floor',node)
        if token=='sum':
            take('_');take('{');name=take();take('=');lo=expression();take('}')
            take('^');hi=primary();return ('sum',name,lo,hi,product())
        if token=='D':
            radix=index();take('(');number=expression();take(',');place=expression();take(')')
            return ('D',radix,number,place)
        if token=='h':
            take('(');q=expression();take(',');b=expression();take(')');return ('h',q,b)
        if token=='r':
            take('_');take('{');d=expression();take(',');q=expression();take('}');return ('r',d,q)
        if token=='|':
            take('S');d=index();take('cap');take('range');lo=primary();hi=primary();take('|')
            return ('count',d,lo,hi)
        if token in ['T','E']:
            sub=index();need(sub==('n',0),'literal decoder zero subscript');return ('v',token+'0')
        if token in ['nu','sigma','tau','u','v','d','m','F','e'] and p<len(stream) and stream[p]=='_':
            return ('arr',token,index())
        need(token in ['A','N','q','b','j','k','w','n','d','e','s','a','t','u','v','r'],
             'supported actual recipe variable '+str(token))
        return ('v',token)
    def powered():
        nonlocal p
        node=primary()
        if p<len(stream) and stream[p]=='^':p+=1;node=('^',node,primary())
        return node
    starts={'(','{','floor','sum','D','h','r','|','T','E','nu','sigma','tau','u','v','d','m','F','e',
            'A','N','q','b','j','k','w','n','s','a','t'}
    def product():
        nonlocal p
        node=powered()
        while p<len(stream):
            token=stream[p]
            if token in ['*','/','mod']:
                p+=1;node=(token,node,powered())
            elif type(token) is int or token in starts:node=('*',node,powered())
            else:break
        return node
    def expression():
        nonlocal p
        node=product()
        while p<len(stream) and stream[p] in ['+','-']:
            op=stream[p];p+=1;node=(op,node,product())
        return node
    result=expression();need(p==len(stream),'complete actual recipe expression consumed');return result


def context(tree, names=(), arrays=(), functions=(), binders=(), label='recipe'):
    """Validate lexical availability before evaluating or collecting an AST."""
    def require(ok,message):
        if not ok:raise RecipeContextError('RECIPE_CONTEXT: '+label+': '+message)
    def visit(node,bound=frozenset()):
        op=node[0]
        if op=='n':require(type(node[1]) is int,'literal integer')
        elif op=='v':require(node[1] in set(names)|bound,'unavailable/free variable '+node[1])
        elif op=='arr':
            require(node[1] in arrays,'unavailable/self array '+node[1]);visit(node[2],bound)
        elif op in ['+','-','*','/','^']:
            visit(node[1],bound);visit(node[2],bound)
        elif op=='sum':
            name=node[1];require(name in binders and name not in set(names)|bound,'unavailable/shadowed sum index '+str(name))
            visit(node[2],bound);visit(node[3],bound);visit(node[4],bound|{name})
        else:
            require(op in functions,'unavailable function '+op)
            for child in node[1:]:visit(child,bound)
    visit(tree);return tree


def pc(c):return {():c} if c else {}
def pa(a,b,sign=1):
    out=dict(a)
    for mon,c in b.items():out[mon]=out.get(mon,0)+sign*c
    return {m:c for m,c in out.items() if c}
def pm(a,b):
    out=defaultdict(int)
    for m,c in a.items():
        for n,d in b.items():out[tuple(sorted(m+n))]+=c*d
    return {m:c for m,c in out.items() if c}
def pp(a,n):
    need(type(n) is int and 0<=n<=5000,'bounded nonnegative fixed polynomial power')
    out=pc(1)
    while n:
        if n%2:out=pm(out,a)
        n//=2
        if n:a=pm(a,a)
    return out


def polynomial(node, special=None):
    op=node[0]
    if op=='n':return pc(node[1])
    if op=='v':return {(node[1],):1}
    if op in ['+','-','*','/','^']:
        a=polynomial(node[1],special);b=polynomial(node[2],special)
        if op=='+':return pa(a,b)
        if op=='-':return pa(a,b,-1)
        if op=='*':return pm(a,b)
        need(set(b)<={()},'constant polynomial divisor/exponent')
        z=b.get((),0)
        if op=='^':return pp(a,z)
        need(z!=0,'nonzero polynomial divisor')
        need(all(c%z==0 for c in a.values()),'integral polynomial division');return {m:c//z for m,c in a.items()}
    need(special is not None,'pure actual polynomial arithmetic')
    return special(node)


def number(node, env, arrays, functions):
    op=node[0]
    if op=='n':return node[1]
    if op=='v':return env[node[1]]
    if op=='arr':
        i=number(node[2],env,arrays,functions)
        need(type(i) is int and i in arrays[node[1]],'defined actual decoder array index '+node[1])
        return arrays[node[1]][i]
    if op in ['+','-','*','/','^','mod']:
        a,b=(number(n,env,arrays,functions) for n in node[1:])
        if op=='+':return a+b
        if op=='-':return a-b
        if op=='*':return a*b
        if op=='/':need(b!=0,'actual nonzero divisor');return Fraction(a,b)
        if op=='mod':need(type(a) is int and type(b) is int and b>0,'actual integer remainder');return a%b
        need(type(b) is int and 0<=b<=5000,'bounded actual fixed power');return a**b
    if op=='floor':
        z=number(node[1],env,arrays,functions);return z.numerator//z.denominator if isinstance(z,Fraction) else z
    if op=='sum':
        lo,hi=(number(n,env,arrays,functions) for n in node[2:4])
        need(type(lo) is int and type(hi) is int and 0<=lo<=hi+1<=1000,'bounded actual finite/empty sum')
        return sum(number(node[4],dict(env,**{node[1]:i}),arrays,functions) for i in range(lo,hi+1))
    args=[number(n,env,arrays,functions) for n in node[1:]]
    if op=='D':
        b,a,k=args;need(all(type(z) is int for z in args) and b>1 and a>=0 and 0<=k<=1000,'actual digit arguments')
        return a//(b**k)%b
    return functions[op](*args)


def one(pattern,text,label):
    matches=list(re.finditer(pattern,text,re.S));need(len(matches)==1,'one complete actual '+label);return matches[0]


def full(pattern,text,label):
    match=re.fullmatch(pattern,text,re.S);need(match is not None,'entire actual '+label);return match


def slots(tex):
    """All replacements below are semantic cuts, never hash-only bypasses."""
    patterns={
        'direction':r'Use the actions \$u_j,v_j,d_j\$ decoded below\. For \$(.*?)\$, let',
        'head':r'h\(q,b\)=(.*?)\.\n\\end\{gathered\}',
        'table':r'\\text\{index \}i&\\text\{tile \}t_i=\(w,n,e,s\)\\\\\\hline\n(.*?)\n\\end\{array\}',
        'payload':r'v\(t\)=(.*?)\.\n\\\]',
        'decoder':r'Put \$D_b\(A,k\)=(.*?)\n\\\]\nEmpty sums are zero\.',
        'positional':r'put \$\\mathcal A=(.*?)\$\.\\par'}
    found={name:one(pattern,tex,name) for name,pattern in patterns.items()}
    return {name:m[1] for name,m in found.items()},found


def normalize(tex, reference):
    actual,found=slots(tex);_,original=slots(reference)
    for name,m in sorted(found.items(),key=lambda item:item[1].start(1),reverse=True):
        tex=tex[:m.start(1)]+original[name][1]+tex[m.end(1):]
    return tex


def assignment(block,lhs):
    parts=split_top(block,'=');need(len(parts)==2 and parts[0].strip()==lhs,'complete actual assignment '+lhs)
    return parse(parts[1])


def enum_domain(text, variables):
    parts=split_top(text,'=');need(len(parts)==2,'entire actual finite enumeration')
    actual=[s.strip() for s in split_top(parts[0],',')]
    if actual!=variables:raise RecipeContextError('RECIPE_CONTEXT: domain: unexpected local binders '+str(actual))
    values=[]
    for raw in split_top(parts[1],','):
        tree=context(parse(raw),label='enumerated finite value')
        value=number(tree,{}, {},{});need(type(value) is int and 0<=value<=1000,'bounded enumerated integer')
        values.append(value)
    need(values and len(values)==len(set(values)),'nonempty distinct finite enumeration');return values


def integer_range(text, name):
    parts=re.split(r'\\le|<',text)
    need(len(parts)==3 and parts[1].strip()==name and text.count(r'\le')==1 and text.count('<')==1,
         'entire actual half-open finite range '+name)
    ends=[number(context(parse(s),label='finite range endpoint'),{}, {},{}) for s in [parts[0],parts[2]]]
    lo,hi=ends;need(all(type(z) is int for z in ends) and 0<=lo<=hi<=1000,'bounded actual finite range')
    return range(lo,hi)


def read_functions(head):
    parts=split_top(head.replace(r'\\','').replace(r'\quad',''),',')
    need(len(parts)==3,'all actual h/set/rank definitions')
    h=context(parse(parts[0]),names={'q','b'},label='h')
    need(polynomial(h)==polynomial(parse('2q+b+2')),'whole head-label polynomial')
    m=full(r'\s*\\mathcal S_d=\\\{(.*?):(.*?),\s*(.*?)\\\}\s*',
           parts[1].replace('\\ ',' '),'direction set comprehension')
    data=context(parse(m[1]),names={'j','d'},arrays={'u','d'},label='S datum')
    cond=split_top(m[2],'=');need(len(cond)==2,'actual set equality predicate')
    pred=[context(parse(s),names={'j','d'},arrays={'u','d'},label='S predicate') for s in cond]
    indices=integer_range(m[3],'j')
    need(list(indices)==list(range(430)),'entire actual430-action set-comprehension domain')
    def set_symbol(node):
        need(node[0]=='arr' and node[1] in ['u','d'] and polynomial(node[2])=={('j',):1},
             'whole actual direction-set array binding')
        return {(node[1].upper(),):1}
    need(polynomial(data,set_symbol)=={('U',):1},'entire actual direction-set datum')
    difference=pa(polynomial(pred[0],set_symbol),polynomial(pred[1],set_symbol),-1)
    standard={('D',):1,('d',):-1}
    need(difference in [standard,{m:-c for m,c in standard.items()}],'full actual direction-set equality predicate')
    rank=assignment(parts[2],r'r_{d,q}')
    context(rank,names={'d','q'},functions={'count'},label='rank')
    def rank_symbol(node):
        need(node[0]=='count' and polynomial(node[1])=={('d',):1} and polynomial(node[2])=={} and
             polynomial(node[3])=={('q',):1,():-1},'actual rank set index and whole interval endpoints')
        return {('C',):1}
    need(polynomial(rank,rank_symbol)=={():205,('d',):-199,('C',):1},'full rank polynomial with independent count')
    return h,data,pred,indices,rank


def read_decoder(block):
    pre,body=block.split(r'\[')
    m=full(r'(.*?)\$, where\n\$a\\bmod b=(.*?)\$\. For \$(.*?)\$, \$(.*?)\$, \$(.*?)\$:\n',pre,'digit/remainder/domain preamble')
    digit=context(parse(m[1]),names={'A','b','k'},functions={'floor','mod'},label='D definition')
    remainder=context(parse(m[2]),names={'a','b'},functions={'floor'},label='remainder definition')
    need(digit==parse(r'\fl{A/b^k}\bmod b') and remainder==parse(r'a-b\fl{a/b}'),'entire ordinary quotient/remainder definitions')
    qs=list(integer_range(m[3],'q'));bs=enum_domain(m[4],['b'])
    jtree=assignment(m[5],'j');context(jtree,names={'q','b'},label='action index')
    need(polynomial(jtree)=={('q',):2,('b',):1},'actual action index polynomial')
    need(body.startswith('\n'+r'\begin{gathered}') and body.endswith('\n'+r'\end{gathered}'), 'complete decoder gathered wrapper')
    body=body[len('\n'+r'\begin{gathered}'):-len('\n'+r'\end{gathered}')]
    body=body.replace(r'\\','').replace(r'\quad','').strip()
    need(body.endswith('.'),'complete decoder terminal punctuation');body=body[:-1]
    fields=split_top(body,',');lhs=['N',r'T_0',r'E_0',r'\nu_j',r'\sigma_j','m_q',r'\tau_q','F_q','u_j','v_j','d_j']
    need(len(fields)==len(lhs),'all eleven actual decoder assignments')
    trees={name:assignment(raw,name) for name,raw in zip(lhs,fields)}
    scopes=[('N',{'A'},set(),{'mod'}),('T_0',{'A'},set(),{'floor','mod'}),('E_0',{'A'},set(),{'floor'}),
            (r'\nu_j',{'N','j'},set(),{'D'}),(r'\sigma_j',{'j'},{'nu'},{'sum'}),
            ('m_q',{'N','q'},set(),{'D'}),(r'\tau_q',{'q'},{'m'},{'sum'}),
            ('F_q',{'E0','q'},{'m','tau'},{'D'}),
            ('u_j',{'T0','j'},{'nu','sigma'},{'D'}),('v_j',{'q','b'},{'F'},{'D'}),('d_j',{'q','b'},{'F'},{'D'})]
    for name,names,arrays,functions in scopes:
        context(trees[name],names,arrays,functions,{'k'} if 'sum' in functions else set(),label=name)
    # These ten complete formulas are unchanged. Compare their consumed,
    # scoped ASTs with the complete ordinary mathematical definitions, not
    # a source hash or a selection of numeric samples. F alone is refactored.
    unchanged={'N':r'\mathcal A\bmod2^{636}',
               'T_0':r'\fl{\mathcal A/2^{636}}\bmod2^{1675}',
               'E_0':r'\fl{\mathcal A/2^{2311}}',
               r'\nu_j':r'D_2(N,j)',r'\sigma_j':r'\sum_{k=0}^{j-1}\nu_k',
               'm_q':r'D_2(N,430+q)',r'\tau_q':r'\sum_{k=0}^{q-1}m_k',
               'u_j':r'\nu_j(1+\sigma_j)+(1-\nu_j)D_{216}(T_0,j-\sigma_j)',
               'v_j':r'D_2(F_q,2b)','d_j':r'D_2(F_q,2b+1)'}
    need(all(trees[name]==parse(rhs) for name,rhs in unchanged.items()),'every complete unchanged decoder mathematical AST')
    def flag_symbol(node):
        if node[0]=='arr':
            need(node[1]=='m' and polynomial(node[2])=={('q',):1},'whole actual flag mask index');return {('M',):1}
        need(node[0]=='D' and polynomial(node[1])=={():16} and node[2]==('v','E0') and
             node[3][0:2]==('arr','tau') and polynomial(node[3][2])=={('q',):1},'whole stored-nibble digit binding')
        return {('Z',):1}
    need(polynomial(trees['F_q'],flag_symbol)=={():14,('M',):-14,('M','Z'):1},'full factored flag polynomial')
    return trees,qs,bs,jtree


def reference_actions(tiles):
    """Invert every complete accepted copy block; no inherited decoder runs."""
    maps={0:{},1:{}}
    for d,lo,hi in [(0,205,250),(1,6,205)]:
        for r in range(lo,hi):
            recovered=[]
            for b in [0,1]:
                i=424+2*r+b;w,n,e,s=tiles[i]
                need((w,n,e)==(d*r,b,(1-d)*r) and (s-b-2)%2==0,'whole parent copy-direction tuple')
                recovered.append((s-b-2)//2)
            need(recovered[0]==recovered[1] and 0<=recovered[0]<=215,'both parent copy rows give one target')
            maps[d][r]=recovered[0]
        need(len(set(maps[d].values()))==hi-lo,'whole target/rank bijection')
    actions=[]
    for j in range(430):
        w,n,e,s=tiles[j+2];q,b=divmod(j,2);need(n==2*q+b+2 and s in [0,1] and (w==0)!=(e==0),'whole parent transition tuple')
        d=int(e>0);r=e if d else w;need(r in maps[d],'parent transition target rank')
        actions.append((maps[d][r],s,d))
    need(actions[0]==(1,1,1),'actual first renamed target');return actions


def decode(trees,qs,bs,jtree,A):
    env={'A':A};arrays={name:{} for name in ['nu','sigma','m','tau','F','u','v','d']}
    for name,variable in [('N','N'),('T_0','T0'),('E_0','E0')]:env[variable]=number(trees[name],env,arrays,{})
    pairs=[]
    for q in qs:
        for b in bs:
            j=number(jtree,{'q':q,'b':b},arrays,{})
            need(type(j) is int and 0<=j<430,'actual430-action index range');pairs.append((j,q,b))
    need(len(pairs)==430 and {j for j,q,b in pairs}==set(range(430)),'actual domain covers each action once')
    for j,q,b in sorted(pairs):
        local=dict(env,j=j,q=q,b=b)
        arrays['nu'][j]=number(trees[r'\nu_j'],local,arrays,{})
        arrays['sigma'][j]=number(trees[r'\sigma_j'],local,arrays,{})
    for q in qs:
        local=dict(env,q=q)
        arrays['m'][q]=number(trees['m_q'],local,arrays,{})
        arrays['tau'][q]=number(trees[r'\tau_q'],local,arrays,{})
        arrays['F'][q]=number(trees['F_q'],local,arrays,{})
    for j,q,b in sorted(pairs):
        local=dict(env,j=j,q=q,b=b)
        for name in ['u','v','d']:arrays[name][j]=number(trees[name+'_j'],local,arrays,{})
    actions=[tuple(arrays[name][j] for name in ['u','v','d']) for j in range(430)]
    need(all(type(u) is int and 0<=u<=215 and v in [0,1] and d in [0,1] for u,v,d in actions),'all430 actual action labels')
    return arrays,actions,pairs


def tuple_trees(text,names):
    text=text.replace('\\ ',' ').strip()
    need(text.startswith('(') and text.endswith(')'),'whole actual ordered tile tuple')
    parts=split_top(text[1:-1],',');need(len(parts)==4,'all four ordered actual tile coordinates')
    return [context(parse(s),names,{'u','v','d'},{'h','r'},label='tile coordinate') for s in parts]


def table_rows(text,arrays,pairs,functions,sets):
    rows=split_top(text,r'\\');need(len(rows)==10,'all ten actual complete tile rows')
    output={}
    def add(index,tuple_ast,env):
        i=number(index,env,arrays,functions);t=[number(n,env,arrays,functions) for n in tuple_ast]
        need(type(i) is int and 0<=i<943 and i not in output,'actual tile indices exactly once')
        need(all(type(z) is int and 0<=z<=438 for z in t),'all actual ordered tile labels');output[i]=t
    for row_number,row in enumerate(rows):
        sides=split_top(row.strip(),'&');need(len(sides)==2,'entire actual tile row/index/domain')
        left,right=(s.strip() for s in sides)
        if row_number==0:
            indices=split_top(left,',');tuples=split_top(right,',')
            need(len(indices)==len(tuples)==2,'both literal initial tiles')
            for i,t in zip(indices,tuples):add(context(parse(i),label='literal tile index'),tuple_trees(t,set()),{})
            continue
        if row_number==3:
            m=full(r'\\substack\{(.*?)\\\\q\\in\\mathcal S_d,\s*d,b=(.*?)\}',
                   left.replace('\\ ',' '),'copy index and domain')
            index=context(parse(m[1]),{'d','q','b'},functions={'r'},label='copy index')
            values=enum_domain('d,b='+m[2],['d','b']);coord=tuple_trees(right,{'d','q','b'})
            for d in values:
                need(d in sets,'actual direction set index')
                for b in values:
                    for q in sorted(sets[d]):add(index,coord,{'d':d,'b':b,'q':q})
            continue
        domain=None
        if r'\ (' in left:
            raw,domain=left.split(r'\ (',1);need(domain.endswith(')'),'complete actual tile domain');domain=domain[:-1]
        else:raw=left
        names={1:{'j','q','b'},2:{'a','b'},4:{'a','b'},8:{'t'},9:{'a','b'}}.get(row_number,set())
        index=context(parse(raw),names,functions={'r'},label='tile index')
        coord=tuple_trees(right,names)
        if row_number==1:
            need(domain is not None,'actual transition domain')
            p=split_top(domain,'=');need(len(p)==2 and p[0].strip()=='j','actual transition index binding')
            p=split_top(p[1],'<');need(len(p)==2,'complete actual transition upper bound')
            expr=context(parse(p[0]),{'q','b'},label='transition index binding')
            high=number(context(parse(p[1]),label='transition bound'),{}, {},{})
            for j,q,b in pairs:
                local={'j':number(expr,{'q':q,'b':b},arrays,functions),'q':q,'b':b}
                if local['j']<high:add(index,coord,local)
        elif row_number in [2,4,9]:
            need(domain is not None,'actual two-parameter tile domain');values=enum_domain(domain,['a','b'])
            for a in values:
                for b in values:add(index,coord,{'a':a,'b':b})
        elif row_number==8:
            need(domain is not None,'actual tail domain')
            for t in enum_domain(domain,['t']):add(index,coord,{'t':t})
        else:
            need(domain is None,'no unconsumed literal tile domain');add(index,coord,{})
    need(set(output)==set(range(943)),'all943 actual indexed tiles');return [output[i] for i in range(943)]


def audit(tex,reference,tiles,seed,alphabet):
    raw,_=slots(tex);directions=enum_domain(raw['direction'],['d'])
    need(set(directions)=={0,1},'complete actual binary direction-parameter domain')
    h,data,pred,indices,rank=read_functions(raw['head'])
    payload=context(parse(raw['payload']),{'w','n','e','s'},label='complemented payload')
    expected=polynomial(parse('2^{34}-w-2^8n-2^{17}e-2^{25}s'))
    actual=polynomial(payload);need(actual==expected,'entire complemented payload polynomial in four independent coordinates')
    old=polynomial(parse('w+2^8n+2^{17}e+2^{25}s+127*2^{34}'))
    need(pa(actual,old)==pc(1<<41),'full independent payload relation v_new=2^41-v_old')
    trees,qs,bs,jtree=read_decoder(raw['decoder'])
    positional=context(parse(raw['positional']),arrays={'e'},functions={'sum'},binders={'j'},label='positional integer')
    need(positional[0]=='sum' and positional[1]=='j' and positional[2]==('n',0) and positional[3]==('n',435),'entire436 positional sum bounds')
    independent={}
    for j in range(436):
        def digit_symbol(node):
            need(node[0:2]==('arr','e') and number(node[2],{'j':j},{},{})==j,'whole actual positional digit index')
            return {('digit'+str(j),):1}
        # Substitute the bound index before polynomial collection, preserving each digit.
        def substitute(node):
            if node==('v','j'):return ('n',j)
            return tuple([node[0]]+[substitute(v) if isinstance(v,tuple) else v for v in node[1:]])
        term=polynomial(substitute(positional[4]),digit_symbol)
        independent=pa(independent,term)
    need(independent=={('digit'+str(j),):62**(435-j) for j in range(436)},'all436 independent literal positional coefficients')
    literal=one(r'\\begingroup\\fontsize\{7\.7\}\{8\.2\}\\selectfont\\ttfamily\n(.*?)\\endgroup',tex,'actual literal seed block')[1]
    literal=re.sub(r'\\par|\s','',literal)
    actual_alphabet=one(r'\{\\fontsize\{7\.7\}\{8\.2\}\\selectfont\\ttfamily (.*?)\}\.\\par',tex,'actual ordered alphabet')[1]
    need(literal==seed and actual_alphabet==alphabet and len(seed)==436 and len(alphabet)==62,'whole actual fixed literal seed/alphabet')
    digit_arrays={'e':{j:alphabet.index(c) for j,c in enumerate(seed)}}
    A=number(positional,{},digit_arrays,{})
    arrays,actions,pairs=decode(trees,qs,bs,jtree,A)
    need(actions==reference_actions(tiles),'all430 actual decoded actions equal complete accepted transition/copy inverse')
    sets={}
    for d in directions:
        sets[d]={number(data,{'j':j,'d':d},arrays,{}) for j in indices
                 if number(pred[0],{'j':j,'d':d},arrays,{})==number(pred[1],{'j':j,'d':d},arrays,{})}
    def count(d,lo,hi):
        need(d in sets and all(type(z) is int for z in [lo,hi]),'actual finite rank count arguments')
        return sum(lo<=q<=hi for q in sets[d])
    functions={'h':lambda q,b:number(h,{'q':q,'b':b},arrays,{}),
               'r':lambda d,q:number(rank,{'d':d,'q':q},arrays,{'count':count})}
    actual_tiles=table_rows(raw['table'],arrays,pairs,functions,sets)
    need(actual_tiles==tiles,'every one of943 complete actual tuples at its accepted index')
    for t in actual_tiles:
        env=dict(zip(['w','n','e','s'],t));z=number(payload,env,arrays,{})
        need(z==(1<<41)-(t[0]+(t[1]<<8)+(t[2]<<17)+(t[3]<<25)+(127<<34)),'whole actual complemented payload at every tile')
    normalized=normalize(tex,reference)
    return normalized,{'all_actual_fields_fully_parsed':True,'strict_lexical_contexts_before_evaluation':True,
        'payload_identity_four_independent_coordinates':True,'payload_complement_constant':1<<41,
        'all436_positional_coefficients':True,'all430_actions_from_complete_parent_copy_inverse':True,
        'actual_direction_set_sizes':{str(d):len(s) for d,s in sets.items()},'all943_tuples_pointwise_identical':True,
        'all_ten_rows_and_actual_domains_checked':True,'actual_flags_full_polynomial_identity':True}
