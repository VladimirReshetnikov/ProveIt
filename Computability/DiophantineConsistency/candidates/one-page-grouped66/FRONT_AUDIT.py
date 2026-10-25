#!/usr/bin/env python3
"""CODE/TEX ONLY/HOLD: actual grouped-native expressions and whole P66 audit."""
import argparse
from collections import defaultdict
from fractions import Fraction
import gzip
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
PAGE = ROOT/'candidates/one-page-grouped66'
PARENT = ROOT/'candidates/one-page-fifteen66'
INDEXED = ROOT/'research/indexed-tile-enumeration'
MARKER = r'\textbf{The four fixed integers.}'
SEALS = {'candidates/one-page-fifteen66':'065a396f78fb271b1b82cadd2d61b9a79f774cd82739d41946b1a9fcf8384424',
         'research/grouped-fixed-coefficient-recipe':'f5ae707993e3041a6d35f4144e0baade3cfa45fd3d4f5875c825771fad1a9594',
         'research/indexed-tile-enumeration':'e077a476c38cb9abd96217887d16b011f6f5e16847036702720d69fcf91b1f84'}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True)+'\n').encode()


def load(path):
    return json.loads(path.read_bytes())


def authenticate():
    pins = load(PAGE/'SOURCE_PINS.json')
    for group in ['external_files','own_core']:
        for name,pin in pins[group].items():
            path = ROOT/name
            raw = path.read_bytes()
            need(not path.is_symlink() and {'bytes':len(raw),'sha256':digest(raw)}==pin, 'reviewed whole input '+name)
    need({p['folder']:p['manifest_sha256'] for p in pins['closed_dependencies']}==SEALS, 'three exact whole contracts')
    for name,seal in SEALS.items():
        folder = ROOT/name
        raw = (folder/'MANIFEST.json').read_bytes()
        need(digest(raw)==seal, 'whole calibrated seal')
        entries = json.loads(raw)['files']
        actual = {p.relative_to(folder).as_posix() for p in folder.rglob('*') if p.is_file() and p!=folder/'MANIFEST.json'}
        need(actual==set(entries), 'complete whole calibrated inventory')
        for relative,pin in entries.items():
            path = folder/relative
            data = path.read_bytes()
            expected = {'bytes':len(data),'sha256':digest(data)} if isinstance(pin,dict) else digest(data)
            need(not path.is_symlink() and pin==expected, 'whole calibrated member '+relative)
    return pins


def adopted_front():
    # This sole nonstdlib import happens only after complete authentication.
    path = PARENT/'FRONT_AUDIT.py'
    spec = importlib.util.spec_from_file_location('reviewed_complete_p66_front', path)
    need(spec is not None and spec.loader is not None, 'exact accepted front module')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.PAGE = PAGE
    module.PRESERVED = PARENT
    module.INDEXED = INDEXED
    return module


# Laurent polynomials in one argument, with all943 independent payload symbols.
# Keys are (argument exponent, sorted tuple of symbolic tile indices).
def const(n):
    return {(0,()):n} if n else {}


def add(a,b,sign=1):
    out = dict(a)
    for mon,c in b.items():
        out[mon] = out.get(mon,0)+sign*c
    return {m:c for m,c in out.items() if c}


def mul(a,b):
    out = defaultdict(int)
    for (e,v),c in a.items():
        for (f,w),d in b.items():
            out[(e+f,tuple(sorted(v+w)))] += c*d
    return {m:c for m,c in out.items() if c}


def power(a,n):
    need(type(n) is int and abs(n)<=10000, 'bounded fixed integer exponent')
    if n<0:
        need(len(a)==1, 'Laurent inverse must be a unit monomial')
        (e,v),c = next(iter(a.items()))
        need(not v and c in [-1,1], 'integral Laurent inverse')
        return {(e*n,()):c**(-n)}
    out = const(1)
    while n:
        if n%2:
            out = mul(out,a)
        n//=2
        if n:
            a = mul(a,a)
    return out


def lexer(text):
    for token in [r'\qquad',r'\quad',r'\\','&']:
        text = text.replace(token,' ')
    commands = {r'\rho':'rho',r'\beta':'beta',r'\Lambda':'Lambda',r'\Phi':'Phi',r'\sum':'sum',r'\fl':'floor'}
    out,p = [],0
    while p<len(text):
        c = text[p]
        if c.isspace():
            p+=1
        elif text.startswith('v(t_i)',p):
            out.append('payload');p+=len('v(t_i)')
        elif c.isdigit():
            m = re.match(r'\d+',text[p:]);out.append(int(m[0]));p+=len(m[0])
        elif c in '+-*/^(){}_,=':
            out.append(c);p+=1
        elif c in 'xieBGD':
            out.append(c);p+=1
        else:
            command = next((s for s in commands if text.startswith(s,p)),None)
            need(command is not None, 'entire native TeX token '+text[p:])
            out.append(commands[command]);p+=len(command)
    return out


def parse(text):
    stream,p = lexer(text),0
    def take(token=None):
        nonlocal p
        need(p<len(stream), 'complete native operand')
        v=stream[p];p+=1
        need(token is None or v==token, 'native expected delimiter '+str(token))
        return v
    def primary():
        token = take()
        if type(token) is int:
            return ('n',token)
        if token in ['rho','beta','Lambda','x','i','e','B']:
            return ('v',token)
        if token=='payload':
            return ('payload',)
        if token in ['(','{']:
            result=expression();take(')' if token=='(' else '}');return result
        if token=='floor':
            take('{');result=expression();take('}');return ('floor',result)
        if token=='Phi':
            take('(');result=expression();take(')');return ('Phi',result)
        if token=='G':
            take('_');length=primary();take('(');arg=expression();take(')');return ('G',length,arg)
        if token=='D':
            take('_');base=primary();take('(');number=expression();take(',');index=expression();take(')')
            return ('D',base,number,index)
        if token=='sum':
            take('_');take('{');index=take();need(index in ['i','e'],'fixed native sum index')
            take('=');low=take();take('}');take('^');high=primary()
            need(type(low) is int,'fixed lower sum bound')
            return ('sum',index,low,high,product())
        raise ValueError('unsupported native primary '+str(token))
    def powered():
        nonlocal p
        value=primary()
        if p<len(stream) and stream[p]=='^':
            p+=1;value=('^',value,primary())
        return value
    def product():
        nonlocal p
        value=powered()
        while p<len(stream):
            token=stream[p]
            if token in ['*','/']:
                p+=1;value=(token,value,powered())
            elif type(token) is int or token in ['rho','beta','Lambda','x','i','e','B','payload','G','D','Phi','floor','sum','(','{']:
                value=('*',value,powered())
            else:
                break
        return value
    def expression():
        nonlocal p
        value=product()
        while p<len(stream) and stream[p] in ['+','-']:
            op=stream[p];p+=1;value=(op,value,product())
        return value
    result=expression();need(p==len(stream),'all native expression consumed');return result


def native_slots(body):
    patterns = {'Lambda':r'\\Lambda=(.*?)\.\n\\end\{gathered\}',
                'MC':r'M_C=\{\}&(.*?)\\\\\nM_F=',
                'MF':r'M_F=\{\}&(.*?)\\\\\nK=',
                'K':r'K=\{\}&(.*?),\n\\end\{align\*\}',
                'Phi':r'\\Phi\(x\)=\{\}&(.*?)\.\n\\end\{split\}'}
    slots={};masked=body
    for name,pattern in patterns.items():
        matches=list(re.finditer(pattern,body,re.S));need(len(matches)==1,'unique complete native slot '+name)
        m=matches[0];rhs=m[1]
        if name in ['MC','MF']:
            need(rhs.rstrip().endswith(','),'complete native assignment punctuation')
            rhs=rhs.rstrip()[:-1]
        slots[name]=rhs
    for name,pattern in patterns.items():
        masked=re.sub(pattern,lambda m,name=name:m[0][:m.start(1)-m.start(0)]+'<'+name+'>'+m[0][m.end(1)-m.start(0):],masked,flags=re.S)
    return slots,masked


class NativeContextError(ValueError):
    """An actual printed expression violates its definition or lexical scope."""


def native_contexts(trees):
    # Distinct printed variables are never identified until these checks prove
    # the appropriate one-variable context. In particular x is local to Phi;
    # rho is unavailable there, and x is unavailable in every integer definition.
    contexts = {
        'Phi':({'x'},{'G','sum'},{'i'}),
        'Lambda':({'rho'},set(),set()),
        'MC':({'rho','B','beta'},{'Phi','D','floor','sum'},{'e'}),
        'MF':({'rho','B','beta','Lambda'},{'G'},set()),
        'K':({'rho','B','beta','Lambda'},{'Phi','G'},set())}
    order=['Phi','Lambda','MC','MF','K']
    need(set(trees)==set(order),'five complete native definitions')
    established={'rho','B','beta'}
    records={}
    for slot in order:
        globals_allowed,functions_allowed,indices_allowed=contexts[slot]
        actual_globals,dependencies,indices=set(),set(),set()
        def require(ok, message):
            if not ok:
                raise NativeContextError('NATIVE_CONTEXT: '+slot+': '+message)
        def fixed(node,bound):
            # Powers and finite bounds may use only literal arithmetic and
            # lexically bound finite indices, never x,rho or another global.
            op=node[0]
            if op=='n':
                require(type(node[1]) is int,'literal fixed integer')
            elif op=='v':
                require(node[1] in bound,'unbound/global name in fixed exponent or bound '+node[1])
            else:
                require(op in ['+','-','*','/','^'],'nonarithmetic fixed exponent or bound '+op)
                fixed(node[1],bound);fixed(node[2],bound)
        def visit(node,bound=frozenset()):
            op=node[0]
            if op=='n':
                require(type(node[1]) is int,'literal integer')
            elif op=='v':
                name=node[1]
                if name not in bound:
                    require(name in globals_allowed,'unbound or unavailable variable '+name)
                    actual_globals.add(name)
                    if name!='x':
                        require(name in established,'definition used before proof '+name)
                        dependencies.add(name)
            elif op=='payload':
                require(slot=='Phi' and 'i' in bound,'payload requires the lexical Phi sum index i')
            elif op in ['+','-','*','/']:
                visit(node[1],bound);visit(node[2],bound)
            elif op=='^':
                visit(node[1],bound);fixed(node[2],bound)
            else:
                require(op in functions_allowed,'unavailable function '+op)
                if op=='G':
                    fixed(node[1],bound);visit(node[2],bound)
                elif op=='sum':
                    index=node[1]
                    require(index in indices_allowed and index not in bound,'unavailable or shadowed sum index '+index)
                    require(type(node[2]) is int,'literal lower finite bound')
                    fixed(node[3],bound)
                    indices.add(index)
                    visit(node[4],bound|{index})
                elif op=='floor':
                    visit(node[1],bound)
                elif op=='D':
                    visit(node[1],bound);visit(node[2],bound);fixed(node[3],bound)
                elif op=='Phi':
                    require('Phi' in established,'Phi used before its definition is proved')
                    dependencies.add('Phi');visit(node[1],bound)
                else:
                    raise NativeContextError('NATIVE_CONTEXT: '+slot+': unsupported function '+op)
        visit(trees[slot])
        records[slot]={'global_variables':sorted(actual_globals),'previous_definition_dependencies':sorted(dependencies),
                       'lexically_bound_sum_indices':sorted(indices)}
        established.add(slot)
    return {'definition_order':order,'definitions':records,'acyclic_context_checked_before_all_evaluation':True,
            'x_local_to_Phi_and_rho_excluded_from_Phi':True,'no_self_reference_or_unbound_indices':True}


class Native:
    def __init__(self,phi,tiles):
        self.rho=1<<67;self.B=1<<590069
        need(len(tiles)==943 and all(type(t) is list and len(t)==4 and
             all(type(c) is int and 0<=c<=438 for c in t) for t in tiles),'all943 complete actual tile labels')
        self.values=[w+(n<<8)+(e<<17)+(s<<25)+(127<<34) for w,n,e,s in tiles]
        need(len(self.values)==943 and all(127*(1<<34)<=v<(1<<41) for v in self.values),'all943 actual payload bounds')
        self.phi=phi;self.numeric_phi={};self.digits=[]
        self.numeric_variables={'rho':self.rho,'B':self.B,'beta':self.B-1,
                                'Lambda':self.rho**4393+self.rho**5495}
        self.coefficients=defaultdict(int)
        for (e,vs),c in phi.items():
            z=c
            for i in vs:
                z*=self.values[i]
            self.coefficients[e]+=z
        self.coefficients={e:c for e,c in self.coefficients.items() if c}
        need(all(0<=e<=3296 and 0<c<self.rho for e,c in self.coefficients.items()),'all complete Phi digit bounds')
    def phi_value(self,arg):
        if arg not in self.numeric_phi:
            value=0
            for e in range(3296,-1,-1):
                value=value*arg+self.coefficients.get(e,0)
            self.numeric_phi[arg]=value
        return self.numeric_phi[arg]
    def number(self,node,env=None):
        env={} if env is None else env;op=node[0]
        if op=='n':return node[1]
        if op=='v':
            return env[node[1]] if node[1] in env else self.numeric_variables[node[1]]
        if op=='payload':
            i=env['i'];need(type(i) is int and 0<=i<943,'all actual payload indices');return self.values[i]
        if op in ['+','-','*','/','^']:
            a,b=self.number(node[1],env),self.number(node[2],env)
            if op=='+':return a+b
            if op=='-':return a-b
            if op=='*':return a*b
            if op=='/':need(b!=0,'nonzero native divisor');return Fraction(a,b)
            need(type(b) is int and abs(b)<=10000,'fixed native exponent');return a**b if b>=0 else Fraction(a)**b
        if op=='Phi':return self.phi_value(self.number(node[1],env))
        if op=='floor':
            a=self.number(node[1],env);return a.numerator//a.denominator if isinstance(a,Fraction) else a
        if op=='D':
            b,a,e=(self.number(n,env) for n in node[1:])
            need(all(type(x) is int for x in [b,a,e]) and b>1 and a>=0 and 0<=e<=10000,'integer digit arguments')
            # Exact power-of-two digit extraction avoids3297 giant divisions;
            # the ordinary quotient/remainder formula is retained for other bases.
            d=(a>>(e*(b.bit_length()-1)))&(b-1) if b&(b-1)==0 else (a//(b**e))%b
            self.digits.append((b,e,d));return d
        if op=='G':
            m,a=self.number(node[1],env),self.number(node[2],env)
            need(type(m) is int and 0<=m<=10000,'fixed complete geometric bound')
            return sum(a**j for j in range(m))
        if op=='sum':
            hi=self.number(node[3],env);need(type(hi) is int and 0<=node[2]<=hi<=10000,'fixed complete native sum bounds')
            return sum(self.number(node[4],dict(env,**{node[1]:i})) for i in range(node[2],hi+1))
        raise ValueError('native numerical operation '+op)
    def formal(self,node,env=None):
        env={} if env is None else env;op=node[0]
        if op=='n':return const(node[1])
        if op=='v':
            if node[1] in env:return const(env[node[1]])
            return {'x':{(1,()):1},'rho':{(1,()):1},'B':{(8807,()):1},
                    'beta':{(8807,()):1,(0,()):-1},'Lambda':{(4393,()):1,(5495,()):1}}[node[1]]
        if op=='payload':
            i=env['i'];need(type(i) is int and 0<=i<943,'all943 formal payload indices');return {(0,(i,)):1}
        if op in ['+','-','*','/','^']:
            a=self.formal(node[1],env)
            if op=='^':return power(a,self.number(node[2],env))
            b=self.formal(node[2],env)
            if op=='+':return add(a,b)
            if op=='-':return add(a,b,-1)
            if op=='*':return mul(a,b)
            return mul(a,power(b,-1))
        if op=='floor':return const(self.number(node,env))
        if op=='Phi':
            arg=self.formal(node[1],env);need(len(arg)==1,'formal Phi monomial argument')
            (ex,vs),c=next(iter(arg.items()));need(not vs and c==1,'formal Phi unit monomial')
            out=defaultdict(int)
            for (e,v),a in self.phi.items():out[(e*ex,v)]+=a
            return {m:c for m,c in out.items() if c}
        if op=='G':
            m=self.number(node[1],env);need(type(m) is int and 0<=m<=10000,'full formal geometric bound')
            a=self.formal(node[2],env);out={};term=const(1)
            for _ in range(m):out=add(out,term);term=mul(term,a)
            return out
        if op=='sum':
            hi=self.number(node[3],env);need(type(hi) is int and 0<=node[2]<=hi<=10000,'full formal sum bound')
            out={}
            for i in range(node[2],hi+1):out=add(out,self.formal(node[4],dict(env,**{node[1]:i})))
            return out
        raise ValueError('unsupported formal native operation '+op)


def expected_phi():
    # Derive the comparison from the complete accepted eleven-triple specification.
    text=(PARENT/'equation.tex').read_text()
    block=text.split(r'\mathcal C={}',1)[1].split(r'\end{split}',1)[0]
    triples=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',block)]
    need(len(triples)==11 and len(set(triples))==11 and sum(t[2] for t in triples)==41,'complete old controls')
    out={}
    for i in range(943):out[(i,())]=1+(1<<51);out[(i,(i,))]=-(1<<10)
    for b,e,m in triples:
        for j in range(m):
            need((e+j,()) not in out,'disjoint old control support');out[(e+j,())]=1<<(b+j)
    return out,triples


def native_audit(tex):
    body=tex.split(MARKER,1)[1]
    slots,skeleton=native_slots(body)
    reference=(PAGE/'fixed/native-body-reference.txt').read_text()
    need(skeleton==native_slots(reference.split(MARKER,1)[1])[1], 'entire unchanged943 tile/action/seed/footer text and native display skeleton')
    need(r'\mathcal E' not in body and r'\mathcal C' not in body,'no hidden old support/control table')
    trees={name:parse(rhs) for name,rhs in slots.items()}
    contexts=native_contexts(trees)
    expected,triples=expected_phi();tiles=load(INDEXED/'TILES.json')
    work=Native(expected,tiles)
    actual_phi=work.formal(trees['Phi'])
    need(actual_phi==expected,'entire Phi over943 independent formal payload coefficients and all41 controls')
    work=Native(actual_phi,tiles)
    native={'Lambda':work.formal(trees['Lambda'])}
    need(native['Lambda']=={(4393,()):1,(5495,()):1},'complete Lambda identity')
    # Only now may the remaining definitions use the proved Lambda expansion.
    native.update({name:work.formal(trees[name]) for name in ['MC','MF','K']})
    old=(PARENT/'equation.tex').read_text();support_block=old.split(r'\mathcal E={}',1)[1].split(r'\end{split}',1)[0]
    support=set()
    # The first shorthand is \rg0{942}; every other range has braced limits.
    need(r'\rg0{942}' in support_block,'complete accepted selector support')
    support.update(range(943))
    for a,b in re.findall(r'\\rg\{(\d+)\}\{(\d+)\}',support_block):support.update(range(int(a),int(b)+1))
    literal=re.findall(r'\\\{([\d,]+)\\\}',support_block);need(len(literal)==1,'complete accepted dummy/anchor set')
    support.update(map(int,literal[0].split(',')))
    need(len(support)==986 and set(work.coefficients)==support-{1063,1064},'entire formal/nonzero support and both dummy holes')
    old_mc={(8807,()):1,(0,()):-1}
    for e in support-{1}:old_mc=add(old_mc,{(e,()):-1})
    old_mc=add(old_mc,{(1063,()):-2})
    need(native['MC']==old_mc,'complete low-mask rho polynomial with all3297 indicator terms')
    need(len(work.digits)==3297 and [e for b,e,d in work.digits]==list(range(3297)) and
         all(b==work.rho and d==work.coefficients.get(e,0) for b,e,d in work.digits),'actual complete Phi digit extraction and support bounds')
    old_mf=old.split('M_F={}&',1)[1].split('\\\\\nK=',1)[0].rstrip()
    need(old_mf.endswith(','),'complete accepted MF punctuation');old_mf=old_mf[:-1]
    old_k=old.split('K={}&',1)[1].split(',\n\\end{align*}',1)[0]
    need(native['MF']==work.formal(parse(old_mf)),'entire unchanged formal MF polynomial')
    need(native['K']==work.formal(parse(old_k)),'entire unchanged formal K with943 independent payloads')
    # Evaluate whole collected polynomials, not sampled coefficients or hashes alone.
    values={'beta':work.B-1}
    for name in ['MC','MF','K']:
        poly=native[name];need(all(e>=0 for e,vs in poly),'native final integer powers')
        coefficients=defaultdict(int)
        for (e,vs),c in poly.items():
            for i in vs:c*=work.values[i]
            coefficients[e]+=c
        value=0
        for e in range(max(coefficients),-1,-1):value=value*work.rho+coefficients.get(e,0)
        values['K0' if name=='K' else name]=value
    records={};total=0
    for name,pin in load(PAGE/'COEFFICIENT_BINDING.json')['ports'].items():
        raw=gzip.decompress((PAGE/'coefficients'/pin['file']).read_bytes());value=values[name]
        need(value>0 and value.bit_length()==pin['bits'] and value.to_bytes((pin['bits']+7)//8,'little')==raw,'all bytes of actual printed native integer '+name)
        records[name]={'bytes':len(raw),'sha256':digest(raw)};total+=len(raw)
    need(total==295388,'all four whole integers')
    return {'native_contexts':contexts,'all943_formal_selector_coefficients':True,'control_triples':len(triples),'control_coefficients':41,
            'full_formal_Phi_terms':len(actual_phi),'actual_digits_checked':3297,'nonzero_support':984,
            'zero_dummy_positions':[1063,1064],'all_formal_Lambda_MC_MF_K_coefficients_equal':True,'whole_raw_bytes':total,'ports':records}


def prose_hyphen_words():
    # Immutable English words paired with their exact reviewed prose spans.
    # No word is obtained from arbitrary TeX, math, commands or seed bytes.
    spans=[
        ('The only unknowns are',{'unknowns'}),
        ('All other symbols in the equation are polynomial abbreviations:',{'symbols','equation','polynomial','abbreviations'}),
        ('The single equation is',{'single','equation'}),
        ('Every index, set, sum, product and floor below defines a constant, not\nanother unknown. Put',
         {'Every','product','floor','below','defines','constant','another','unknown'}),
        ('The rational intermediate in K cancels exactly; all four results are positive integers.',
         {'rational','intermediate','cancels','exactly','results','positive','integers'}),
        ('Use the actions ',{'actions'}),
        (' decoded below. Let',{'decoded'}),
        ('An interval ending at ',{'interval','ending'}),
        (' is empty. The table defines ',{'empty','table','defines'}),
        ('; all index ranges are fixed:',{'ranges','fixed'}),
        ('uses this actual first target, including its state renaming.',{'actual','first','target','including','state','renaming'}),
        ('The alphabet, in order of digit values ',{'alphabet','order','digit','values'}),
        ('Concatenate the following 436 characters as digits ',{'Concatenate','following','characters','digits'}),
        ('The ordinary state/color-conjugacy, native and Pell arguments give',{'ordinary','color','conjugacy','native','arguments'}),
        ('unsolvability iff ',{'unsolvability'}),
        ('Native calibration and internal-ZFC formalization remain open in Lean.',{'Native','calibration','internal','formalization','remain'}),
        ('This page is a complete finite specification, not an unsolvability proof.',{'complete','finite','specification','unsolvability','proof'})]
    tex=(PAGE/'equation.tex').read_text()
    math=list(re.finditer(r'\\\[(.*?)\\\]|\$(.*?)\$|\\begin\{align\*\}(.*?)\\end\{align\*\}',tex,re.S))
    math_words={w for m in math for w in re.findall(r'[A-Za-z]+',m[0])}
    commands=set(re.findall(r'\\([A-Za-z]+)',tex))
    seed=(PAGE/'SEED.txt').read_text().strip()
    intentional={a+b for a,b in re.findall(r'([A-Za-z]+)-([A-Za-z]+)',tex)}
    words=set()
    for span,allowed in spans:
        need(tex.count(span)==1 and not re.search(r'[\\$]',span),'one exact literal English prose span')
        start=tex.index(span);end=start+len(span)
        need(all(end<=m.start() or start>=m.end() for m in math),'prose whitelist span is outside all math')
        for word in allowed:
            need(re.fullmatch(r'[A-Za-z]{5,}',word) and re.search(r'\b'+re.escape(word)+r'\b',span),
                 'whitelist word occurs in its literal prose span')
            need(word not in math_words and word not in commands and word not in seed and word not in intentional,
                 'whitelist excludes math, macros, seed and intentional hyphen joins')
        words.update(allowed)
    return words


def glyphs(text):
    # Normalize only whitespace, known floor font encodings, and automatic
    # English hyphenation from the validated immutable prose-only whitelist.
    words=prose_hyphen_words()
    def join(m):
        return m[1]+m[2] if m[1]+m[2] in words else m[0]
    text=re.sub(r'\b([A-Za-z]{2,})-\s*\n\s*([A-Za-z]{3,})\b',join,text)
    return re.sub(r'\s','',text.replace('\x04','⌊').replace('\x05','⌋'))


def expected_native_glyphs():
    # The entire actual old PDF suffix, with complete prescribed replacements.
    text=(PARENT/'equation.txt').read_text().split('The four fixed integers.',1)[1]
    text=glyphs(text)
    a=text.index('DefineE=');b=text.index('MF=',a)
    mc='MC=β+ρ−(ρ+3)ρ1063−X3296e=0⌊(Dρ(Φ(ρ),e)+ρ−1)/ρ⌋ρe,'
    text=text[:a]+mc+text[b:]
    a=text.index('+X(b,e,m)∈C',text.index('Φ(x)'))
    b=text.index('Therationalintermediate',a)
    controls=('+210x1003(x20+217)G8(2x)+218x983(x30+217)G9(2x)'
              '+244x992(x39+2x30+4x19+8)+248x1095(1+2x1100+4x2201).')
    text=text[:a]+controls+text[b:]
    old='(ρ4393+ρ5495)'
    need(text.count(old)==2 and text.count('xj.')==1,'two complete old Lambda uses and whole initial display')
    return text.replace(old,'Λ').replace('xj.','xj,Λ=ρ4393+ρ5495.')


def compare_native_glyphs(text):
    expected=expected_native_glyphs()
    need(glyphs(text)==expected,'entire actual native glyph stream, all five changed slots,943 table,decoder,436seed,alphabet and footer')
    return expected


def compare_front_glyphs(text):
    prior=(PARENT/'equation.txt').read_text().split('The four fixed integers.',1)[0]
    need(glyphs(text)==glyphs(prior),'every actual front/title/domain/equation glyph')


def front_hyphen_controls():
    prior=(PARENT/'equation.txt').read_text().split('The four fixed integers.',1)[0]
    target='D = X + ac + γH'
    need(prior.count(target)==1 and prior.count('polynomial')==1 and prior.count('fifteen-variable')==1,
         'unique actual complete-front hyphenation control targets')
    rejected=[]
    for label,replacement in [('mathematical ASCII minus','D = X + a-\nc + γH'),
                              ('mathematical Unicode minus','D = X + a−\nc + γH'),
                              ('unknown mathematical glyph','D = X + a☃c + γH')]:
        try:
            compare_front_glyphs(prior.replace(target,replacement))
        except ValueError:
            rejected.append(label)
        else:
            raise ValueError('accepted complete-front corruption '+label)
    compare_front_glyphs(prior.replace('polynomial','poly-\nnomial'))
    compare_front_glyphs(prior.replace('fifteen-variable','fifteen-\nvariable'))
    need(len(rejected)==3,'all three complete-front corruption controls')
    return {'complete_front_negative':rejected,'valid_English_line_hyphen':True,'intentional_hyphen_preserved':True}


def native_controls(tex):
    mutants=[('low-mask rho sign',r'\beta+\rho-(\rho+3)',r'\beta-\rho-(\rho+3)'),
             ('dummy correction',r'(\rho+3)\rho^{1063}',r'(\rho+2)\rho^{1063}'),
             ('missing highest indicator',r'\sum_{e=0}^{3296}',r'\sum_{e=0}^{3295}'),
             ('wrong digit base',r'D_\rho(\Phi(\rho),e)',r'D_2(\Phi(\rho),e)'),
             ('indicator wrong offset',r'+\rho-1)/\rho}',r'+2\rho-1)/\rho}'),
             ('selector common coefficient',r'\Phi(x)={}&(1+2^{51})',r'\Phi(x)={}&(1+2^{50})'),
             ('missing selector',r'\sum_{i=0}^{942}',r'\sum_{i=0}^{941}'),
             ('first geometric bound','G_8(2x)','G_7(2x)'),
             ('first control shift','x^{1003}(x^{20}+2^{17})','x^{1003}(x^{21}+2^{17})'),
             ('second control weight','2^{18}x^{983}','2^{19}x^{983}'),
             ('third control coefficient','x^{39}+2x^{30}+4x^{19}+8','x^{39}+2x^{30}+5x^{19}+8'),
             ('fourth control exponent','1+2x^{1100}+4x^{2201}','1+2x^{1100}+4x^{2200}'),
             ('Lambda exponent',r'\Lambda=\rho^{4393}+\rho^{5495}',r'\Lambda=\rho^{4393}+\rho^{5494}'),
             ('MF clause mask',r'(2^{51}-2)\Lambda',r'(2^{51}-1)\Lambda'),
             ('K reciprocal argument',r'\Lambda\Phi(1/\rho)',r'\Lambda\Phi(\rho)'),
             ('K whole-cell exponent',r'+\rho^{8849}',r'+\rho^{8848}'),
             ('unconsumed native token','G_8(2x)','G_8(2x)!')]
    rejected=[]
    for label,old,new in mutants:
        need(tex.count(old)==1,'unique actual native mutation '+label)
        try:
            native_audit(tex.replace(old,new))
        except (ValueError,KeyError,IndexError,TypeError):
            rejected.append(label)
        else:
            raise ValueError('accepted native corruption '+label)
    slots,_=native_slots(tex.split(MARKER,1)[1])
    scope_mutants=[
        ('Lambda self reference',r'\Lambda=\rho^{4393}+\rho^{5495}',r'\Lambda=\Lambda'),
        ('Phi self reference',slots['Phi'],r'\Phi(x)'),
        ('Phi local x replaced by global rho','G_{943}(x)',r'G_{943}(\rho)'),
        ('Lambda global rho replaced by free x',r'\Lambda=\rho^{4393}+\rho^{5495}',r'\Lambda=x^{4393}+\rho^{5495}'),
        ('MF free global x',r'\rho^{1013}G_{10}(\rho)',r'x^{1013}G_{10}(\rho)'),
        ('K free global x',r'\Lambda\Phi(1/\rho)',r'\Lambda\Phi(1/x)'),
        ('MC unbound index i',r'D_\rho(\Phi(\rho),e)',r'D_\rho(\Phi(\rho),i)'),
        ('MF unbound index e',r'\rho^{2195}+\rho^{3296}',r'\rho^e+\rho^{3296}'),
        ('Phi payload outside its lexical sum','G_{943}(x)','v(t_i)G_{943}(x)'),
        ('Phi nonfixed sum bound',r'\sum_{i=0}^{942}',r'\sum_{i=0}^{x}'),
        ('Phi nonfixed geometric bound','G_{943}(x)','G_x(x)'),
        ('Phi nonfixed exponent','x^{20}','x^x')]
    scope_rejected=[]
    for label,old,new in scope_mutants:
        need(tex.count(old)==1,'unique actual native context mutation '+label)
        try:
            native_audit(tex.replace(old,new))
        except NativeContextError as error:
            need(str(error).startswith('NATIVE_CONTEXT: '),'specific native context rejection')
            scope_rejected.append({'control':label,'error':str(error)})
        else:
            raise ValueError('accepted native context corruption '+label)
    positives=[tex.replace(r'\beta+\rho-(\rho+3)',r'\rho+\beta-(\rho+3)'),
               tex.replace(r'\Lambda=\rho^{4393}+\rho^{5495}',r'\Lambda=\rho^{5495}+\rho^{4393}'),
               tex.replace('x^{1003}(x^{20}+2^{17})','x^{1003}(2^{17}+x^{20})'),
               tex.replace(r'(2^{51}-2)\Lambda',r'\Lambda(2^{51}-2)'),
               tex.replace(r'\Lambda\Phi(1/\rho)',r'\Phi(1/\rho)\Lambda')]
    for good in positives:
        native_audit(good)
    expected=expected_native_glyphs()
    glyph_controls=[]
    for label,old,new in [('Lambda glyph','Λ','L'),('native exponent','x1003','x1004'),
                          ('missing seed digit','BxEnhvy6Ni','BxEnhvy6N'),
                          ('constructor','(3,436,4,4)','(3,436,4,0)')]:
        need(old in expected,'actual full native glyph control target')
        altered=expected.replace(old,new,1)
        try:
            compare_native_glyphs(altered)
        except ValueError:
            pass
        else:
            raise ValueError('accepted whole native glyph corruption '+label)
        glyph_controls.append(label)
    need(len(rejected)==17 and len(scope_rejected)==12 and len(positives)==5 and len(glyph_controls)==4,'all grouped native controls')
    return {'actual_TeX_negative':rejected,'actual_TeX_context_negative':scope_rejected,
            'valid_native_algebra':len(positives),'whole_native_glyph_negative':glyph_controls}


def pdf_audit():
    def extract(path):
        return subprocess.run(['pdftotext','-raw',str(path),'-'],check=True,capture_output=True,text=True,timeout=30).stdout
    actual=extract(PAGE/'equation.pdf');prior=(PARENT/'equation.txt').read_text()
    boundary='The four fixed integers.'
    need(actual.count(boundary)==prior.count(boundary)==1,'whole actual PDF section boundary')
    left,native=actual.split(boundary,1)
    compare_front_glyphs(left)
    expected=compare_native_glyphs(native)
    need((PAGE/'equation.txt').read_text()==actual,'whole saved PDF text matches actual extraction')
    info=subprocess.run(['pdfinfo',str(PAGE/'equation.pdf')],check=True,capture_output=True,text=True,timeout=30).stdout
    need(re.search(r'Pages:\s+1\b',info) and '612 x 792' in info,'one actual Letter page')
    need(all('Overfull' not in (PAGE/n).read_text() for n in ['RENDER.txt','TEX_DIAGNOSTICS.txt']),'retained zero overfull diagnostics')
    return {'whole_front_glyphs_equal_accepted_parent':True,'whole_native_glyphs_equal_prescribed_complete_replacement':True,
            'native_normalized_glyphs':len(expected),'native_expected_sha256':digest(expected.encode()),
            'actual_nonwhite_PDF_characters':len(re.sub(r'\s','',actual)),'all_saved_text_bytes_match':True,
            'normalization':'whitespace, two known floor encodings, and only immutable-prose-whitelist ASCII line hyphens with left>=2/right>=3 letters; Unicode minus, intentional hyphens and unknown glyphs preserved'}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source-only',action='store_true')
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    pins=authenticate()
    old=adopted_front()
    old.source_index()
    packet=load(PAGE/'polynomial.json');historical=load(PAGE/'fixed/source54-p66.json')
    need((PAGE/'polynomial.json').read_bytes()==(PARENT/'polynomial.json').read_bytes(),'complete accepted polynomial bytes unchanged')
    need((PAGE/'COEFFICIENT_BINDING.json').read_bytes()==(PARENT/'COEFFICIENT_BINDING.json').read_bytes(),'complete accepted coefficient binding bytes unchanged')
    definitions,counts=old.circuit(packet,historical);bound=old.binding(packet)
    cal=load(PAGE/'CALIBRATION_BINDING.json');old.calibration(cal)
    expected_cal=load(PARENT/'CALIBRATION_BINDING.json');expected_cal['proof_sha256']=digest((PAGE/'PROOF.md').read_bytes())
    need(cal==expected_cal,'entire inherited calibration with only proof-hash update')
    seed=(PAGE/'SEED.txt').read_text().strip()
    need((PAGE/'SEED.txt').read_bytes()==(PARENT/'SEED.txt').read_bytes()==(INDEXED/'SEED.txt').read_bytes(),'whole unchanged436-character seed')
    tex=(PAGE/'equation.tex').read_text();native=native_audit(tex)
    body=tex.split(MARKER,1)[1]
    cuts,math,box,_=old.tex_audit(tex,packet,historical,body,seed)
    mapping=load(PAGE/'FORMULA_MAP.json')
    need((PAGE/'FORMULA_MAP.json').read_bytes()==(PARENT/'FORMULA_MAP.json').read_bytes() and
         mapping['assignments']==cuts+[{'tex_lhs':'BOX','literal_register':'polynomial'}] and
         mapping['historical_source_sha256']==digest((PAGE/'fixed/source54-p66.json').read_bytes()) and
         mapping['operations']==66 and mapping['exact_degree']==157 and mapping['operation_counts']==counts,'entire actual formula map and all23 cuts')
    degree=old.degree_audit(definitions)
    front_negative,front_positive=old.controls(tex,packet,historical,body,seed,cal)
    controls=native_controls(tex)
    hyphens=front_hyphen_controls()
    pdf=None if args.source_only else pdf_audit()
    result={'status':'PASS','optimized_python':bool(sys.flags.optimize),'mode':'source/actual-TeX only' if args.source_only else 'complete actual grouped page',
            'operations':66,'operation_counts':counts,'exact_degree':157,'all66_rows_live_and_covered':True,
            'all15_positive_unknowns_and4_ports_live':True,'actual_polynomial_cuts':cuts+[{'tex_lhs':'BOX','literal_register':'polynomial'}],
            'degree_proof':degree,'whole_native_recipe':native,'whole_indexed_binding':bound,
            'accepted_front_negative_controls':front_negative,'accepted_front_valid_controls':front_positive,
            'grouped_native_controls':controls,'PDF_audited':not args.source_only,'actual_PDF':pdf,
            'complete_front_hyphenation_controls':hyphens,
            'source_pins_sha256':digest((PAGE/'SOURCE_PINS.json').read_bytes()),'auditor_sha256':digest(Path(__file__).read_bytes()),
            'adopted_front_sha256':digest((PARENT/'FRONT_AUDIT.py').read_bytes()),
            'sha256':{n:digest((PAGE/n).read_bytes()) for n in ['equation.tex','polynomial.json','COEFFICIENT_BINDING.json','CALIBRATION_BINDING.json','SOURCE_INDEX.json','FORMULA_MAP.json','SEED.txt']},
            'scope':'Same exact complete P66 and native integers; full actual changed recipe parsing/formal algebra/whole bytes. No new native calibration, consistency decision or main-page promotion.'}
    if not args.source_only:result['sha256']['equation.pdf']=digest((PAGE/'equation.pdf').read_bytes())
    raw=encoded(result)
    protected={(ROOT/n).resolve() for group in ['external_files','own_core'] for n in pins[group]}
    protected|={(PAGE/n).resolve() for n in ['SOURCE_PINS.json','HOLD_INVENTORY.json','MANIFEST.json','polynomial.json','COEFFICIENT_BINDING.json','CALIBRATION_BINDING.json','SOURCE_INDEX.json','equation.pdf','equation.txt','RENDER.txt','TEX_DIAGNOSTICS.txt','RENDER_DATA.json']}
    need(args.output.resolve()!=ROOT.parents[1].resolve() and ROOT.parents[1].resolve() not in args.output.resolve().parents,
         'receipt must remain outside the repository')
    need(not args.output.is_symlink() and args.output.resolve() not in protected and
         (not args.output.exists() or args.output.read_bytes()==raw),'separate fresh or identical audit receipt')
    args.output.write_bytes(raw);print(raw.decode(),end='')


if __name__=='__main__':
    main()
