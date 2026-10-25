#!/usr/bin/env python3
"""CODE/TEX ONLY/HOLD: complete actual compact recipe and accepted P66."""
import argparse
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
PAGE=ROOT/'candidates/one-page-compact66'
PARENT=ROOT/'candidates/one-page-fifteen66'
INDEXED=ROOT/'research/indexed-tile-enumeration'
GROUPED=ROOT/'candidates/one-page-grouped66'
MARKER=r'\textbf{The four fixed integers.}'
ALPHABET='0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
SEALS={'candidates/one-page-fifteen66':'065a396f78fb271b1b82cadd2d61b9a79f774cd82739d41946b1a9fcf8384424',
       'research/grouped-fixed-coefficient-recipe':'f5ae707993e3041a6d35f4144e0baade3cfa45fd3d4f5875c825771fad1a9594',
       'research/indexed-tile-enumeration':'e077a476c38cb9abd96217887d16b011f6f5e16847036702720d69fcf91b1f84',
       'research/compact-tile-parameters':'5dafe5e3d18abb8d8a4e2254d7ac777d9db21933a8b768eba2c46535a9e3fdf9',
       'research/binary-pass-cleanup-tiles':'80d44e88695ed56036aaeab3a50292a388bbf2cd7e960463125c7a75fb349a6c',
       'candidates/one-page-grouped66':'187ce13905b346ccb435e86745b60f212dc46c9c726307e5cd82cb98b9e7c886'}


def need(ok,message):
    if not ok:raise ValueError(message)


def digest(raw):return sha256(raw).hexdigest()
def load(path):return json.loads(path.read_bytes())
def encoded(value):return (json.dumps(value,indent=2,sort_keys=True)+'\n').encode()


def authenticate():
    pins=load(PAGE/'SOURCE_PINS.json')
    for group in ['external_files','own_core']:
        for name,pin in pins[group].items():
            path=ROOT/name;raw=path.read_bytes()
            need(not path.is_symlink() and pin=={'bytes':len(raw),'sha256':digest(raw)},'whole reviewed input '+name)
    need({d['folder']:d['manifest_sha256'] for d in pins['closed_dependencies']}==SEALS,'six whole fixed contracts')
    for name,seal in SEALS.items():
        folder=ROOT/name;raw=(folder/'MANIFEST.json').read_bytes()
        need(digest(raw)==seal,'whole parent seal '+name)
        files=json.loads(raw)['files']
        actual={p.relative_to(folder).as_posix() for p in folder.rglob('*') if p.is_file() and p!=folder/'MANIFEST.json'}
        need(actual==set(files),'complete immutable parent inventory '+name)
        for relative,pin in files.items():
            path=folder/relative;data=path.read_bytes()
            expected={'bytes':len(data),'sha256':digest(data)} if isinstance(pin,dict) else digest(data)
            need(not path.is_symlink() and pin==expected,'whole parent payload '+relative)
    return pins


def imported(path,name):
    # Called only after own/direct/whole-parent authentication has completed.
    spec=importlib.util.spec_from_file_location(name,path)
    need(spec is not None and spec.loader is not None,'reviewed local module '+name)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module


def configure():
    global core,recipe,_native,_grouped_expected
    core=imported(PAGE/'GROUPED_CORE.py','reviewed_local_grouped66_r2_core')
    recipe=imported(PAGE/'RECIPE_AUDIT.py','reviewed_actual_compact66_recipe')
    core.ROOT=ROOT;core.PAGE=PAGE;core.PARENT=PARENT;core.INDEXED=INDEXED
    old=core.adopted_front()
    canonical=core.Native
    class ComplementedNative(canonical):
        # The canonical stored values remain OLD payloads: the resulting Phi
        # coefficients and whole integer evaluation use exactly that basis.
        # Only an actual printed new payload occurrence is complemented.
        def formal(self,node,env=None):
            if node[0]=='payload':
                env={} if env is None else env;i=env['i']
                need(type(i) is int and 0<=i<943,'all actual complemented formal payload indices')
                return core.add(core.const(1<<41),{(0,(i,)):1},-1)
            return super().formal(node,env)
        def number(self,node,env=None):
            if node[0]=='payload':
                env={} if env is None else env;i=env['i']
                need(type(i) is int and 0<=i<943,'all actual complemented numerical payload indices')
                return (1<<41)-self.values[i]
            return super().number(node,env)
    core.Native=ComplementedNative
    _native=core.native_audit;_grouped_expected=core.expected_native_glyphs
    core.native_audit=native_audit
    core.glyphs=glyphs;core.prose_hyphen_words=prose_hyphen_words
    core.expected_native_glyphs=expected_native_glyphs
    return old


def native_audit(tex):
    reference=(PAGE/'equation.tex').read_text()
    seed=(PAGE/'SEED.txt').read_text().strip()
    normalized,record=recipe.audit(tex,reference,load(INDEXED/'TILES.json'),seed,ALPHABET)
    # Every cut was parsed/scoped/proved before this immutable skeleton guard.
    # All five actual Phi/Lambda/MC/MF/K RHS expressions stay untouched here.
    native=_native(normalized)
    native['actual_compact_recipe']=record
    return native


def expected_native_glyphs():
    text=glyphs((GROUPED/'equation.txt').read_text().split('The four fixed integers.',1)[1])
    need(text==_grouped_expected(),'entire actual accepted grouped suffix also matches its full reviewed prescription')
    def replace(old,new):
        nonlocal text
        need(text.count(old)==1,'one whole inherited native glyph replacement '+old[:45])
        text=text.replace(old,new)
    replace('Φ(x)=(1+251)G943(x)−210X942i=0v(ti)xi',
            'Φ(x)=G943(x)+210X942i=0v(ti)xi')
    a=text.index('The943indexedfixedtiles.');b=text.index('Acloseddecoderforthe430actions.',a)
    tiles=('The943indexedfixedtiles.Usetheactionsuj,vj,djdecodedbelow.Ford=0,1,let'
           'h(q,b)=2q+b+2,Sd={uj:dj=d,0≤j<430},rd,q=205−199d+|Sd∩{0,...,q−1}|.'
           'Anintervalendingat−1isempty.Thetabledefinestifor0≤i≤942;allindexrangesarefixed:'
           'indexitileti=(w,n,e,s)0,1(2,435,3,1),(5,0,0,0)'
           'j+2(j=2q+b<430)((1−dj)r0,uj,h(q,b),djr1,uj,vj)'
           '434−2a+b(a,b=0,1)(0,432a+b,0,432a+b)'
           '424+2rd,q+bq∈Sd,d,b=0,1(drd,q,b,(1−d)rd,q,h(q,b))'
           '924+2a+b(a,b=0,1)(0,432a+b,0,438)'
           '928(2,434,2,0)929(3,436,4,4)930(4,436,4,0)'
           '497+t(t=434,435,436)(1,438,1,t)934+3a+b(a,b=0,1,2)(a2,437,b,437)'
           'Fort=(w,n,e,s)putv(t)=234−w−28n−217e−225s.')
    text=text[:a]+tiles+text[b:]
    replace('Fq=14(1−mq)+mqD16(E0,τq),','Fq=14+mq(D16(E0,τq)−14),')
    return text


def math_delimiter_controls(tex):
    regions=core.tex_math_regions(tex)
    counts={label:sum(m[group] is not None for m in regions)
            for label,group in [('display',1),('inline',2),('align',3)]}
    need(counts=={'display':9,'inline':17,'align':1} and len(regions)==27,'all27 actual TeX math regions')
    first=next(m for m in regions if m[1] is not None)
    need(tex[:first.start()].count('\n')+1==19,'actual first display is the unknowns signature on line19')
    for text in [r'\\[-1pt]','A complete fifteen-variable consistency equation','The only unknowns are']:
        need(tex.count(text)==1,'unique title/prose delimiter regression target')
        start=tex.index(text);end=start+len(text)
        need(all(end<=m.start() or start>=m.end() for m in regions),'title linebreak and first prose excluded from math')
    fixture=r'\\[-1pt] literal \$5; $x+\$y$ \[z\] \begin{align*}w\end{align*}'
    expected=[r'$x+\$y$',r'\[z\]',r'\begin{align*}w\end{align*}']
    need([m[0] for m in core.tex_math_regions(fixture)]==expected,'same-helper linebreak/escaped-dollar fixture')
    return {'actual_TeX_regions':counts,'total':27,'first_display_line':19,
            'title_linebreak_and_first_prose_outside_math':True,'same_helper_escaped_dollar_fixture':True}




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
        (' decoded below. For ',{'decoded'}),
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
    math=core.tex_math_regions(tex)
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




def native_controls(tex):
    mutants=[('low-mask rho sign',r'\beta+\rho-(\rho+3)',r'\beta-\rho-(\rho+3)'),
             ('dummy correction',r'(\rho+3)\rho^{1063}',r'(\rho+2)\rho^{1063}'),
             ('missing highest indicator',r'\sum_{e=0}^{3296}',r'\sum_{e=0}^{3295}'),
             ('wrong digit base',r'D_\rho(\Phi(\rho),e)',r'D_2(\Phi(\rho),e)'),
             ('indicator wrong offset',r'+\rho-1)/\rho}',r'+2\rho-1)/\rho}'),
             ('selector common coefficient',r'\Phi(x)={}&G_{943}',r'\Phi(x)={}&2G_{943}'),
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
    slots,_=core.native_slots(tex.split(MARKER,1)[1])
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
        except core.NativeContextError as error:
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
            core.compare_native_glyphs(altered)
        except ValueError:
            pass
        else:
            raise ValueError('accepted whole native glyph corruption '+label)
        glyph_controls.append(label)
    need(len(rejected)==17 and len(scope_rejected)==12 and len(positives)==5 and len(glyph_controls)==4,'all grouped native controls')
    return {'actual_TeX_negative':rejected,'actual_TeX_context_negative':scope_rejected,
            'valid_native_algebra':len(positives),'whole_native_glyph_negative':glyph_controls}




def recipe_controls(tex):
    mutants=[
        ('global direction domain','For $d=0,1$, let','For $d=0,1,2$, let'),
        ('head label','h(q,b)=2q+b+2','h(q,b)=2q+b+3'),
        ('set direction predicate','d_j=d,','d_j=1,'),
        ('set action range',r'd_j=d,\ 0\le j<430',r'd_j=d,\ 0\le j<429'),
        ('rank affine offset','205-199d+','204-199d+'),
        ('rank set subscript',r'|\mathcal S_d\cap',r'|\mathcal S_0\cap'),
        ('rank interval end',r'\rg0{q-1}',r'\rg0q'),
        ('transition index',r'j+2\ (j=2q+b<430)',r'j+3\ (j=2q+b<430)'),
        ('transition direction',r'((1-d_j)r_{0,u_j}',r'(d_jr_{0,u_j}'),
        ('transition domain',r'j+2\ (j=2q+b<430)',r'j+2\ (j=2q+b<429)'),
        ('pass index',r'434-2a+b\ (a,b=0,1)',r'434-a+b\ (a,b=0,1)'),
        ('pass domain',r'434-2a+b\ (a,b=0,1)',r'434-2a+b\ (a,b=0,1,2)'),
        ('pass north/south labels','(0,432a+b,0,432a+b)','(0,431a+b,0,431a+b)'),
        ('copy index','424+2r_{d,q}+b','423+2r_{d,q}+b'),
        ('copy direction','(dr_{d,q},b,(1-d)r_{d,q},h(q,b))','((1-d)r_{d,q},b,(1-d)r_{d,q},h(q,b))'),
        ('copy binary domain',r'q\in\mathcal S_d,\ d,b=0,1',r'q\in\mathcal S_d,\ d,b=0,1,2'),
        ('cleanup index',r'924+2a+b\ (a,b=0,1)',r'925+2a+b\ (a,b=0,1)'),
        ('cleanup domain',r'924+2a+b\ (a,b=0,1)',r'924+2a+b\ (a,b=0)'),
        ('cleanup label','(0,432a+b,0,438)','(0,430a+b,0,438)'),
        ('literal controller','928&(2,434,2,0)','928&(2,435,2,0)'),
        ('tail domain','t=434,435,436','t=434,435,435'),
        ('terminal index',r'934+3a+b\ (a,b=0,1,2)',r'934+2a+b\ (a,b=0,1,2)'),
        ('terminal domain',r'934+3a+b\ (a,b=0,1,2)',r'934+3a+b\ (a,b=0,1)'),
        ('terminal square','(a^2,437,b,437)','(a,437,b,437)'),
        ('complemented payload sign','v(t)=2^{34}-w-','v(t)=2^{34}+w-'),
        ('complemented payload constant','v(t)=2^{34}-w-','v(t)=2^{35}-w-'),
        ('decoder N modulus',r'N=\mathcal A\bmod2^{636}',r'N=\mathcal A\bmod2^{635}'),
        ('decoder target quotient',r'T_0=\fl{\mathcal A/2^{636}}',r'T_0=\fl{\mathcal A/2^{635}}'),
        ('decoder nibble quotient',r'E_0=\fl{\mathcal A/2^{2311}}',r'E_0=\fl{\mathcal A/2^{2310}}'),
        ('decoder target flag',r'\nu_j=D_2(N,j)',r'\nu_j=D_2(N,j+1)'),
        ('decoder target rank sum',r'\sigma_j=\sum_{k=0}^{j-1}\nu_k',r'\sigma_j=\sum_{k=0}^{j}\nu_k'),
        ('decoder default mask','m_q=D_2(N,430+q)','m_q=D_2(N,429+q)'),
        ('decoder stored rank sum',r'\tau_q=\sum_{k=0}^{q-1}m_k',r'\tau_q=\sum_{k=0}^{q}m_k'),
        ('factored nibble constant','F_q=14+m_q','F_q=13+m_q'),
        ('stored nibble index',r'D_{16}(E_0,\tau_q)',r'D_{16}(E_0,\tau_q+1)'),
        ('target radix','D_{216}(T_0','D_{215}(T_0'),
        ('write bit','v_j=D_2(F_q,2b)','v_j=D_2(F_q,2b+1)'),
        ('direction bit','d_j=D_2(F_q,2b+1)','d_j=D_2(F_q,2b)'),
        ('decoder state domain',r'For $0\le q<215$',r'For $0\le q<214$'),
        ('decoder binary domain',r'$b=0,1$, $j=2q+b$',r'$b=0,1,2$, $j=2q+b$'),
        ('decoder action binding',r'$j=2q+b$:',r'$j=2q+1-b$:'),
        ('positional full bound',r'\sum_{j=0}^{435}e_j62^{435-j}',r'\sum_{j=0}^{434}e_j62^{435-j}'),
        ('positional radix','e_j62^{435-j}','e_j61^{435-j}'),
        ('positional exponent','e_j62^{435-j}','e_j62^{434-j}'),
        ('actual digit primitive',r'D_b(A,k)=\fl{A/b^k}',r'D_b(A,k)=\fl{A/b^{k+1}}'),
        ('actual remainder primitive',r'a\bmod b=a-b\fl{a/b}',r'a\bmod b=a+b\fl{a/b}'),
        ('unconsumed head token','h(q,b)=2q+b+2','h(q,b)=2q+b+2!')]
    rejected=[]
    for label,old,new in mutants:
        need(tex.count(old)==1,'one complete actual recipe corruption '+label)
        try:native_audit(tex.replace(old,new))
        except (ValueError,KeyError,IndexError,TypeError):rejected.append(label)
        else:raise ValueError('accepted actual recipe corruption '+label)
    scopes=[
        ('payload free q','v(t)=2^{34}-w-','v(t)=2^{34}-q-'),
        ('head free j','h(q,b)=2q+b+2','h(q,b)=2j+b+2'),
        ('rank free j','205-199d+','205-199j+'),
        ('set free a','d_j=d,','d_j=a,'),
        ('flag self reference','F_q=14+m_q','F_q=14+F_q'),
        ('target flag self reference',r'\nu_j=D_2(N,j)',r'\nu_j=\nu_j'),
        ('target rank free q',r'\sigma_j=\sum_{k=0}^{j-1}\nu_k',r'\sigma_j=q+\sum_{k=0}^{j-1}\nu_k'),
        ('rank sum shadowing',r'\tau_q=\sum_{k=0}^{q-1}m_k',r'\tau_q=\sum_{q=0}^{q-1}m_q'),
        ('transition free a','((1-d_j)r_{0,u_j},h(q,b)','((1-d_j)r_{0,u_j},h(a,b)'),
        ('pass free q','(0,432a+b,0,432a+b)','(0,432q+b,0,432a+b)'),
        ('cleanup free j','(0,432a+b,0,438)','(0,432j+b,0,438)'),
        ('terminal free d','(a^2,437,b,437)','(d^2,437,b,437)'),
        ('target quotient self reference',r'T_0=\fl{\mathcal A/2^{636}}',r'T_0=\fl{T_0/2^{636}}'),
        ('positional free q','e_j62^{435-j}','e_j62^{435-q}')]
    scope_rejected=[]
    for label,old,new in scopes:
        need(tex.count(old)==1,'one complete actual recipe scope control '+label)
        try:native_audit(tex.replace(old,new))
        except recipe.RecipeContextError as error:
            need(str(error).startswith('RECIPE_CONTEXT: '),'specific pre-evaluation lexical rejection')
            scope_rejected.append({'control':label,'error':str(error)})
        else:raise ValueError('accepted actual recipe scope corruption '+label)
    positives=[
        ('payload term order','v(t)=2^{34}-w-2^8n','v(t)=2^{34}-2^8n-w'),
        ('head distributivity','h(q,b)=2q+b+2','h(q,b)=2(q+1)+b'),
        ('set equality symmetry','d_j=d,','d=d_j,'),
        ('pass index commutation',r'434-2a+b\ (a,b=0,1)',r'b+434-2a\ (a,b=0,1)'),
        ('cleanup index commutation',r'924+2a+b\ (a,b=0,1)',r'b+924+2a\ (a,b=0,1)'),
        ('terminal square multiplication','(a^2,437,b,437)','(a*a,437,b,437)'),
        ('flag distributivity',r'F_q=14+m_q(D_{16}(E_0,\tau_q)-14)',r'F_q=14(1-m_q)+m_qD_{16}(E_0,\tau_q)'),
        ('positional parentheses','e_j62^{435-j}','e_j62^{(435-j)}')]
    for label,old,new in positives:
        need(tex.count(old)==1,'one actual valid recipe algebra control '+label)
        native_audit(tex.replace(old,new))
    glyph_controls=[];expected=expected_native_glyphs()
    for label,old,new in [('direction parameter','Ford=0,1,let','Ford=0,let'),
                          ('set subscript','Sd={uj','S0={uj'),('rank definition','205−199d','205+199d'),
                          ('pass domain','434−2a+b(a,b=0,1)','434−2a+b(a,b=0,1,2)'),
                          ('copy coordinate','(drd,q,b,','((1−d)rd,q,b,'),
                          ('cleanup label','(0,432a+b,0,438)','(0,431a+b,0,438)'),
                          ('terminal square','(a2,437,b,437)','(a,437,b,437)'),
                          ('payload sign','v(t)=234−w','v(t)=234+w'),
                          ('flag parentheses','Fq=14+mq(D16(E0,τq)−14)','Fq=14+mqD16(E0,τq)−14')]:
        need(expected.count(old)==1,'one full native glyph corruption '+label)
        try:core.compare_native_glyphs(expected.replace(old,new))
        except ValueError:glyph_controls.append(label)
        else:raise ValueError('accepted compact full glyph corruption '+label)
    need(len(rejected)==47 and len(scope_rejected)==14 and len(positives)==8 and len(glyph_controls)==9,
         'all complete compact recipe/control families retained')
    return {'actual_recipe_negative':rejected,'actual_recipe_scope_negative':scope_rejected,
            'valid_recipe_algebra':[label for label,old,new in positives],'complete_native_glyph_negative':glyph_controls}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source-only',action='store_true');ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();pins=authenticate();old=configure()
    old.source_index();packet=load(PAGE/'polynomial.json');historical=load(PAGE/'fixed/source54-p66.json')
    need((PAGE/'polynomial.json').read_bytes()==(PARENT/'polynomial.json').read_bytes(),'entire accepted polynomial bytes')
    need((PAGE/'COEFFICIENT_BINDING.json').read_bytes()==(PARENT/'COEFFICIENT_BINDING.json').read_bytes(),'entire accepted coefficient binding bytes')
    definitions,counts=old.circuit(packet,historical);bound=old.binding(packet)
    cal=load(PAGE/'CALIBRATION_BINDING.json');old.calibration(cal)
    expected_cal=load(PARENT/'CALIBRATION_BINDING.json');expected_cal['proof_sha256']=digest((PAGE/'PROOF.md').read_bytes())
    need(cal==expected_cal,'entire calibration changed only in local proof hash')
    seed=(PAGE/'SEED.txt').read_text().strip()
    need((PAGE/'SEED.txt').read_bytes()==(PARENT/'SEED.txt').read_bytes()==(INDEXED/'SEED.txt').read_bytes(),'entire original436 seed')
    tex=(PAGE/'equation.tex').read_text();delimiters=math_delimiter_controls(tex);native=native_audit(tex)
    body=tex.split(MARKER,1)[1];cuts,math,box,_=old.tex_audit(tex,packet,historical,body,seed)
    mapping=load(PAGE/'FORMULA_MAP.json')
    need((PAGE/'FORMULA_MAP.json').read_bytes()==(PARENT/'FORMULA_MAP.json').read_bytes() and
         mapping['assignments']==cuts+[{'tex_lhs':'BOX','literal_register':'polynomial'}] and
         mapping['historical_source_sha256']==digest((PAGE/'fixed/source54-p66.json').read_bytes()) and
         mapping['operations']==66 and mapping['exact_degree']==157 and mapping['operation_counts']==counts,'whole23 actual arithmetic cuts/map')
    degree=old.degree_audit(definitions);front_negative,front_positive=old.controls(tex,packet,historical,body,seed,cal)
    inherited=native_controls(tex);compact=recipe_controls(tex);hyphens=core.front_hyphen_controls()
    pdf=None if args.source_only else core.pdf_audit()
    result={'status':'PASS','optimized_python':bool(sys.flags.optimize),'mode':'source/actual-TeX only' if args.source_only else 'complete actual compact page',
            'operations':66,'operation_counts':counts,'exact_degree':157,'all66_rows_live_and_covered':True,
            'all15_positive_unknowns_and4_ports_live':True,'actual_polynomial_cuts':cuts+[{'tex_lhs':'BOX','literal_register':'polynomial'}],
            'degree_proof':degree,'whole_native_recipe':native,'whole_indexed_binding':bound,
            'accepted_front_negative_controls':front_negative,'accepted_front_valid_controls':front_positive,
            'inherited_native_controls':inherited,'actual_compact_controls':compact,'PDF_audited':not args.source_only,'actual_PDF':pdf,
            'complete_front_hyphenation_controls':hyphens,'actual_TeX_math_delimiter_controls':delimiters,
            'source_pins_sha256':digest((PAGE/'SOURCE_PINS.json').read_bytes()),'auditor_sha256':digest(Path(__file__).read_bytes()),
            'local_core_sha256':digest((PAGE/'GROUPED_CORE.py').read_bytes()),'local_recipe_sha256':digest((PAGE/'RECIPE_AUDIT.py').read_bytes()),
            'sha256':{n:digest((PAGE/n).read_bytes()) for n in ['equation.tex','polynomial.json','COEFFICIENT_BINDING.json','CALIBRATION_BINDING.json','SOURCE_INDEX.json','FORMULA_MAP.json','SEED.txt']},
            'scope':'Same accepted complete P66 and all four indexed943 integers; actual full recipe scopes/algebra/actions/tuples/Phi/support/rawbytes; no new calibration or formal-kernel proof and no main-page promotion.'}
    if not args.source_only:result['sha256']['equation.pdf']=digest((PAGE/'equation.pdf').read_bytes())
    raw=encoded(result)
    protected={(ROOT/n).resolve() for group in ['external_files','own_core'] for n in pins[group]}
    protected|={(PAGE/n).resolve() for n in ['SOURCE_PINS.json','HOLD_INVENTORY.json','MANIFEST.json','polynomial.json','COEFFICIENT_BINDING.json','CALIBRATION_BINDING.json','SOURCE_INDEX.json','equation.pdf','equation.txt','RENDER.txt','TEX_DIAGNOSTICS.txt','RENDER_DATA.json']}
    need(args.output.resolve()!=ROOT.parents[1].resolve() and ROOT.parents[1].resolve() not in args.output.resolve().parents,'receipt outside whole repository')
    need(not args.output.is_symlink() and args.output.resolve() not in protected and (not args.output.exists() or args.output.read_bytes()==raw),'fresh or byte-identical separate audit receipt')
    args.output.write_bytes(raw);print(raw.decode(),end='')


if __name__=='__main__':main()
