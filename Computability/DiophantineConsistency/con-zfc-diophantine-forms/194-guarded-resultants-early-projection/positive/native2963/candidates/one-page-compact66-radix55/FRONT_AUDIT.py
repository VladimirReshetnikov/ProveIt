#!/usr/bin/env python3
"""HOLD: full actual radix55 recipe, coherent tuple, P66 and PDF audit."""
import argparse
from collections import defaultdict
from copy import deepcopy
from fractions import Fraction
import gzip
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
PAGE=ROOT/'candidates/one-page-compact66-radix55'
PARENT=ROOT/'candidates/one-page-fifteen66'
COMPACT=ROOT/'candidates/one-page-compact66'
INDEXED=ROOT/'research/indexed-tile-enumeration'
MARKER=r'\textbf{The four fixed integers.}'
ALPHABET='0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
WRAP='e5cf81f0fd5ccf00f354050aca05570074a616c8dbadeb961f34042dfb80796a'
UNITS='876626ac37c31d50bc57b4e1f232b605728d867791e27d34751a3cc8d4284890'


def need(ok,message):
    if not ok:raise ValueError(message)


def bootstrap():
    def unique(items):
        out={}
        for k,v in items:
            need(k not in out,'duplicate bootstrap JSON key');out[k]=v
        return out
    for item in [PAGE/'SOURCE_PINS.json',PAGE/'guard.py']:
        need(item.is_file() and not item.is_symlink() and all(not p.is_symlink() for p in item.parents),
             'regular bootstrap input without symbolic path components')
    pins=json.loads((PAGE/'SOURCE_PINS.json').read_bytes(),object_pairs_hook=unique)
    path=PAGE/'guard.py';raw=path.read_bytes()
    pin=pins['own_core'][path.relative_to(ROOT).as_posix()]
    need(type(pin) is dict and set(pin)=={'bytes','sha256'} and type(pin['bytes']) is int and
         type(pin['sha256']) is str and re.fullmatch('[0-9a-f]{64}',pin['sha256']),'strict bootstrap guard byte/hash schema')
    need(not path.is_symlink() and all(not p.is_symlink() for p in path.parents) and
         pin=={'bytes':len(raw),'sha256':sha256(raw).hexdigest()},
         'whole reviewed guard before any local import')
    spec=importlib.util.spec_from_file_location('held_radix55_audit_guard',path)
    need(spec is not None and spec.loader is not None,'reviewed guard specification')
    g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g);return g


def imported(path,name):
    # Complete own/direct/whole closure authentication precedes all three calls.
    spec=importlib.util.spec_from_file_location(name,path)
    need(spec is not None and spec.loader is not None,'reviewed adopted module specification')
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module


def configure():
    global core,recipe,old,ORIGINAL_CIRCUIT
    core=imported(COMPACT/'GROUPED_CORE.py','reviewed_radix55_laurent_core')
    recipe=imported(COMPACT/'RECIPE_AUDIT.py','reviewed_radix55_recipe_parser')
    old=imported(PARENT/'FRONT_AUDIT.py','reviewed_radix55_arithmetic_front')
    core.ROOT=ROOT;core.PAGE=PAGE;core.PARENT=PARENT;core.INDEXED=INDEXED
    old.ROOT=ROOT;old.PAGE=PAGE;old.PRESERVED=PARENT;old.INDEXED=INDEXED
    ORIGINAL_CIRCUIT=old.circuit;old.circuit=circuit
    old.binding=lambda packet:binding(packet['coefficient_binding'],packet,CURRENT_VALUES)
    old.calibration=calibration
    core.glyphs=glyphs;core.prose_hyphen_words=prose_hyphen_words
    core.expected_native_glyphs=expected_native_glyphs
    canonical=core.Native
    class Radix55Native(canonical):
        def __init__(self,phi,tiles):
            self.rho=1<<55;self.B=1<<(55*8807)
            need(len(tiles)==943 and all(type(t) is list and len(t)==4 and
                 all(type(c) is int and 0<=c<=438 for c in t) for t in tiles),'all943 ordered typed labels')
            self.values=[w+(n<<8)+(e<<17)+(s<<25)+(127<<34) for w,n,e,s in tiles]
            need(all(127*(1<<34)<=v<(1<<41) for v in self.values),'all943 canonical payload bounds')
            self.phi=phi;self.numeric_phi={};self.digits=[]
            self.numeric_variables={'rho':self.rho,'B':self.B,'beta':self.B-1,
                                    'Lambda':self.rho**4393+self.rho**5495}
            coeff=defaultdict(int)
            for (e,vs),c in phi.items():
                for i in vs:c*=self.values[i]
                coeff[e]+=c
            self.coefficients={e:c for e,c in coeff.items() if c}
            need(all(0<=e<=3296 and 0<c<self.rho for e,c in self.coefficients.items()),'all complete55 Phi digit bounds')
        def formal(self,node,env=None):
            if node[0]=='payload':
                env={} if env is None else env;i=env['i']
                need(type(i) is int and 0<=i<943,'lexical complemented payload index')
                return core.add(core.const(1<<41),{(0,(i,)):1},-1)
            return super().formal(node,env)
        def number(self,node,env=None):
            if node[0]=='payload':
                env={} if env is None else env;i=env['i']
                need(type(i) is int and 0<=i<943,'numeric complemented payload index')
                return (1<<41)-self.values[i]
            return super().number(node,env)
    core.Native=Radix55Native


def typed_equal(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return set(a)==set(b) and all(typed_equal(a[k],b[k]) for k in a)
    if type(a) is list:return len(a)==len(b) and all(typed_equal(x,y) for x,y in zip(a,b))
    return a==b


def circuit(packet,historical):
    expected=g.load(COMPACT/'polynomial.json')
    need(type(packet) is dict and set(packet)==set(expected) and
         all(typed_equal(packet[k],expected[k]) for k in expected if k!='coefficient_binding'),
         'entire typed accepted free-port P66 metadata and all literal rows')
    return ORIGINAL_CIRCUIT(packet,historical)


def coordinate_cut(tex):
    header=r'\text{tile }t_i=(w_i,n_i,p_i,s_i)'
    if tex.count(header)!=1:raise recipe.RecipeContextError('RECIPE_CONTEXT: four distinct indexed coordinate bindings w_i,n_i,p_i,s_i')
    slots,_=core.native_slots(tex.split(MARKER,1)[1]);rhs=slots['Phi']
    boundary=r'&+2^{10}x^{1003}'
    need(rhs.count(boundary)==1,'complete selector/control boundary')
    selector,tail=rhs.split(boundary,1)
    clean=selector.replace(r'\\','').replace('&','').strip()
    m=re.fullmatch(r'\\sum_\{i=(.*?)\}\^\{(.*?)\}\((.*)\)x\^i',clean,re.S)
    need(m is not None,'entire actual direct-coordinate selector')
    for raw,wanted in [(m[1],0),(m[2],942)]:
        tree=recipe.context(recipe.parse(raw),label='fixed selector bound')
        need(recipe.polynomial(tree)==recipe.pc(wanted),'whole selector finite bound')
    coefficient=m[3];coordinates={'w':'w','n':'n','p':'e','s':'s'}
    pattern=r'([wnps])_(?:i|\{i\})'
    remainder=re.sub(pattern,'',coefficient)
    if re.search(r'[A-Za-z_\\]',remainder):
        raise recipe.RecipeContextError('RECIPE_CONTEXT: selector: only four coordinate families at its bound i')
    converted=re.sub(pattern,lambda z:coordinates[z[1]],coefficient)
    tree=recipe.context(recipe.parse(converted),{'w','n','e','s'},label='direct-coordinate coefficient')
    expected={():1+(1<<44),('w',):-(1<<10),('n',):-(1<<18),('e',):-(1<<27),('s',):-(1<<35)}
    need(recipe.polynomial(tree)==expected,'whole direct coefficient in four independent coordinates')
    # Only after the universal proof replace this complete semantic cut. The
    # synthetic v is the accepted complement, never an unparsed printed field.
    newrhs=r'G_{943}(x)+2^{10}\sum_{i=0}^{942}v(t_i)x^i\\'+'\n'+boundary+tail
    virtual=tex.replace(slots['Phi'],newrhs,1).replace(header,r'\text{tile }t_i=(w,n,e,s)')
    payload='For $t=(w,n,e,s)$ put\n\\[\nv(t)=2^{34}-w-2^8n-2^{17}e-2^{25}s.\n\\]\n\n'
    anchor=r'\textbf{A closed decoder for the 430 actions.}'
    need(virtual.count(anchor)==1,'one semantic payload insertion location')
    return virtual.replace(anchor,payload+anchor),{'all_four_coordinate_families_bound':True,
        'whole_independent_coordinate_identity':True,'selector_indices':[0,942],'seed_e_j_and_E0_distinct_from_p_i':True}


def old_phi_route():
    record=g.load(COMPACT/'COEFFICIENT_BINDING.json');values={};total=0
    for name,p in record['ports'].items():
        blob=(COMPACT/'coefficients'/p['file']).read_bytes();raw=gzip.decompress(blob)
        value=int.from_bytes(raw,'little');total+=len(raw)
        need(g.digest(blob)==p['gzip_sha256'] and g.digest(raw)==p['raw_sha256'] and value.bit_length()==p['bits'] and
             raw==value.to_bytes((p['bits']+7)//8,'little'),'all old67 raw provenance bytes '+name)
        values[name]=value
    need(total==295388,'all295388 old raw bytes retained only as provenance')
    residual=values['K0']-sum(1<<(67*e) for e in [30,62,1100,2201,8849])
    quotient,remainder=divmod(residual,1<<(67*1097));need(remainder==0,'old K first complete exact Phi factor')
    reverse,remainder=divmod(quotient,1+(1<<(67*1102)));need(remainder==0,'old K second complete exact Phi factor')
    digits=[]
    for _ in range(3297):digits.append(reverse&((1<<67)-1));reverse>>=67
    need(reverse==0,'whole reversed old Phi has no omitted high digits')
    return list(reversed(digits))


def native_audit(tex):
    virtual,coordinate=coordinate_cut(tex)
    reference,_=coordinate_cut((PAGE/'equation.tex').read_text())
    normalized,record=recipe.audit(virtual,reference,g.load(INDEXED/'TILES.json'),(PAGE/'SEED.txt').read_text().strip(),ALPHABET)
    body=normalized.split(MARKER,1)[1];slots,skeleton=core.native_slots(body)
    need(r'\mathcal E' not in body and r'\mathcal C' not in body and 'v(t)=' not in tex,'no hidden E/C/payload table in printed page')
    # These complete printed definitions are consumed before interpreting the
    # five native ASTs. Distinct global and local variable contexts are retained.
    definitions=re.search(r'\\rho=(.*?),\\quad B=(.*?),\\quad\\beta=(.*?),\\\\\nG_m\(x\)=(.*?),\\quad\n\\Lambda=',body,re.S)
    need(definitions is not None,'entire actual rho/B/beta/G definitions')
    for actual,wanted in zip(definitions.groups()[:3],[r'2^{55}',r'\rho^{8807}','B-1']):
        need(core.parse(actual)==core.parse(wanted),'complete actual55 radix/base/beta definition')
    need(definitions[4]==r'\sum_{j=0}^{m-1}x^j','complete fixed geometric function definition')
    need(skeleton==core.native_slots(reference.split(MARKER,1)[1])[1],
         'entire unchanged943 table/action/seed/footer and actual radix/G skeleton')
    trees={name:core.parse(rhs) for name,rhs in slots.items()};contexts=core.native_contexts(trees)
    expected,triples=core.expected_phi();tiles=g.load(INDEXED/'TILES.json');work=core.Native(expected,tiles)
    need(work.formal(trees['Phi'])==expected,'all943 independent actual Phi selectors and41 control coefficients')
    actual=[work.coefficients.get(e,0) for e in range(3297)]
    need(actual==old_phi_route(),'all3297 coefficients from actual new recipe versus independent old K factors')
    evidence=g.load(ROOT/'research/compact66-radix55-unit-probe-verification/captures/compact66-radix55-unit-probe-normal.json')
    need(evidence['phi']['canonical_array_sha256']==g.digest(g.encoded(actual)),'whole Phi array bound to accepted finite unit evidence')
    Lambda=work.formal(trees['Lambda']);need(Lambda=={(4393,()):1,(5495,()):1},'entire actual Lambda definition')
    native={name:work.formal(trees[name]) for name in ['MC','MF','K']}
    support=set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296}
    need(set(work.coefficients)==support-{1063,1064} and len(support)==986,'complete support with dummy holes')
    mc={(8807,()):1,(0,()):-1}
    for e in support-{1}:mc=core.add(mc,{(e,()):-1})
    mc=core.add(mc,{(1063,()):-2});need(native['MC']==mc,'entire MC polynomial after all3297 digit indicators')
    need(len(work.digits)==3297 and [e for b,e,d in work.digits]==list(range(3297)) and
         all(b==work.rho and d==actual[e] for b,e,d in work.digits),'all actual radix55 digit extractions')
    positive=(r'B-1+4+(2^{51}-2)\Lambda+\rho^{1013}G_{10}(\rho)+\rho^{1065}G_9(\rho)'
              r'+\rho^{2195}+\rho^{3296}+(\rho-1)\rho^{8792}G_{15}(\rho)+(2^{41}-4)\rho^{7691}')
    need(native['MF']==work.formal(core.parse(positive)),'full actual telescoped MF equals independent positive padding plus one beta')
    k=r'\rho^{30}+\rho^{62}+\rho^{1100}+\rho^{2201}+\rho^{8849}+\Lambda\Phi(1/\rho)'
    need(native['K']==work.formal(core.parse(k)),'entire actual K over943 independent canonical payloads')
    values={'beta':work.B-1}
    for name,poly in native.items():
        coeff=defaultdict(int)
        for (e,vs),c in poly.items():
            need(e>=0,'all final native powers integral')
            for i in vs:c*=work.values[i]
            coeff[e]+=c
        value=0
        for e in range(max(coeff),-1,-1):value=value*work.rho+coeff.get(e,0)
        values['K0' if name=='K' else name]=value
    base=work.B;beta=values['beta'];mf=values['MF']-beta
    units=[]
    for prime,wanted in [(5,0),(8807,3422),(581197,500242)]:
        residue=(1+base*values['K0']+base*base)%prime
        need(residue==wanted and (prime==5 or residue!=0),'actual new55 whole-K controller bound to accepted units')
        units.append({'prime':prime,'Hctrl_residue':residue,'unit_required':prime!=5})
    dc=values['K0']-work.rho**8849
    need(0<dc<base and 0<values['MC']<beta and 0<mf<beta and values['MC']%4==2 and mf%8==4,
         'complete source/native scalar boxes and low phases')
    need(values['MC'].bit_count()==55*8807-986 and mf.bit_count()==986,'both full mask populations')
    padding=(work.rho-1)*sum(work.rho**e for e in range(8792,8807))+(2**41-4)*work.rho**7691
    bits={55*e+b for e in range(8792,8807) for b in range(55)}|{55*7691+b for b in range(2,41)}
    need(len(bits)==864 and padding==sum(1<<b for b in bits) and not ((mf-padding)&padding),
         'all864 exact padding bit positions and disjoint native mask support')
    dc_cells={30,62,1100,2201}|{a-e for a in [4393,5495] for e in work.coefficients}
    need(max(dc_cells)+max(support)==8791 and all(not (7691<=a+e<=7695) for a in dc_cells for e in support) and
         max({42+e for e in support})<7691 and max(support)<7691,
         'entire zero-convolution band/tail and spatial/temporal padding separation')
    return values,{'coordinate_proof':coordinate,'actual_recipe':record,'native_contexts':contexts,
        'all943_formal_selectors':True,'all41_controls':True,'all3297_digit_and_dual_Phi_coefficients':True,
        'all_five_native_definitions_proved':True,'all864_padding_positions_and_zero_convolution_band':True,
        'native_populations':[values['MC'].bit_count(),mf.bit_count()],'source_MF_shift_exactly_once':True,
        'actual_whole_K_controller_residues':units}


def binding(record,packet,values,overrides=None):
    overrides={} if overrides is None else overrides
    expected={'schema':'whole_radix55_p66_binding_v1','path':'coefficients/','ports':record.get('ports'),
              'raw_bytes':record.get('raw_bytes'),'tuple':'same indexed BFS943; coherent wrapping-controller radix55; MF_source shifted once',
              'ordinary_proof':'PROOF.md','indexed_seal':'e077a476c38cb9abd96217887d16b011f6f5e16847036702720d69fcf91b1f84',
              'wrap_seal':WRAP,'unit_evidence_seal':UNITS}
    need(typed_equal(record,expected) and typed_equal(packet['coefficient_binding'],record),'entire new55 binding association/schema')
    need(type(record['raw_bytes']) is int and record['raw_bytes']>0 and type(record['ports']) is dict and
         set(record['ports'])=={'beta','K0','MC','MF'},'exact four typed new55 ports')
    files={'beta':'beta.bin.gz','K0':'K.bin.gz','MC':'MC.bin.gz','MF':'MF_source.bin.gz'};total=0;records={}
    for name,p in record['ports'].items():
        need(type(p) is dict and set(p)=={'file','bits','gzip_sha256','raw_sha256'} and p['file']==files[name] and
             type(p['bits']) is int and p['bits']>0 and all(type(p[k]) is str and re.fullmatch('[0-9a-f]{64}',p[k]) for k in ['gzip_sha256','raw_sha256']),
             'strict complete port schema '+name)
        blob=overrides[name] if name in overrides else (PAGE/'coefficients'/p['file']).read_bytes();raw=gzip.decompress(blob)
        value=int.from_bytes(raw,'little');total+=len(raw)
        need(g.digest(blob)==p['gzip_sha256'] and g.digest(raw)==p['raw_sha256'] and value.bit_length()==p['bits'] and
             raw==value.to_bytes((p['bits']+7)//8,'little') and gzip.compress(raw,compresslevel=9,mtime=0)==blob,'whole canonical compressed/raw port '+name)
        need(value==values[name],'every raw byte equals actual printed new55 constant '+name)
        records[name]={'bytes':len(raw),'sha256':g.digest(raw),'bits':p['bits']}
    need(total==record['raw_bytes'],'complete four-port raw byte census')
    return {'whole_raw_bytes':total,'ports':records,'new55_coherent_specialization':True,'old67_specialized_identity_claimed':False}


def calibration(record):
    expected={'schema':'whole_radix55_p66_calibration_v1','historical_free_port_source':'fixed/source54-p66.json',
         'historical_sha256':g.digest((PAGE/'fixed/source54-p66.json').read_bytes()),'all_arithmetic_rows_unchanged':True,
         'old_and_new_specialized_polynomials_identified':False,'all_four_ports_bound_together':True,
         'source_interface':'whole radix55 wrapping-controller positive native source; fresh canonical R=3 mod4',
         'soundness_map':'T_old=f*T; retain every other positive input and all current radix55 ports',
         'completeness_map':'fresh V=chi_S(R)/S,y=psi_S(R),T=(V+c+R*f^2)/(c*f^2)',
         'fresh_native_and_rank_witnesses':True,'wrap_seal':WRAP,'unit_evidence_seal':UNITS,
         'binding_sha256':g.digest((PAGE/'COEFFICIENT_BINDING.json').read_bytes()),'proof_sha256':g.digest((PAGE/'PROOF.md').read_bytes()),
         'raw_port_bytes':g.load(PAGE/'COEFFICIENT_BINDING.json')['raw_bytes'],
         'scope':'Ordinary composed calibration; finite programs bind this instance, not the unbounded proof or consistency.'}
    need(typed_equal(record,expected),'entire ordinary55 calibration and both complete positive maps')


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


def expected_native_glyphs():
    # Start with every glyph of the accepted actual complete compact suffix.
    # These are the complete changed streams, not a subset of target tokens.
    text=glyphs((COMPACT/'equation.txt').read_text().split('The four fixed integers.',1)[1])
    def replace(a,b):
        nonlocal text
        need(text.count(a)==1,'one complete prescribed native glyph replacement '+a[:45]);text=text.replace(a,b)
    replace('ρ=267,','ρ=255,')
    a=text.index('MF=');b=text.index('K=',a)
    oldmf=('MF=B−1+4+(251−2)Λ+ρ1013G10(ρ)+ρ1065G9(ρ)+ρ2195+ρ3296'
           '+(265−1)ρ8792G13(ρ)+(219−1)ρ8805,')
    need(text[a:b]==oldmf,'entire actual accepted old MF glyph stream')
    text=text[:a]+('MF=2B+3+(251−2)Λ+ρ1013G10(ρ)+ρ1065G9(ρ)+ρ2195+ρ3296'
                  '−ρ8792+(241−4)ρ7691,')+text[b:]
    replace('Φ(x)=G943(x)+210X942i=0v(ti)xi',
            'Φ(x)=X942i=0(1+244−210wi−218ni−227pi−235si)xi')
    replace('tileti=(w,n,e,s)','tileti=(wi,ni,pi,si)')
    replace('Fort=(w,n,e,s)putv(t)=234−w−28n−217e−225s.','')
    return text


def math_delimiter_controls(tex):
    regions=core.tex_math_regions(tex)
    counts={label:sum(m[group] is not None for m in regions)
            for label,group in [('display',1),('inline',2),('align',3)]}
    need(counts=={'display':8,'inline':16,'align':1} and len(regions)==25,'all25 actual TeX math regions after payload deletion')
    first=next(m for m in regions if m[1] is not None)
    need(tex[:first.start()].count('\n')+1==19,'actual first display on line19')
    for target in [r'\\[-1pt]','A complete fifteen-variable consistency equation','The only unknowns are']:
        need(tex.count(target)==1,'unique title/prose delimiter regression')
        a=tex.index(target);b=a+len(target)
        need(all(b<=m.start() or a>=m.end() for m in regions),'title linebreak and prose excluded from math')
    fixture=r'\\[-1pt] literal \$5; $x+\$y$ \[z\] \begin{align*}w\end{align*}'
    need([m[0] for m in core.tex_math_regions(fixture)]==[r'$x+\$y$',r'\[z\]',r'\begin{align*}w\end{align*}'],
         'same guarded helper escaped-dollar and linebreak regression')
    return {'counts':counts,'total':25,'first_display_line':19,'escaped_delimiter_fixture':True}


def native_controls(tex):
    cases=[('actual55 radix',r'\rho=2^{55}',r'\rho=2^{67}'),
        ('low mask sign',r'\beta+\rho-(\rho+3)',r'\beta-\rho-(\rho+3)'),
        ('dummy correction',r'(\rho+3)\rho^{1063}',r'(\rho+2)\rho^{1063}'),
        ('highest digit',r'\sum_{e=0}^{3296}',r'\sum_{e=0}^{3295}'),
        ('digit base',r'D_\rho(\Phi(\rho),e)',r'D_2(\Phi(\rho),e)'),
        ('indicator offset',r'+\rho-1)/\rho}',r'+2\rho-1)/\rho}'),
        ('selector common coefficient','(1+2^{44}-','(2+2^{44}-'),
        ('selector range',r'\sum_{i=0}^{942}',r'\sum_{i=0}^{941}'),
        ('first geometric length','G_8(2x)','G_7(2x)'),
        ('first control shift','x^{1003}(x^{20}+2^{17})','x^{1003}(x^{21}+2^{17})'),
        ('second control weight','2^{18}x^{983}','2^{19}x^{983}'),
        ('third control coefficient','x^{39}+2x^{30}+4x^{19}+8','x^{39}+2x^{30}+5x^{19}+8'),
        ('fourth control exponent','1+2x^{1100}+4x^{2201}','1+2x^{1100}+4x^{2200}'),
        ('Lambda exponent',r'\Lambda=\rho^{4393}+\rho^{5495}',r'\Lambda=\rho^{4393}+\rho^{5494}'),
        ('MF clause mask',r'(2^{51}-2)\Lambda',r'(2^{51}-1)\Lambda'),
        ('MF source shift once','M_F={}&2B+3','M_F={}&B+4'),
        ('MF telescope sign',r'-\rho^{8792}',r'+\rho^{8792}'),
        ('MF partial padding',r'(2^{41}-4)\rho^{7691}',r'(2^{40}-4)\rho^{7691}'),
        ('MF partial padding cell',r'(2^{41}-4)\rho^{7691}',r'(2^{41}-4)\rho^{7690}'),
        ('K reciprocal',r'\Lambda\Phi(1/\rho)',r'\Lambda\Phi(\rho)'),
        ('K whole-cell exponent',r'+\rho^{8849}',r'+\rho^{8848}'),
        ('unconsumed native token','G_8(2x)','G_8(2x)!')]
    rejected=[]
    for label,a,b in cases:
        need(tex.count(a)==1,'unique actual native corruption '+label)
        try:native_audit(tex.replace(a,b))
        except (ValueError,KeyError,IndexError,TypeError):rejected.append(label)
        else:raise ValueError('accepted actual native corruption '+label)
    scopes=[('Lambda self',r'\Lambda=\rho^{4393}+\rho^{5495}',r'\Lambda=\Lambda'),
        ('Phi self in control','G_8(2x)',r'\Phi(x)'),
        ('Phi global rho','G_8(2x)',r'G_8(2\rho)'),
        ('Lambda free x',r'\Lambda=\rho^{4393}+\rho^{5495}',r'\Lambda=x^{4393}+\rho^{5495}'),
        ('MF free x',r'\rho^{1013}G_{10}(\rho)',r'x^{1013}G_{10}(\rho)'),
        ('K free x',r'\Lambda\Phi(1/\rho)',r'\Lambda\Phi(1/x)'),
        ('MC unbound i',r'D_\rho(\Phi(\rho),e)',r'D_\rho(\Phi(\rho),i)'),
        ('MF unbound e',r'\rho^{2195}+\rho^{3296}',r'\rho^e+\rho^{3296}'),
        ('Phi unbound i','G_8(2x)','G_8(2ix)'),
        ('Phi unbound e','G_8(2x)','G_8(2ex)'),
        ('Phi nonfixed geometric bound','G_8(2x)','G_x(2x)'),
        ('Phi nonfixed exponent','x^{20}','x^x')]
    lexical=[]
    for label,a,b in scopes:
        need(tex.count(a)==1,'unique actual native scope mutation '+label)
        try:native_audit(tex.replace(a,b))
        except core.NativeContextError as error:lexical.append({'control':label,'error':str(error)})
        else:raise ValueError('accepted native lexical corruption '+label)
    positives=[('MC addition order',r'\beta+\rho-(\rho+3)',r'\rho+\beta-(\rho+3)'),
        ('Lambda addition order',r'\Lambda=\rho^{4393}+\rho^{5495}',r'\Lambda=\rho^{5495}+\rho^{4393}'),
        ('control addition order','x^{1003}(x^{20}+2^{17})','x^{1003}(2^{17}+x^{20})'),
        ('MF multiplication order',r'(2^{51}-2)\Lambda',r'\Lambda(2^{51}-2)'),
        ('K multiplication order',r'\Lambda\Phi(1/\rho)',r'\Phi(1/\rho)\Lambda'),
        ('MF exact telescope','M_F={}&2B+3','M_F={}&B+B+3')]
    for label,a,b in positives:
        need(tex.count(a)==1,'unique valid native algebra '+label);native_audit(tex.replace(a,b))
    need(len(rejected)==22 and len(lexical)==12 and len(positives)==6,'all native actual controls')
    return {'negative':rejected,'lexical':lexical,'valid':[a for a,b,c in positives]}


def recipe_controls(tex):
    mutants=[
        ('global direction domain','For $d=0,1$, let','For $d=0,1,2$, let'),
        ('head label','h(q,b)=2q+b+2','h(q,b)=2q+b+3'),
        ('set direction predicate','d_j=d,','d_j=1,'),
        # Action429 repeats289: this preserves the set but violates coverage.
        ('set action coverage/schema (duplicate preserving)',r'd_j=d,\ 0\le j<430',r'd_j=d,\ 0\le j<429'),
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
        ('direct coordinate sign','2^{44}-2^{10}w_i','2^{44}+2^{10}w_i'),
        ('direct coordinate constant','1+2^{44}-','1+2^{45}-'),
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
        ('direct coefficient free q','2^{10}w_i','2^{10}q'),
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
        ('direct coefficient term order','1+2^{44}-2^{10}w_i-2^{18}n_i','1+2^{44}-2^{18}n_i-2^{10}w_i'),
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
                          ('direct coordinate sign','244−210wi','244+210wi'),
                          ('flag parentheses','Fq=14+mq(D16(E0,τq)−14)','Fq=14+mqD16(E0,τq)−14')]:
        need(expected.count(old)==1,'one full native glyph corruption '+label)
        try:core.compare_native_glyphs(expected.replace(old,new))
        except ValueError:glyph_controls.append(label)
        else:raise ValueError('accepted compact full glyph corruption '+label)
    need(len(rejected)==47 and len(scope_rejected)==14 and len(positives)==8 and len(glyph_controls)==9,
         'all complete compact recipe/control families retained')
    return {'actual_recipe_negative':rejected,'actual_recipe_scope_negative':scope_rejected,
            'valid_recipe_algebra':[label for label,old,new in positives],'complete_native_glyph_negative':glyph_controls}


def artifact_controls(packet,cal,values,tex):
    rejected=[]
    def reject(label,reason,action):
        try:action()
        except (ValueError,KeyError,IndexError,TypeError) as error:
            need(reason in str(error),'specific artifact control rejection '+label+': '+str(error))
            rejected.append({'control':label,'reason':str(error)})
        else:raise ValueError('accepted actual-artifact corruption '+label)
    # Rebind all outer byte/bit/hash metadata to the actual corrupted bytes.
    # Every case still has to fail the mathematical whole-port comparison.
    for label,name,value in [('old67 K only','K0',int.from_bytes(gzip.decompress((COMPACT/'coefficients/K.bin.gz').read_bytes()),'little')),
                             ('K low bit','K0',values['K0']^1),('MC low bit','MC',values['MC']^1),
                             ('MF shift omitted','MF',values['MF']-values['beta']),
                             ('MF shift twice','MF',values['MF']+values['beta'])]:
        bad=deepcopy(packet);record=bad['coefficient_binding'];p=record['ports'][name]
        raw=value.to_bytes((value.bit_length()+7)//8,'little');blob=gzip.compress(raw,compresslevel=9,mtime=0)
        old_size=(p['bits']+7)//8;p.update(bits=value.bit_length(),gzip_sha256=g.digest(blob),raw_sha256=g.digest(raw))
        record['raw_bytes']+=len(raw)-old_size
        reject(label,'every raw byte equals actual printed new55 constant',
               lambda bad=bad,record=record,name=name,blob=blob:binding(record,bad,values,{name:blob}))
    for label,change,reason in [
        ('boolean bits',lambda r:r['ports']['beta'].__setitem__('bits',True),'strict complete port schema'),
        ('float bits',lambda r:r['ports']['beta'].__setitem__('bits',float(r['ports']['beta']['bits'])),'strict complete port schema'),
        ('missing whole port',lambda r:r['ports'].pop('MC'),'exact four typed new55 ports'),
        ('raw byte census',lambda r:r.__setitem__('raw_bytes',r['raw_bytes']+1),'complete four-port raw byte census'),
        ('old binding schema',lambda r:r.__setitem__('schema','whole_indexed_p66_binding_v1'),'entire new55 binding association/schema'),
        ('wrong wrap seal',lambda r:r.__setitem__('wrap_seal','0'*64),'entire new55 binding association/schema')]:
        bad=deepcopy(packet);change(bad['coefficient_binding'])
        reject(label,reason,lambda bad=bad:binding(bad['coefficient_binding'],bad,values))
    for label,key,value in [('false specialized identity','old_and_new_specialized_polynomials_identified',True),
                            ('wrong forward map','soundness_map','T_old=T'),
                            ('wrong inverse map','completeness_map','retain old67 witnesses'),
                            ('isolated source ports','all_four_ports_bound_together',False),
                            ('wrong units','unit_evidence_seal','0'*64),('wrong proof','proof_sha256','0'*64)]:
        bad=deepcopy(cal);bad[key]=value
        reject(label,'entire ordinary55 calibration',lambda bad=bad:calibration(bad))
    bad=deepcopy(packet);bad['auxiliary_gap']=0
    reject('integer masquerading as boolean metadata','entire typed accepted free-port P66',lambda:circuit(bad,g.load(PAGE/'fixed/source54-p66.json')))
    reject('duplicate actual source JSON key','duplicate JSON key',lambda:g.decode(b'{"operations":66,"operations":66}'))
    reject('nonfinite JSON value','nonfinite JSON constant',lambda:g.decode(b'{"operations":NaN}'))
    for label,a,b in [('east/seed collision',r't_i=(w_i,n_i,p_i,s_i)',r't_i=(w_i,n_i,e_i,s_i)'),
                      ('free coordinate index',r'2^{27}p_i',r'2^{27}p_j'),
                      ('unindexed positive input',r'2^{10}w_i',r'2^{10}w')]:
        need(tex.count(a)==1,'one new coordinate scope mutation')
        reject(label,'RECIPE_CONTEXT:',lambda a=a,b=b:native_audit(tex.replace(a,b)))
    valid=[]
    reverse=deepcopy(packet);reverse['coefficient_binding']['ports']=dict(reversed(list(reverse['coefficient_binding']['ports'].items())))
    binding(reverse['coefficient_binding'],reverse,values);valid.append('whole-port contribution order')
    need(typed_equal(g.decode(g.encoded(packet)),packet),'valid whole canonical source JSON round trip');valid.append('complete typed JSON round trip')
    need(len(rejected)==23 and len(valid)==2,'all new actual-artifact and binding controls')
    return {'negative':rejected,'valid':valid,'outer_metadata_rebound_for_five_complete_port_mutations':True}


def glyph_controls():
    expected=expected_native_glyphs();rejected=[]
    for label,a,b in [('radix','ρ=255','ρ=267'),('new MF source shift','MF=2B+3','MF=B+3'),
                      ('new padding exponent','ρ7691','ρ7690'),('new selector coordinate','227pi','227ei'),
                      ('new indexed header','(wi,ni,pi,si)','(wi,ni,ei,si)'),('Lambda glyph','Λ','L'),
                      ('control exponent','x1003','x1004'),('missing literal seed digit','BxEnhvy6Ni','BxEnhvy6N'),
                      ('constructor','(3,436,4,4)','(3,436,4,0)')]:
        need(a in expected,'actual whole native glyph control target '+label)
        try:core.compare_native_glyphs(expected.replace(a,b,1))
        except ValueError:rejected.append(label)
        else:raise ValueError('accepted complete native glyph corruption '+label)
    need(len(rejected)==9,'all nine additional complete native glyph corruptions');return rejected


def main():
    global g,CURRENT_VALUES
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--source-only',action='store_true');ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();g=bootstrap();g.authenticate(materialized=True);before=g.snapshot()
    role=('source-audit' if args.source_only else 'audit')+('-optimized' if sys.flags.optimize else '')
    g.receipt_path(role,args.output);configure()
    for name in ['polynomial.json','COEFFICIENT_BINDING.json','CALIBRATION_BINDING.json','SOURCE_INDEX.json']:
        need(g.encoded(g.load(PAGE/name))==(PAGE/name).read_bytes(),'entire strict canonical source JSON '+name)
    seed=(PAGE/'SEED.txt').read_text().strip()
    need((PAGE/'SEED.txt').read_bytes()==(COMPACT/'SEED.txt').read_bytes()==(INDEXED/'SEED.txt').read_bytes(),'whole unchanged436 seed file')
    packet=g.load(PAGE/'polynomial.json');historical=g.load(PAGE/'fixed/source54-p66.json')
    need((PAGE/'fixed/source54-p66.json').read_bytes()==(COMPACT/'fixed/source54-p66.json').read_bytes(),'entire historical free-port source bytes')
    definitions,counts=circuit(packet,historical);tex=(PAGE/'equation.tex').read_text()
    delimiters=math_delimiter_controls(tex);CURRENT_VALUES,native=native_audit(tex)
    bound=binding(g.load(PAGE/'COEFFICIENT_BINDING.json'),packet,CURRENT_VALUES)
    cal=g.load(PAGE/'CALIBRATION_BINDING.json');calibration(cal)
    body=tex.split(MARKER,1)[1];cuts,math,box,_=old.tex_audit(tex,packet,historical,body,seed)
    mapping=g.load(PAGE/'FORMULA_MAP.json')
    need((PAGE/'FORMULA_MAP.json').read_bytes()==(COMPACT/'FORMULA_MAP.json').read_bytes() and
         mapping['assignments']==cuts+[{'tex_lhs':'BOX','literal_register':'polynomial'}] and
         mapping['historical_source_sha256']==g.digest((PAGE/'fixed/source54-p66.json').read_bytes()) and
         mapping['operations']==66 and mapping['exact_degree']==157 and mapping['operation_counts']==counts,
         'whole23 actual arithmetic cuts and literal schedule map')
    degree=old.degree_audit(definitions)
    front_negative,front_valid=old.controls(tex,packet,historical,body,seed,cal)
    front_negative=[s.replace('binding: isolated historical K substitution','binding: corrupted whole-port raw hash') for s in front_negative]
    inherited=native_controls(tex);compact=recipe_controls(tex);artifacts=artifact_controls(packet,cal,CURRENT_VALUES,tex)
    native_glyphs=glyph_controls();hyphens=core.front_hyphen_controls()
    pdf=None if args.source_only else core.pdf_audit()
    g.unchanged(before)
    result={'status':'PASS','optimized_python':bool(sys.flags.optimize),'mode':'complete new55 source/actual TeX' if args.source_only else 'complete actual new55 page',
            'operations':66,'operation_counts':counts,'exact_degree':157,'all66_rows_live_and_covered':True,
            'all15_positive_unknowns_and4_ports_live':True,'actual_polynomial_cuts':cuts+[{'tex_lhs':'BOX','literal_register':'polynomial'}],
            'degree_proof':degree,'whole_native_recipe':native,'whole_new55_binding':bound,
            'accepted_front_negative':front_negative,'accepted_front_valid':front_valid,
            'native_controls':inherited,'compact_controls':compact,'new_artifact_controls':artifacts,
            'additional_native_glyph_negative':native_glyphs,'front_hyphenation_controls':hyphens,'math_delimiter_controls':delimiters,
            'PDF_audited':not args.source_only,'actual_PDF':pdf,'source_pins_sha256':g.digest((PAGE/'SOURCE_PINS.json').read_bytes()),
            'auditor_sha256':g.digest(Path(__file__).read_bytes()),'sha256':{n:g.digest((PAGE/n).read_bytes()) for n in
                ['equation.tex','polynomial.json','COEFFICIENT_BINDING.json','CALIBRATION_BINDING.json','SOURCE_INDEX.json','FORMULA_MAP.json','SEED.txt']},
            'scope':'New coherent radix55 tuple with accepted ordinary wrapping calibration and two bounded units; same literal free-port P66. No native/Lean replay, consistency decision, minimum or maintained-page promotion.'}
    if not args.source_only:result['sha256']['equation.pdf']=g.digest((PAGE/'equation.pdf').read_bytes())
    g.receipt(role,g.encoded(result),args.output)


if __name__=='__main__':main()
