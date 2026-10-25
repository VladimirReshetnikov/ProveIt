#!/usr/bin/env python3
"""Held independent actual-TeX, complete P66 source/degree and PDF audit.

No producer, project or incoming module import. Separate root release required.
"""
import argparse
from collections import Counter
from copy import deepcopy
import gzip
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
PAGE = ROOT/'candidates/one-page-fifteen66'
PRESERVED = ROOT/'candidates/one-page-doubled85'
INDEXED = ROOT/'research/indexed-tile-enumeration'
MARKER = r'\textbf{The four fixed integers.}'
ALPHABET = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
INPUTS = ['J','F','alpha','z','f','h','i','T','s','w','tau','eta','zeta','y','gamma']
PORTS = ['beta','K0','MC','MF']
REGISTERS = ['qm','q','C','X','Y','E','k','ell','c','a','H','Delta','main_root','R','V','normalized_S','N0','N1','Na','Nk','Nt','scaled_Ns','polynomial']
ALIASES = {r'q_-':'qm',r'\alpha':'alpha',r'\eta':'eta',r'\zeta':'zeta',r'\tau':'tau',r'\gamma':'gamma',r'\beta':'beta',r'\Delta':'Delta',r'\ell':'ell',r'M_C':'MC',r'M_F':'MF','D':'main_root','S':'normalized_S','K':'K0','N_0':'N0','N_1':'N1','N_a':'Na','N_k':'Nk','N_t':'Nt','N_s':'scaled_Ns'}
for _name in INPUTS+['q','C','X','Y','E','k','c','a','H','R','V']:
    ALIASES.setdefault(_name,_name)
SEALS = {'candidates/one-page-doubled85':'606d77c216f6464447f0682d4d0d26a35d5ddcbcc6f4d519929ad8871797ad48','research/indexed-tile-enumeration':'e077a476c38cb9abd96217887d16b011f6f5e16847036702720d69fcf91b1f84','research/ten-positive-index-weight':'cf3825ce1852236545c09bcf54e30ade41c8e79d3a5e9ace6ac61b08580d5d54'}


def need(ok,why):
    if not ok:
        raise ValueError(why)


def digest(raw):
    return sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value,indent=2,sort_keys=True)+'\n').encode()


def load(path):
    return json.loads(path.read_bytes())


def authenticate():
    pins = load(PAGE/'SOURCE_PINS.json')
    for group in ['external_files','own_core']:
        for name,pin in pins[group].items():
            path = ROOT/name
            raw = path.read_bytes()
            need(not path.is_symlink() and {'bytes':len(raw),'sha256':digest(raw)}==pin,'whole reviewed input '+name)
    need({d['folder']:d['manifest_sha256'] for d in pins['closed_dependencies']}==SEALS,'three exact whole calibrated contracts')
    for name,seal in SEALS.items():
        base = ROOT/name
        raw = (base/'MANIFEST.json').read_bytes()
        need(digest(raw)==seal,'whole calibrated seal')
        entries = json.loads(raw)['files']
        actual = {p.relative_to(base).as_posix() for p in base.rglob('*') if p.is_file() and p!=base/'MANIFEST.json'}
        need(actual==set(entries),'complete calibrated inventory')
        for relative,entry in entries.items():
            path = base/relative
            raw = path.read_bytes()
            expected = {'bytes':len(raw),'sha256':digest(raw)} if isinstance(entry,dict) else digest(raw)
            need(not path.is_symlink() and entry==expected,'whole calibrated member '+relative)
    return pins


def constant(value):
    return {(): value} if value else {}


def variable(name):
    return {(name,): 1}


def add(a, b, sign=1):
    out = dict(a)
    for monomial, coefficient in b.items():
        out[monomial] = out.get(monomial, 0)+sign*coefficient
    return {m: c for m, c in out.items() if c}


def multiply(a, b):
    out = {}
    for left, c in a.items():
        for right, d in b.items():
            monomial = tuple(sorted(left+right))
            out[monomial] = out.get(monomial, 0)+c*d
    return {m: c for m, c in out.items() if c}


def power(value, exponent):
    need(type(exponent) is int and exponent >= 0, 'fixed natural exponent')
    out = constant(1)
    for _ in range(exponent):
        out = multiply(out, value)
    return out


def tokens(text):
    result, position = [], 0
    ordered = sorted(ALIASES, key=len, reverse=True)
    while position < len(text):
        char = text[position]
        if char.isspace():
            position += 1
        elif char in '+-*^()[]{}':
            result.append(char)
            position += 1
        elif char.isdigit():
            match = re.match(r'\d+', text[position:])
            result.append(int(match[0]))
            position += len(match[0])
        else:
            name = next((k for k in ordered if text.startswith(k, position)), None)
            need(name is not None, 'entire polynomial TeX token '+text[position:])
            result.append(('variable', ALIASES[name]))
            position += len(name)
    return result


def parse(text, available):
    stream, position = tokens(text), 0

    def expression():
        nonlocal position
        value = product()
        while position < len(stream) and stream[position] in ['+', '-']:
            operator = stream[position]
            position += 1
            value = add(value, product(), 1 if operator == '+' else -1)
        return value

    def product():
        nonlocal position
        value = powered()
        while position < len(stream):
            token = stream[position]
            if token == '*':
                position += 1
                value = multiply(value, powered())
            elif type(token) is int or isinstance(token, tuple) or token in ['(', '[', '{']:
                value = multiply(value, powered())
            else:
                break
        return value

    def powered():
        nonlocal position
        value = primary()
        if position < len(stream) and stream[position] == '^':
            position += 1
            need(position < len(stream), 'complete exponent')
            exponent = stream[position]
            position += 1
            if exponent == '{':
                need(position+1 < len(stream), 'complete braced exponent')
                exponent = stream[position]
                need(stream[position+1] == '}', 'fixed exponent closing brace')
                position += 2
            value = power(value, exponent)
        return value

    def primary():
        nonlocal position
        need(position < len(stream), 'complete polynomial operand')
        token = stream[position]
        position += 1
        if type(token) is int:
            return constant(token)
        if isinstance(token, tuple):
            need(token[1] in available, 'previously proved abbreviation '+token[1])
            return variable(token[1])
        need(token in ['(', '[', '{'], 'group opening')
        value = expression()
        need(position < len(stream) and stream[position] == {'(': ')', '[': ']', '{': '}'}[token],
             'matching polynomial group')
        position += 1
        return value

    value = expression()
    need(position == len(stream), 'entire actual expression consumed')
    return value


def circuit(packet, historical):
    immutable = set(historical)-{'name','coefficient_binding','proof','proof_boundary'}
    need(set(packet)==set(historical) and all(packet[k]==historical[k] for k in immutable), 'whole66 literal rows, domain and unchanged metadata')
    need(packet['name']=='indexed_p66_degree157' and packet['proof']=='PROOF.md' and
         packet['proof_boundary']=='Whole indexed normalized-positive source and canonical R=3 mod4 composed with source54 section8; ordinary inherited calibration, no new formal-kernel certificate.', 'new whole-specialization provenance')
    need(packet['witnesses']==INPUTS and packet['fixed_numerals']==PORTS and packet['witness_domain']=='strictly positive integers' and packet['output']=='polynomial', 'all fifteen positive inputs and four free ports')
    definitions,known = {},set(INPUTS+PORTS)
    counts = dict(Counter(row[1] for row in packet['source']))
    need(len(packet['source'])==packet['operations']==66 and counts==packet['operation_counts']=={'*':38,'+':15,'-':13}, 'entire66-gate cost')
    for row in packet['source']:
        need(type(row) is list and len(row)==4, 'entire binary source row')
        name,op,a,b = row
        need(type(name) is str and name not in known and op in ['+','-','*'], 'fresh literal gate')
        need(all(type(v) is int or type(v) is str and v in known for v in [a,b]), 'strict complete source topology')
        definitions[name]=(op,a,b)
        known.add(name)
    live,todo = set(),['polynomial']
    while todo:
        name=todo.pop()
        if type(name) is int or name in live:
            continue
        live.add(name)
        todo.extend(definitions.get(name,('',))[1:])
    need(live==known,'all66 gates, all15 unknowns and all4 ports live')
    return definitions,counts


def binding(packet):
    expected_ports = load(PRESERVED/'polynomial.json')['coefficient_binding']['ports']
    record = load(PAGE/'COEFFICIENT_BINDING.json')
    need(record==packet['coefficient_binding'] and set(record)=={'schema','path','ports','raw_bytes','tuple','ordinary_proof','indexed_seal'}, 'whole emitted binding fields')
    need(record['schema']=='whole_indexed_p66_binding_v1' and record['path']=='coefficients/' and record['ports']==expected_ports and record['raw_bytes']==295388 and
         record['tuple']=='whole directly indexed BFS943; new P66 specialization; MF_source shifted once' and record['ordinary_proof']=='PROOF.md' and
         record['indexed_seal']==SEALS['research/indexed-tile-enumeration'], 'whole new indexed specialization')
    need(set(record['ports'])==set(PORTS),'exact four ports')
    values,total = {},0
    for name,pin in record['ports'].items():
        blob=(PAGE/'coefficients'/pin['file']).read_bytes()
        need(blob==(PRESERVED/'coefficients'/pin['file']).read_bytes()==(INDEXED/'coefficients'/pin['file']).read_bytes(), 'complete whole three-way payload '+name)
        raw=gzip.decompress(blob)
        value=int.from_bytes(raw,'little')
        need(digest(blob)==pin['gzip_sha256'] and digest(raw)==pin['raw_sha256'] and value.bit_length()==pin['bits'] and
             raw==value.to_bytes((pin['bits']+7)//8,'little'), 'canonical whole compressed/raw integer '+name)
        values[name]=value
        total+=len(raw)
    beta=values['beta']
    native_high=values['MF']-beta
    need(total==295388 and beta==(1<<590069)-1 and 0<values['MC']<beta and 0<native_high<beta and
         values['MC']%4==2 and native_high%8==4 and values['MC'].bit_count()+native_high.bit_count()==590069 and values['K0']>0,
         'whole normalized native masks, shift and radix premises')
    return record


def source_index():
    index=load(PAGE/'SOURCE_INDEX.json')
    need(set(index)=={'schema','files','producer_sha256','source_pins_sha256'} and index['schema']=='indexed_p66_source_inventory_v1', 'whole source inventory schema')
    need(set(index['files'])=={'polynomial.json','COEFFICIENT_BINDING.json','CALIBRATION_BINDING.json'}, 'all three complete generated source files')
    for name,pin in index['files'].items():
        path=PAGE/name
        raw=path.read_bytes()
        need(not path.is_symlink() and pin=={'bytes':len(raw),'sha256':digest(raw)}, 'whole indexed source file '+name)
    need(index['producer_sha256']==digest((PAGE/'build.py').read_bytes()) and index['source_pins_sha256']==digest((PAGE/'SOURCE_PINS.json').read_bytes()), 'actual reviewed producer and pins')
    return index


def calibration(record):
    expected={'schema':'whole_indexed_p66_calibration_v1','historical_free_port_source':'fixed/source54-p66.json',
              'historical_sha256':digest((PAGE/'fixed/source54-p66.json').read_bytes()),'all_arithmetic_rows_unchanged':True,
              'old_and_new_specialized_polynomials_identified':False,'all_four_ports_bound_together':True,
              'source_interface':'whole indexed normalized positive native source; fresh canonical R=3 mod4',
              'soundness_map':'T_old=f*T; retain every other positive input and all current indexed ports',
              'completeness_map':'fresh V=chi_S(R)/S,y=psi_S(R),T=(V+c+R*f^2)/(c*f^2)',
              'fresh_native_and_rank_witnesses':True,'closed_dependencies':SEALS,
              'proof_sha256':digest((PAGE/'PROOF.md').read_bytes()),'raw_port_bytes':295388,
              'scope':'Ordinary composed calibration; finite programs check literal binding, not the unbounded compiler proof or consistency.'}
    need(record==expected,'complete source calibration and both positive maps')


def degree_audit(definitions):
    degree=lambda monomial:sum(name in INPUTS for name in monomial)
    leading={name:(1 if name in INPUTS else 0,variable(name)) for name in INPUTS+PORTS}
    full={name:variable(name) for name in INPUTS+PORTS}
    def expand(name):
        if type(name) is int:
            return constant(name)
        if name not in full:
            op,a,b=definitions[name]
            left,right=expand(a),expand(b)
            full[name]=multiply(left,right) if op=='*' else add(left,right,1 if op=='+' else -1)
        return full[name]
    cancellations=[]
    for name,(op,a,b) in definitions.items():
        da,pa=(0,constant(a)) if type(a) is int else leading[a]
        db,pb=(0,constant(b)) if type(b) is int else leading[b]
        if op=='*':
            d,p=da+db,multiply(pa,pb)
        else:
            d=max(da,db)
            p=add(pa if da==d else {},pb if db==d else {},1 if op=='+' else -1)
        if not p:
            actual=expand(name)
            need(actual,'no identically-zero arithmetic node')
            d=max(map(degree,actual))
            p={m:c for m,c in actual.items() if degree(m)==d}
            cancellations.append({'node':name,'degree':d,'full_terms':len(actual)})
        need(p and all(degree(m)==d for m in p),'whole homogeneous leader at '+name)
        leading[name]=(d,p)
    q0=multiply(variable('beta'),variable('J'))
    k0=add(variable('eta'),variable('zeta'))
    tail=add(multiply(variable('w'),add(add(q0,variable('F'),-1),variable('alpha'),-1)),multiply(variable('z'),q0),-1)
    expected=constant(-8)
    for item,exponent in [(q0,91),(variable('h'),1),(variable('gamma'),1),(variable('i'),4),(k0,13),(variable('w'),13),(variable('s'),26),(variable('T'),2),(variable('f'),4),(tail,1)]:
        expected=multiply(expected,power(item,exponent))
    need(leading['polynomial']==(157,expected),'complete global degree157 leading form over four free ports')
    monomial=tuple(sorted(['J']*92+['h','gamma']+['i']*4+['eta']*13+['w']*13+['s']*26+['T']*2+['f']*4+['z']+['beta']*92))
    need(expected.get(monomial)==8,'actual coefficient8*beta^92 cannot vanish')
    need(cancellations==[{'node':'N1','degree':18,'full_terms':323}],'entire main-norm cancellation, no sampled degree claim')
    need([leading[n][0] for n in ['N0','N1','Na','Nk','Nt','scaled_Ns']]==[22,18,62,7,2,46],'all six exact factor degrees')
    return {'exact_degree':157,'factor_degrees':[22,18,62,7,2,46],'whole_leader_terms':len(expected),'distinguished_coefficient':'8*beta^92','cancellations':cancellations}


def tex_audit(tex,packet,historical,body,seed):
    need(tex.count(MARKER)==1 and tex.split(MARKER,1)[1]==body,'entire verbatim constant recipe/table/decoder/seed/footer')
    need(r'J,F,\alpha,z,f,h,i,T,s,w,\tau,\eta,\zeta,y,\gamma\in\mathbb Z_{>0}.' in tex,'actual ordered fifteen-positive domain')
    need('exact degree 157; a 66-operation evaluator.' in tex and r'\fontsize{9}{9.5}\selectfont' in tex,'actual printed metrics and unchanged body font')
    block=re.search(r'\\begingroup[^\n]*\\ttfamily\s*(.*?)\\endgroup',body,re.S)
    need(block and re.sub(r'\\par|\s','',block[1])==seed and len(seed)==436 and set(seed)<=set(ALPHABET) and body.count(ALPHABET)==1,'every seed and alphabet character')
    definitions,counts=circuit(packet,historical)
    front=tex.split('All other symbols in the equation are polynomial abbreviations:',1)[1].split(MARKER,1)[0]
    need(front.count(r'\begin{gathered}')==front.count(r'\end{gathered}')==front.count(r'\boxed{')==1,'one complete schedule and equation')
    before,rest=front.split(r'\begin{gathered}',1)
    math,after=rest.split(r'\end{gathered}',1)
    need(before.strip()==r'\[','no hidden preceding front formula')
    prefix='\\]\nThe single equation is\n\\[\n\\boxed{'
    need(after.strip().startswith(prefix),'exact equation display skeleton')
    boxed=after.strip()[len(prefix):]
    depth,stop=1,None
    for position,char in enumerate(boxed):
        depth+=(char=='{')-(char=='}')
        if depth==0:
            stop=position
            break
    need(stop is not None and boxed[stop+1:].strip()==r'\]','whole boxed body, no extra formula')
    box=boxed[:stop]
    clean=math
    for command in [r'\qquad',r'\quad',r'\\']:
        clean=clean.replace(command,' ')
    available,covered,assignments=set(INPUTS+PORTS),set(),[]
    def compare(target,wanted):
        memo={n:variable(n) for n in available}
        def expand(name):
            if type(name) is int:
                return constant(name)
            if name not in memo:
                need(name in definitions,'complete source dependency '+name)
                covered.add(name)
                op,a,b=definitions[name]
                left,right=expand(a),expand(b)
                memo[name]=multiply(left,right) if op=='*' else add(left,right,1 if op=='+' else -1)
            return memo[name]
        need(expand(target)==wanted,'exact actual-TeX free-port cut '+target)
    for statement in clean.split(','):
        statement=statement.strip()
        if not statement:
            continue
        need(statement.count('=')==1,'single actual displayed definition')
        lhs,rhs=statement.split('=')
        left=tokens(lhs.strip())
        need(len(left)==1 and isinstance(left[0],tuple),'single alias lhs')
        target=left[0][1]
        need(len(assignments)<22 and target not in available and target==REGISTERS[len(assignments)],'exact unique display order')
        expression=rhs.strip()
        if expression.endswith('.'):
            expression=expression[:-1]
        compare(target,parse(expression,available))
        available.add(target)
        assignments.append({'tex_lhs':lhs.strip(),'literal_register':target})
    need(len(assignments)==22 and box.count('=')==1,'all22 definitions and whole equation')
    lhs,rhs=box.split('=')
    need(rhs=='0.','entire zero equation')
    compare('polynomial',parse(lhs,available))
    need(covered==set(definitions),'every one of66 source rows covered by actual printed cuts')
    return assignments,math,box,counts


def controls(tex,packet,historical,body,seed,cal):
    mutants=[('wrong squared quotient','V=f^2(cT-R)-c','V=f(cT-R)-c'),('quotient sign','V=f^2(cT-R)-c','V=f^2(cT+R)-c'),
             ('missing normalized discriminant',r'S=i\Delta c^2','S=ic^2'),('wrong strong factor',r'N_s=\Delta f^2-S^2',r'N_s=f^2-S^2'),
             ('unscaled auxiliary',r'N_a=S^2(V^2-y^2)+y^2',r'N_a=S(V^2-y^2)+y^2'),('wrong first norm',r'N_0=\tau^2-\ell(\ell+k)',r'N_0=\tau^2-\ell(\ell-k)'),
             ('missing factor','N_0N_1N_aN_kN_tN_s-','N_0N_1N_aN_kN_t-'),('wrong final subtraction',r'N_s-\Delta=0.',r'N_s-1=0.'),
             ('wrong main root',r'D=X+ac+\gamma H',r'D=X+ac-\gamma H'),('wrong transport',r'-zq_-',r'+zq_-'),
             ('changed initializer','(3,436,4,4)','(3,436,4,0)'),('changed seed',seed[:10],('0' if seed[0]!='0' else '1')+seed[1:10]),
             ('wrong cost','a 66-operation evaluator.','a 65-operation evaluator.'),('wrong degree','exact degree 157;','exact degree 156;'),
             ('wrong domain',r'\mathbb Z_{>0}',r'\mathbb Z_{\ge0}'),('unparsed suffix','V=f^2(cT-R)-c','V=f^2(cT-R)-c!')]
    rejected=[]
    def reject(label,action):
        try:
            action()
        except (ValueError,KeyError,IndexError,TypeError):
            rejected.append(label)
        else:
            raise ValueError('accepted corruption '+label)
    for label,old,new in mutants:
        need(tex.count(old)==1,'unique actual TeX mutation '+label)
        reject('TeX: '+label,lambda old=old,new=new:tex_audit(tex.replace(old,new),packet,historical,body,seed))
    for label,change in [('actual row coefficient',lambda p:p['source'][0].__setitem__(2,2)),('domain metadata',lambda p:p.__setitem__('witness_domain','integers')),
                         ('missing live gate',lambda p:p['source'].pop()),('positive input removed',lambda p:p['witnesses'].pop()),
                         ('false gate count',lambda p:p.__setitem__('operations',65))]:
        bad=deepcopy(packet)
        change(bad)
        reject('source: '+label,lambda bad=bad:circuit(bad,historical))
    bad=deepcopy(packet)
    bad['coefficient_binding']['ports']['K0']['raw_sha256']='0'*64
    reject('binding: isolated historical K substitution',lambda:binding(bad))
    badcal=deepcopy(cal)
    badcal['old_and_new_specialized_polynomials_identified']=True
    reject('calibration: false old/new polynomial identity',lambda:calibration(badcal))
    wrongdefs=deepcopy(circuit(packet,historical)[0])
    wrongdefs['Na']=('*','aux_product','y2')
    reject('degree: changed full auxiliary factor',lambda:degree_audit(wrongdefs))
    positives=[tex.replace('V=f^2(cT-R)-c','V=(cT-R)f^2-c'),tex.replace('S=i\\Delta c^2','S=c^2i\\Delta'),
               tex.replace('H=4a+3','H=3+4a'),tex.replace('N_1=D^2-\\Delta c^2','N_1=D^2-c^2\\Delta')]
    for good in positives:
        tex_audit(good,packet,historical,body,seed)
    need(len(rejected)==24 and len(positives)==4,'all24 actual structural/TeX controls and4 valid identities')
    return rejected,len(positives)


def pdf_audit(math,box,seed):
    def extract(path):
        return subprocess.run(['pdftotext','-raw',str(path),'-'],check=True,capture_output=True,text=True,timeout=30).stdout
    pdf,prior=extract(PAGE/'equation.pdf'),extract(PRESERVED/'equation.pdf')
    compact=lambda text:re.sub(r'\s','',text)
    boundary='The four fixed integers.'
    need(pdf.count(boundary)==prior.count(boundary)==1 and compact(pdf.split(boundary,1)[1])==compact(prior.split(boundary,1)[1]),'whole actual native PDF suffix')
    def glyphs(text):
        for old,new in [(r'\qquad',''),(r'\quad',''),(r'\\',''),(r'\alpha','α'),(r'\eta','η'),(r'\zeta','ζ'),(r'\tau','τ'),(r'\gamma','γ'),(r'\beta','β'),(r'\Delta','∆'),(r'\ell','ℓ')]:
            text=text.replace(old,new)
        return compact(text).replace('_','').replace('^','').replace('{','').replace('}','').replace('-','−')
    actual=pdf.split('polynomial abbreviations:',1)[1].split(boundary,1)[0].replace('The single equation is','')
    need(compact(actual)==glyphs(math+box),'every actual displayed front glyph in order')
    signature=pdf.split('The only unknowns are',1)[1].split('All other symbols',1)[0]
    need(compact(signature)=='J,F,α,z,f,h,i,T,s,w,τ,η,ζ,y,γ∈Z>0.','every actual fifteen-input/domain glyph')
    need('exact degree 157; a 66-operation evaluator.' in pdf and seed in compact(pdf) and ALPHABET in compact(pdf),'actual PDF metrics/whole seed/alphabet')
    info=subprocess.run(['pdfinfo',str(PAGE/'equation.pdf')],check=True,capture_output=True,text=True,timeout=30).stdout
    need(re.search(r'Pages:\s+1\b',info) and '612 x 792' in info,'one actual Letter page')
    need(all('Overfull' not in (PAGE/n).read_text() for n in ['RENDER.txt','TEX_DIAGNOSTICS.txt']),'retained zero-overflow diagnostics')


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source-only',action='store_true')
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    pins=authenticate()
    source_index()
    historical=load(PAGE/'fixed/source54-p66.json')
    packet=load(PAGE/'polynomial.json')
    definitions,counts=circuit(packet,historical)
    bound=binding(packet)
    cal=load(PAGE/'CALIBRATION_BINDING.json')
    calibration(cal)
    seed=(PAGE/'SEED.txt').read_text().strip()
    need((PAGE/'SEED.txt').read_bytes()==(PRESERVED/'SEED.txt').read_bytes()==(INDEXED/'SEED.txt').read_bytes(),'whole seed file')
    body=(PRESERVED/'equation.tex').read_text().split(MARKER,1)[1]
    need(body==(INDEXED/'equation.tex').read_text().split(MARKER,1)[1],'whole two-parent native TeX body')
    tex=(PAGE/'equation.tex').read_text()
    assignments,math,box,_=tex_audit(tex,packet,historical,body,seed)
    mapping=load(PAGE/'FORMULA_MAP.json')
    need(mapping['assignments']==assignments+[{'tex_lhs':'BOX','literal_register':'polynomial'}] and mapping['historical_source_sha256']==digest((PAGE/'fixed/source54-p66.json').read_bytes()) and
         mapping['operations']==66 and mapping['exact_degree']==157 and mapping['operation_counts']==counts,'entire actual formula map')
    degree=degree_audit(definitions)
    negatives,positives=controls(tex,packet,historical,body,seed,cal)
    if not args.source_only:
        pdf_audit(math,box,seed)
    report={'status':'PASS','optimized_python':bool(sys.flags.optimize),'mode':'source/actual-TeX only' if args.source_only else 'complete actual page',
            'operations':66,'operation_counts':counts,'exact_degree':157,'all66_rows_live_and_covered':True,'all15_unknowns_and4_ports_live':True,
            'actual_polynomial_cuts':assignments+[{'tex_lhs':'BOX','literal_register':'polynomial'}],'degree_proof':degree,'whole_indexed_binding':bound,
            'ordinary_contract':'whole indexed normalized source plus canonical R=3 mod4; both positive maps; old/new specialized polynomials not equated',
            'actual_corruptions_rejected':negatives,'valid_algebra_controls':positives,'PDF_audited':not args.source_only,
            'source_pins_sha256':digest((PAGE/'SOURCE_PINS.json').read_bytes()),'auditor_sha256':digest(Path(__file__).read_bytes()),
            'sha256':{n:digest((PAGE/n).read_bytes()) for n in ['equation.tex','polynomial.json','COEFFICIENT_BINDING.json','CALIBRATION_BINDING.json','SOURCE_INDEX.json','FORMULA_MAP.json','SEED.txt']},
            'scope':'Literal new whole-indexed P66, all actual TeX cuts and exact free-port degree; ordinary compiler/calibration retained; no consistency decision or main-page promotion.'}
    if not args.source_only:
        report['sha256']['equation.pdf']=digest((PAGE/'equation.pdf').read_bytes())
    raw=encoded(report)
    protected={(ROOT/n).resolve() for group in ['external_files','own_core'] for n in pins[group]}
    protected|={(PAGE/n).resolve() for n in ['SOURCE_PINS.json','HOLD_INVENTORY.json','MANIFEST.json','polynomial.json','COEFFICIENT_BINDING.json','CALIBRATION_BINDING.json','SOURCE_INDEX.json','equation.pdf','equation.txt','RENDER.txt','TEX_DIAGNOSTICS.txt','RENDER_DATA.json']}
    need(not args.output.is_symlink() and args.output.resolve() not in protected and (not args.output.exists() or args.output.read_bytes()==raw),'separate fresh or identical audit receipt')
    args.output.write_bytes(raw)
    print(raw.decode(),end='')


if __name__=='__main__':
    main()


