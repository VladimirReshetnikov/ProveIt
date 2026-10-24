#!/usr/bin/env python3
"""Complete saturated-Pell ten-positive page with whole indexed constants."""
import argparse
import ast
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
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'candidates/one-page-saturated10'
OLD = ROOT/'research/indexed-tile-enumeration'
FRONT = ROOT/'research/ten-positive-saturated-pell'
ALPHABET = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
MARKER = r'\textbf{The four fixed integers.}'


def need(ok,message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value,indent=2,sort_keys=True)+'\n').encode()


def symbolic_binding(packet):
    """Exact shared terms modulo associative/commutative + and * only."""
    need(packet['operations'] == 92 and packet['exact_degree'] == 283,
         'accepted complete parent operation and degree metadata')
    terms = []
    pool = {}
    def intern(term):
        if term not in pool:
            pool[term] = len(terms)
            terms.append(term)
        return pool[term]
    def leaf(value):
        if type(value) is int:
            return intern(('integer',value))
        return intern(('symbol','K' if value == 'K0' else value))
    def op(tag,a,b):
        if tag == '-':
            return intern((tag,a,b))
        items = []
        constant = 0 if tag == '+' else 1
        for index in (a,b):
            value = terms[index]
            entries = value[1:] if value[0] == tag else (index,)
            for entry in entries:
                v = terms[entry]
                if v[0] == 'integer':
                    constant = constant+v[1] if tag == '+' else constant*v[1]
                else:
                    items.append(entry)
        if tag == '*' and constant == 0:
            return leaf(0)
        if constant != (0 if tag == '+' else 1) or not items:
            items.append(leaf(constant))
        if len(items) == 1:
            return items[0]
        return intern((tag,*sorted(items)))
    def power(x,n):
        need(type(n) is int and n >= 0,'fixed natural exponent')
        if n == 0:
            return leaf(1)
        if n == 1:
            return x
        y = power(x,n//2)
        z = op('*',y,y)
        return z if n % 2 == 0 else op('*',z,x)
    def parse(text,env):
        def go(node):
            if isinstance(node,ast.Name):
                return env[node.id]
            if isinstance(node,ast.Constant) and type(node.value) is int:
                return leaf(node.value)
            need(isinstance(node,ast.BinOp),'arithmetic formula syntax')
            if isinstance(node.op,ast.Pow):
                return power(go(node.left),node.right.value)
            return op({ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}[type(node.op)],go(node.left),go(node.right))
        return go(ast.parse(text,mode='eval').body)
    # These expressions are the complete displayed front, in display order.
    displayed = [
        ('bJ','beta*J'),('q','bJ+1'),('C','q-F-alpha'),
        ('X','w*q'),('k','eta+zeta'),('c','k*Y+eta'),
        ('mu','q**2+1'),('A','mu*Y*(X+1)'),('H','4*A-1'),
        ('Delta','A*(A+2)'),('U','i*c**2'),
        ('V0','X*(mu*Y)**2'),('ell','V0*k'),('E','ell*(ell+k)+1'),
        ('R','(bJ*(q-F)+alpha)*(q**2-1)+(MC+q*MF)*J'),
        ('e','k-R-1'),('Bt','(K+w)*C-F'),
        ('Df','1+Delta*U**2*E'),('Q','Delta**2*U**2*E'),('delta','Q-1'),
        ('Tp','T+alpha'),('bp','c*Tp-R'),('V','Df*bp-c'),
        ('Dy','Q*V**2-1'),('Kpos','X*(3*c-2*X)+2'),
        ('L','k*Tp'),('Cg','(A+2)*U*E'),
        ('P1','q**3*bJ'),('M','P1*mu**2*H'),
        ('Z','P1*mu**2*(H*(n+V+Cg-L*Bt)+Kpos)+H*(mu**2*(bJ*Y-q**3*Bt)-P1*e)'),
        ('S','delta*Z**2'),('Ag','delta*M**2*E*Df'),('Ay','M**2*Dy'),
        ('N','(S-(Ag+Ay))**2-4*Ag*Ay'),
    ]
    initial = packet['witnesses']+['beta','K','MC','MF']
    printed = {name:leaf(name) for name in initial}
    for name,text in displayed:
        printed[name] = parse(text,printed)
    actual = {name:leaf(name) for name in packet['witnesses']+packet['fixed_numerals']}
    for name,tag,a,b in packet['source']:
        actual[name] = op(tag,leaf(a) if type(a) is int else actual[a],leaf(b) if type(b) is int else actual[b])
    need(actual[packet['output']] == printed['N'],'complete displayed front equals all92 literal gates over free coefficients')
    counts = Counter(row[1] for row in packet['source'])
    need(len(packet['source']) == 92 and dict(counts) == {'*':55,'+':20,'-':17},'actual92-operation inventory')
    return dict(status='PASS',all92_gates_bound=True,method='Exact shared terms modulo associative/commutative ring + and *; no numerical substitution or expanded-polynomial hash inference.',
                printed_schedule=displayed,positive_unknowns=10,operations=92,degree=283,
                aliases=dict(K='K0',A='Am1',H='Hp',Delta='Delta',E='Dtau',Z='Znum',M='Mtot',S='fs',q_minus='bJ',K_2='Kpos'))


def build_data():
    OUT.mkdir(parents=True,exist_ok=True)
    parent_raw = (FRONT/'saturated_upper.json').read_bytes()
    parent = json.loads(parent_raw)
    source_manifest = json.loads((FRONT/'MANIFEST.json').read_bytes())['files']
    for name,pin in source_manifest.items():
        need(digest((FRONT/name).read_bytes()) == pin,'complete frozen saturated parent '+name)
    indexed_manifest = json.loads((OLD/'MANIFEST.json').read_bytes())['files']
    for name,pin in indexed_manifest.items():
        need(digest((OLD/name).read_bytes()) == pin,'complete frozen indexed constants '+name)
    packet = deepcopy(parent)
    packet['name'] = 'one_page_saturated_upper_indexed_bfs_degree283'
    packet['proof'] = '../../research/ten-positive-saturated-pell/PROOF.md'
    packet['parent_sha256'] = digest(parent_raw)
    packet['coefficient_binding'] = deepcopy(json.loads((FRONT/'INDEXED_BINDING.json').read_bytes()))
    packet['coefficient_binding']['path'] = 'coefficients/'
    copied = {}
    values = {}
    (OUT/'coefficients').mkdir(exist_ok=True)
    for name,pin in packet['coefficient_binding']['ports'].items():
        file_name = pin['file']
        blob = (OLD/'coefficients'/file_name).read_bytes()
        raw = gzip.decompress(blob)
        values[name] = int.from_bytes(raw,'little')
        need(digest(blob) == pin['gzip_sha256'] and digest(raw) == pin['raw_sha256'] and values[name].bit_length() == pin['bits'],'entire jointly calibrated indexed port '+name)
        need(blob == (FRONT/'coefficients/indexed_bfs'/file_name).read_bytes(),'whole alternate composition payload '+name)
        (OUT/'coefficients'/file_name).write_bytes(blob)
        copied['coefficients/'+file_name] = digest(blob)
    beta = values['beta']
    need(beta >= 31 and beta % 2 == 1 and 0 < values['MC'] < beta < values['MF'] < 2*beta and values['K0'] > 0,'joint uniform saturation theorem hypotheses')
    literal = (OLD/'SEED.txt').read_bytes()
    (OUT/'SEED.txt').write_bytes(literal)
    copied['SEED.txt'] = digest(literal)
    (OUT/'parent-polynomial.json').write_bytes(parent_raw)
    (OUT/'polynomial.json').write_bytes(encoded(packet))
    result = symbolic_binding(packet)
    template = (OUT/'equation-template.tex').read_text()
    original = (OLD/'equation.tex').read_text()
    need(template.split(MARKER,1)[1] == original.split(MARKER,1)[1],'entire printed indexed fixed-constant body/decoder/initializer verbatim')
    pins = dict(parent_sha256=digest(parent_raw),parent_manifest_sha256=digest((FRONT/'MANIFEST.json').read_bytes()),
        complete_parent_files=source_manifest,ordinary_proof_sha256=digest((FRONT/'PROOF.md').read_bytes()),
        renderer_sha256=digest(Path(__file__).read_bytes()),
        indexed_manifest_sha256=digest((OLD/'MANIFEST.json').read_bytes()),complete_indexed_files=indexed_manifest,
        indexed_proof_sha256=digest((OLD/'PROOF.md').read_bytes()),
        constant_body_sha256=digest(original.split(MARKER,1)[1].encode()),copied_files=copied,
        coefficient_transfer='Whole separately calibrated indexed BFS tuple, not a one-port substitution. Saturated PROOF section7 composes the actual free-port theorem with the whole indexed native/selector/controller theorem. Different K specializes a different polynomial; old native words and polynomials are never identified.',
        formula_binding=result)
    (OUT/'SOURCE_PINS.json').write_bytes(encoded(pins))
    return packet,result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--render',action='store_true')
    args = parser.parse_args()
    packet,binding = build_data()
    literal = (OUT/'SEED.txt').read_text().strip()
    need(len(literal) == 436 and all(ch in ALPHABET for ch in literal),'complete436-character seed')
    template = (OUT/'equation-template.tex').read_text()
    need('%%SEED%%' not in template,'standalone full literal constant recipe')
    tex = template
    if args.render:
        (OUT/'equation.tex').write_text(tex)
        run = subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error','-output-directory='+str(OUT),str(OUT/'equation.tex')],capture_output=True,text=True,timeout=60)
        (OUT/'RENDER.txt').write_text('\n'.join(line.rstrip() for line in (run.stdout+run.stderr).splitlines())+'\n')
        need(run.returncode == 0 and 'Overfull' not in run.stdout,'clean PDF render')
        # Keep seal-worthy diagnostics in ordinary tracked text files.
        # Do not put ignored .log/.aux build products in the manifest.
        tex_log = OUT/'equation.log'
        if tex_log.exists():
            (OUT/'TEX_DIAGNOSTICS.txt').write_text('\n'.join(line.rstrip() for line in tex_log.read_text().splitlines())+'\n')
            tex_log.unlink()
        (OUT/'equation.aux').unlink(missing_ok=True)
    need((OUT/'equation.tex').read_text() == tex,'complete standalone TeX')
    info = subprocess.run(['pdfinfo',str(OUT/'equation.pdf')],capture_output=True,text=True,check=True).stdout
    need(re.search(r'Pages:\s+1\b',info) and '612 x 792' in info,'one Letter page')
    subprocess.run(['pdftotext','-raw',str(OUT/'equation.pdf'),str(OUT/'equation.txt')],check=True)
    text = (OUT/'equation.txt').read_text()
    lines = [line.strip() for line in text.splitlines()]
    seed_lines = [literal[j:j+62] for j in range(0,len(literal),62)]
    need(any(lines[j:j+len(seed_lines)] == seed_lines for j in range(len(lines))),'every436 printed seed character')
    need(ALPHABET in text,'all62 alphabet characters')
    glyphs = ['α','η','ζ','β','ρ','µ','∆','δ','τ','Φ','ν','σ','ℓ']
    need(all(glyph in text for glyph in glyphs),'all distinct printed Greek glyphs')
    report = dict(status='PASS',python_optimization=sys.flags.optimize,formula_binding=binding,
        render=dict(pages=1,paper='Letter',body_font_pt=9,no_overfull_boxes=True,all436_seed_characters_exact=True,
                    all62_alphabet_characters_exact=True,all_Greek_glyphs_present=glyphs,
                    nonwhite_pdf_characters=len(re.sub(r'\s','',text))),
        sha256={name:digest((OUT/name).read_bytes()) for name in ('equation.tex','equation.pdf','polynomial.json','SEED.txt')},
        scope='Complete saturated page and universal printed front identity. Whole indexed tuple licensed by source PROOF section7 and the separately sealed indexed theorem. Complete positive maps, native/controller calibration and global degree proof retained separately. No Lean run or consistency assertion.')
    (OUT/('PAGE_VERIFY_OPTIMIZED.json' if sys.flags.optimize else 'PAGE_VERIFY.json')).write_bytes(encoded(report))
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
