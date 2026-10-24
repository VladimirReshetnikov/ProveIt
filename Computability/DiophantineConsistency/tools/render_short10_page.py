#!/usr/bin/env python3
"""Complete short-projection ten-positive page; preserves existing pages."""
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
OUT = ROOT/'candidates/one-page-short10'
OLD = ROOT/'candidates/one-page-weighted10'
FRONT = ROOT/'candidates/ten-positive-short-projection'
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
        ('X','w*q'),('k','eta+zeta'),('c','k*Y+eta'),('a','X*Y+Y'),
        ('mu','q**2+1'),('A','mu*(a+2)'),('H','4*A-1'),
        ('Delta','A*(A+2)'),('I','i*c**2'),
        ('V0','X*(mu*Y)**2'),('ell','V0*k'),('Dtau','ell*(ell+k)+1'),
        ('R','(bJ*(q-F)+alpha)*(q**2-1)+(MC+q*MF)*J'),
        ('e','k-R-1'),('Bt','(K+w)*C-F'),
        ('Df','1+Delta*I**2'),('Q','Delta**2*I**2'),('delta','Q-1'),
        ('Tp','T+alpha'),('bp','c*Tp-R'),('V','Df*bp-c'),
        ('Dy','Q*V**2-1'),('Kpos','X*(3*c-2*X)+2'),
        ('L','H*I+bp'),('W','1+bJ*L'),
        ('P1','q**3*bJ'),('M','P1*mu**2*H'),
        ('Z','P1*mu**2*(H*(n+V)+Kpos)+H*(mu**2*(bJ*Y-q**3*W*Bt)-P1*e)'),
        ('S','delta*Z**2'),('Atau','9*delta*M**2*Dtau'),('Af','delta*M**2*Df'),
        ('Ay','M**2*Dy'),
        ('Sigma1','S+Ay'),('Sigma2','Atau+Af'),('P','Sigma1-Sigma2'),
        ('U','S*Ay'),('VN','Atau*Af'),('En','P**2-4*(U+VN)'),
        ('N','En**2-64*U*VN'),
    ]
    initial = packet['witnesses']+['beta','K','MC','MF']
    printed = {name:leaf(name) for name in initial}
    for name,text in displayed:
        printed[name] = parse(text,printed)
    actual = {name:leaf(name) for name in packet['witnesses']+packet['fixed_numerals']}
    for name,tag,a,b in packet['source']:
        actual[name] = op(tag,leaf(a) if type(a) is int else actual[a],leaf(b) if type(b) is int else actual[b])
    need(actual[packet['output']] == printed['N'],'complete displayed front equals all101 literal gates over free coefficients')
    counts = Counter(row[1] for row in packet['source'])
    need(len(packet['source']) == 101 and dict(counts) == {'*':60,'+':24,'-':17},'actual101-operation inventory')
    return dict(status='PASS',all101_gates_bound=True,method='Exact shared terms modulo associative/commutative ring + and *; no numerical substitution or expanded-polynomial hash inference.',
                printed_schedule=displayed,positive_unknowns=10,operations=101,degree=368,
                aliases=dict(K='K0',A='Am1',H='Hp',Delta='Dp',Z='Znum',M='Mtot',S='fs',q_minus='bJ',K_2='Kpos'))


def build_data():
    OUT.mkdir(parents=True,exist_ok=True)
    parent_raw = (FRONT/'equation.json').read_bytes()
    parent = json.loads(parent_raw)
    for name,pin in json.loads((FRONT/'MANIFEST.json').read_bytes())['files'].items():
        need(digest((FRONT/name).read_bytes()) == pin,'complete frozen101 parent '+name)
    packet = deepcopy(parent)
    packet['name'] = 'one_page_short10_bfs44_degree368'
    packet['parent_sha256'] = digest(parent_raw)
    packet['coefficient_binding'] = {'path':'coefficients/','tuple':'whole BFS-renamed compact44, corrected initializer; MF_source shifted exactly once','ports':{}}
    port_files = {'beta':'beta.bin.gz','K0':'K.bin.gz','MC':'MC.bin.gz','MF':'MF_source.bin.gz'}
    copied = {}
    values = {}
    (OUT/'coefficients').mkdir(exist_ok=True)
    for name,file_name in port_files.items():
        blob = (OLD/'coefficients'/file_name).read_bytes()
        raw = gzip.decompress(blob)
        values[name] = int.from_bytes(raw,'little')
        (OUT/'coefficients'/file_name).write_bytes(blob)
        packet['coefficient_binding']['ports'][name] = dict(file=file_name,raw_sha256=digest(raw),gzip_sha256=digest(blob),bits=int.from_bytes(raw,'little').bit_length())
        copied['coefficients/'+file_name] = digest(blob)
    beta = values['beta']
    need(beta >= 31 and beta % 2 == 1 and
         0 < values['MC'] < beta < values['MF'] < 2*beta and values['K0'] > 0,
         'whole page tuple satisfies the uniform quadratic-projection proof hypotheses')
    for name in ('SEED.txt',):
        raw = (OLD/name).read_bytes()
        (OUT/name).write_bytes(raw)
        copied[name] = digest(raw)
    (OUT/'parent-polynomial.json').write_bytes(parent_raw)
    (OUT/'polynomial.json').write_bytes(encoded(packet))
    result = symbolic_binding(packet)
    template = (OUT/'equation-template.tex').read_text()
    original = (OLD/'equation-template.tex').read_text()
    need(template.split(MARKER,1)[1] == original.split(MARKER,1)[1],'the entire printed fixed-constant recipe/decoder/initializer body is verbatim')
    pins = dict(parent_sha256=digest(parent_raw),constant_page_template_sha256=digest(original.encode()),
        ordinary_proof_sha256=digest((FRONT/'PROOF.md').read_bytes()),
        short_ordinary_peer_sha256=digest((FRONT/'source/SHORT_ORDINARY_PEER.md').read_bytes()),
        weighted_proof_sha256=digest((FRONT/'source/WEIGHTED_PROOF.md').read_bytes()),
        weighted_ordinary_peer_sha256=digest((FRONT/'source/WEIGHTED_ORDINARY_PEER.md').read_bytes()),
        shifted_proof_sha256=digest((FRONT/'source/SHIFTED_PROOF.md').read_bytes()),
        free_J_proof_sha256=digest((FRONT/'source/FREE_J_PROOF.md').read_bytes()),
        native_transfer_readme_sha256=digest((OLD/'README.md').read_bytes()),
        prior_calibrated_page_polynomial_sha256=digest((OLD/'polynomial.json').read_bytes()),
        constant_body_sha256=digest(original.split(MARKER,1)[1].encode()),
        copied_files=copied,coefficient_transfer='The whole BFS44 tuple is unchanged from the frozen scaled10 page. Uniform free-J, weighted-root, shorter-transport and positive-projection proofs and both positive witness maps apply at these actual ports; the older full typed-color/native/controller transfer is inherited, not a pointwise identity with original44 K.',
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
    need(template.count('%%SEED%%') == 1,'single complete seed slot')
    tex = template.replace('%%SEED%%','\n'.join(literal[j:j+62]+r'\par' for j in range(0,len(literal),62)))
    if args.render:
        (OUT/'equation.tex').write_text(tex)
        run = subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error','-output-directory='+str(OUT),str(OUT/'equation.tex')],capture_output=True,text=True,timeout=60)
        (OUT/'RENDER.txt').write_text(run.stdout+run.stderr)
        need(run.returncode == 0 and 'Overfull' not in run.stdout,'clean PDF render')
        # Keep seal-worthy diagnostics in ordinary tracked text files.
        # Do not put ignored .log/.aux build products in the manifest.
        tex_log = OUT/'equation.log'
        if tex_log.exists():
            (OUT/'TEX_DIAGNOSTICS.txt').write_bytes(tex_log.read_bytes())
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
    glyphs = ['α','η','ζ','β','ρ','µ','κ','ϱ','∆','Σ']
    need(all(glyph in text for glyph in glyphs),'all distinct printed Greek glyphs')
    report = dict(status='PASS',python_optimization=sys.flags.optimize,formula_binding=binding,
        render=dict(pages=1,paper='Letter',body_font_pt=9,no_overfull_boxes=True,all436_seed_characters_exact=True,
                    all62_alphabet_characters_exact=True,all_Greek_glyphs_present=glyphs,
                    nonwhite_pdf_characters=len(re.sub(r'\s','',text))),
        sha256={name:digest((OUT/name).read_bytes()) for name in ('equation.tex','equation.pdf','polynomial.json','SEED.txt')},
        scope='Complete short-projection page and universal printed front identity. Whole fixed tuple inherited from the frozen scaled10 page; ordinary existence maps, native/controller calibration and degree proof retained separately. No Lean run or consistency assertion.')
    (OUT/('PAGE_VERIFY_OPTIMIZED.json' if sys.flags.optimize else 'PAGE_VERIFY.json')).write_bytes(encoded(report))
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
