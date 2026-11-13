#!/usr/bin/env python3
"""Independently parse displayed arithmetic and verify exact cut polynomials."""
import ast,collections,hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';TEX=BASE/'equation75-2011.tex';PDF=BASE/'equation75-2011.pdf';OLD=BASE/'equation.tex';GRAPH=BASE/'research/thirteen-unit-sphere96/polynomial.json';PKG=BASE/'reviews/equation75-2011-display';DEGREE=BASE/'reviews/thirteen75-degree2011-independent-audit'
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
    if not b:raise ValueError(m)
class P:
    def __init__(self,d):self.d={k:v for k,v in d.items() if v}
    @staticmethod
    def c(n):return P({():n})
    @staticmethod
    def v(n):return P({(n,):1})
    def __add__(self,b):
        d=self.d.copy()
        for k,v in b.d.items():d[k]=d.get(k,0)+v
        return P(d)
    def __neg__(self):return P({k:-v for k,v in self.d.items()})
    def __sub__(self,b):return self+-b
    def __mul__(self,b):
        d=collections.defaultdict(int)
        for x,a in self.d.items():
            for y,c in b.d.items():d[tuple(sorted(x+y))]+=a*c
        return P(d)
    def pow(self,n):
        need(type(n) is int and 0<=n<=10,'power');r=P.c(1)
        for _ in range(n):r=r*self
        return r
    def __eq__(self,b):return self.d==b.d
TOKEN=re.compile(r'\\[A-Za-z]+|[A-Za-z]|[0-9]+|[+\-*^()\[\]{}]')
def expr(s,env):
    raw=TOKEN.findall(s);need(''.join(raw)==re.sub(r'\s+','',s),'unknown TeX token '+s)
    tokens=[x.lstrip('\\') if x.startswith('\\') else x for x in raw];parts=[];prev=''
    for t in tokens:
        typ='open' if t in '([{' else 'close' if t in ')]}' else 'op' if t in '+-*^' else 'atom'
        if prev in ('atom','close') and typ in ('atom','open'):parts.append('*')
        parts.append('(' if typ=='open' else ')' if typ=='close' else '**' if t=='^' else t);prev=typ
    tree=ast.parse(''.join(parts),mode='eval').body
    def walk(n):
        if isinstance(n,ast.Name):need(n.id in env,'unknown symbol '+n.id);return env[n.id]
        if isinstance(n,ast.Constant) and type(n.value) is int:return P.c(n.value)
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return -walk(n.operand)
        if isinstance(n,ast.BinOp):
            x=walk(n.left)
            if isinstance(n.op,ast.Pow):need(isinstance(n.right,ast.Constant),'nonliteral exponent');return x.pow(n.right.value)
            y=walk(n.right)
            if isinstance(n.op,ast.Add):return x+y
            if isinstance(n.op,ast.Sub):return x-y
            if isinstance(n.op,ast.Mult):return x*y
        raise ValueError('unsupported syntax '+ast.dump(n))
    return walk(tree)
def main():
    files=[TEX,PDF,PKG/'README.md',PKG/'check_display.py']
    for p in files:
        blob=subprocess.run(['git','show','fd9e89cc36:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(blob).hexdigest()==H(p),'committed file '+str(p))
    need(H(TEX)=='18855bda8468b5a3d61b1ff8c07b52f1660262aaa8ecf387f127af56511e26fa' and H(PDF)=='07acffa02ec7e2068b2cbd04e16cc0089d4fa30af045e86a9130f95ac444abda','display hashes')
    need(H(GRAPH)=='48573f58aac3d60f706eb7f52e92f5c061bd74d41ad7e9e9ee3e2ea43dcd9ca1','graph hash')
    graph=json.loads(GRAPH.read_bytes());rows=graph['source'];nodes={a:(op,b,c) for a,op,b,c in rows};need(len(rows)==len(nodes)==75 and graph['output']=='polynomial','graph inventory')
    reachable=set()
    def visit(n):
        if n not in nodes or n in reachable:return
        reachable.add(n);_,a,b=nodes[n];visit(a);visit(b)
    visit(graph['output']);need(len(reachable)==75,'dead graph rows')
    counts=collections.Counter(op for _,op,_,_ in rows);need(dict(counts)=={'*':42,'+':18,'-':15},'graph operation counts')
    initial=[('J','J'),('F','F'),('alpha','alpha'),('f','f'),('i','i'),('T','T'),('s','s'),('w','w'),('n','n'),('eta','eta'),('zeta','zeta'),('m','m'),('gamma','gamma'),('beta','beta'),('K','K0'),('mu','MC'),('omega','MF')]
    targets=[('b','qm'),('q','q'),('C','C'),('X','X'),('Y','Y'),('E','E'),('k','k'),('ell','ell'),('c','c'),('a','a'),('H','H'),('Delta','Delta'),('D','main_root'),('R','R'),('tau','tau'),('L','cTminusR'),('V','V'),('G','B'),('y','y'),('P','N0'),('Q','N1'),('t',None),('U','Na'),('Z','Z')]
    text=TEX.read_text();display=text.split(r'\textbf{The four fixed integers.}',1)[0]
    unknown=re.search(r'The only unknowns are\s*\\\[(.*?)\\in\\mathbb Z_\{>0\}\.\s*\\\]',display,re.S);need(unknown is not None,'unknown list')
    listed=[x.strip().lstrip('\\') for x in unknown.group(1).split(',')];need(listed==[x[0] for x in initial[:13]] and len(set(listed))==13,'distinct unknown names')
    body=re.search(r'\\begin\{gathered\}(.*?)\\end\{gathered\}',display,re.S).group(1).strip();need(body.endswith('.'),'definition punctuation')
    defs=[x.strip() for x in body[:-1].replace(r'\quad','').replace('\\\\',',').split(',') if x.strip()];need(len(defs)==24,'definition count')
    env={printed:P.v(printed) for printed,_ in initial};inputs={internal:env[printed] for printed,internal in initial};cuts={}
    for definition,(label,target) in zip(defs,targets):
        left,right=definition.split('=',1);need(left.strip().lstrip('\\')==label,'label '+label);actual=expr(right,env);memo={}
        def value(n):
            if type(n) is int:return P.c(n)
            if n in inputs:return inputs[n]
            if n in cuts:return cuts[n]
            if n not in memo:
                op,a,b=nodes[n];x,y=value(a),value(b);memo[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
            return memo[n]
        wanted=env['b']*env['i']*env['c'].pow(2) if target is None else value(target)
        need(actual==wanted,'polynomial '+label)
        if target is None:env[label]=actual
        else:env[label]=P.v('cut_'+label);cuts[target]=env[label]
    boxed=re.search(r'\\boxed\{(.*?)\}',display,re.S).group(1);left,right=boxed.split('=',1)
    need(right.strip()=='0.' and expr(left,env)==(env['P']*env['Q']).pow(2)+env['U'].pow(2)+env['Z'].pow(2)-P.c(3),'boxed output')
    need(rows[-7:]==[['product0','*','N0','N1'],['sqPQ','*','product0','product0'],['sqU','*','Na','Na'],['sqZ','*','Z','Z'],['sumPQ_U','+','sqPQ','sqU'],['sumSquares','+','sumPQ_U','sqZ'],['polynomial','-','sumSquares',3]],'graph output')
    need(expr(r'q+F-\alpha',env)!=expr(r'q-F-\alpha',env),'gap sign control')
    need(expr(r'1+4[b(m+LVG)-G]',env)!=expr(r'1+4[b(m-LVG)-G]',env),'carrier sign control')
    need(expr(r'(PQ)^2+U^2+Z^2+3',env)!=expr(r'(PQ)^2+U^2+Z^2-3',env),'boxed sign control')
    begin=r'\textbf{The four fixed integers.}';end=r'\normalfont\fontsize{7.7}{8.2}\selectfont';old=OLD.read_text();need(text[text.index(begin):text.index(end)]==old[old.index(begin):old.index(end)],'constant block')
    seed=re.search(r'\\begingroup\\fontsize\{7.7\}\{8.2\}\\selectfont\\ttfamily(.*?)\\endgroup',text,re.S).group(1);need(all(re.fullmatch(r'\d+\\par',x.strip()) for x in seed.splitlines() if x.strip()),'base-10 seed formatting')
    p=subprocess.run([sys.executable,'-I','-S',str(PKG/'check_display.py')],capture_output=True,text=True,timeout=60);need(p.returncode==0 and not p.stderr and 'PASS:' in p.stdout,'author checker')
    p2=subprocess.run([sys.executable,'-I','-S','-O',str(PKG/'check_display.py')],capture_output=True,text=True,timeout=30);need(p2.returncode!=0 and 'optimized Python is unsupported' in p2.stderr,'optimized guard')
    degree=subprocess.run([sys.executable,'-I','-S',str(DEGREE/'audit.py')],capture_output=True,text=True,timeout=60);need(degree.returncode==0 and not degree.stderr and json.loads(degree.stdout)['status'].startswith('PASS_'),'degree audit')
    print(json.dumps({'status':'PASS_INDEPENDENT_EQUATION75_2011_DISPLAY_AUDIT','source_commit':'fd9e89cc36','tex_sha256':H(TEX),'pdf_sha256':H(PDF),'graph_sha256':H(GRAPH),'distinct_positive_unknowns':listed,'exact_definitions':24,'reachable_graph_rows':75,'operations':dict(counts),'decimal_seed_digits':sum(len(x.strip().removesuffix('\\par')) for x in seed.splitlines() if x.strip()),'author_checker_exit':p.returncode,'optimized_guard_exit':p2.returncode,'degree_audit_exit':degree.returncode,'scope':'Independent external TeX arithmetic parser and symbolic cut checks, byte-equal inherited constant block and degree review; no formal TeX/PDF semantics or independent formalization of the inherited decoder.'},indent=2))
if __name__=='__main__':main()
