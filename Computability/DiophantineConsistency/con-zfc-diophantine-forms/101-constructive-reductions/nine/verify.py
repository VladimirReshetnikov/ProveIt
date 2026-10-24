#!/usr/bin/env python3
"""Independent exact checks of the delivered polynomial DAGs.

No producer is imported. Fixed leaves are checked against actual port bytes.
Small polynomial identities are checked at every named register, so this is
an exact composition check, not only equality at random points.
"""
from pathlib import Path
from collections import Counter,defaultdict
import gzip,hashlib,json,math,random
ROOT=Path(__file__).resolve().parent

def need(ok,message):
    if not ok:raise ValueError(message)
def read(path):return json.loads(path.read_text())
class P:
    def __init__(self,x=0):
        self.p=x if isinstance(x,dict) else ({():int(x)} if x else {})
    def __add__(self,b):
        b=pol(b);d=defaultdict(int,self.p)
        for k,v in b.p.items():d[k]+=v
        return P({k:v for k,v in d.items() if v})
    __radd__=__add__
    def __neg__(self):return P({k:-v for k,v in self.p.items()})
    def __sub__(self,b):return self+-pol(b)
    def __rsub__(self,b):return pol(b)+-self
    def __mul__(self,b):
        b=pol(b);d=defaultdict(int)
        for k,v in self.p.items():
            for l,w in b.p.items():
                z=defaultdict(int,k)
                for n,e in l:z[n]+=e
                d[tuple(sorted((n,e) for n,e in z.items() if e))]+=v*w
        return P({k:v for k,v in d.items() if v})
    __rmul__=__mul__
    def __pow__(self,e):
        need(type(e) is int and e>=0,'nonnegative fixed exponent')
        if not e:return P(1)
        z=self**(e//2);z=z*z
        return z*self if e%2 else z
    def __eq__(self,b):return self.p==pol(b).p

def pol(x):return x if isinstance(x,P) else P(x)
def atom(n):return P({((n,1),):1})
def recipe_key(rec):return tuple(sorted((tuple(t['powers']),t['coefficient']) for t in rec))

def verify_graph(path):
    body=read(path);nodes=body['nodes'];names=body['named_nodes'];profile=body['profile']
    base=ROOT if profile=='boundary' else ROOT/'compact'
    code=read(base/'data/code.json');kern=read(base/'data/kernels.json')
    ports=[int.from_bytes(gzip.decompress((base/'data'/f'{n}.bin.gz').read_bytes()),'little') for n in ['beta','K','MC','MF_source']]
    fixed={}
    binding=read(ROOT/'fixed'/profile/'BINDING.json')
    for rec in binding['records']:
        blob=(ROOT/rec['path']).read_bytes();raw=gzip.decompress(blob)
        need(hashlib.sha256(blob).hexdigest()==rec['gzip_sha256'],'gzip coefficient hash')
        need(hashlib.sha256(raw).hexdigest()==rec['raw_sha256'],'raw coefficient hash')
        fixed[rec['name']]=rec['sign']*int.from_bytes(raw,'little')
    fixed_recipes=body['coefficient_recipes']
    for name,rec in fixed_recipes.items():
        val=sum(t['coefficient']*math.prod(x**e for x,e in zip(ports,t['powers'])) for t in rec)
        need(fixed[name]==val,'exact fixed coefficient recipe')
    kap=2134939 if profile=='boundary' else 864026
    h=1866 if profile=='boundary' else 2080;W=115;E=h+W+2
    popheight=E+W+23;lp=(22-popheight*kap)%2;nB=(popheight-15)//2;nc=(15*kap+lp-22)//2
    need(fixed['base_scale']==1<<kap and fixed['threshold_scale']==1<<nc,'exact fixed scale leaves')
    used=set();todo=[body['output']]
    while todo:
        q=todo.pop()
        if q in used:continue
        used.add(q);n=nodes[q]
        if n['kind'] in ('add','sub','mul'):
            need(0<=n['left']<q and 0<=n['right']<q,'DAG topological order')
            todo.extend([n['left'],n['right']])
    need(len(used)==len(nodes),'all nodes are live')
    need(set(n['name'] for n in nodes if n['kind']=='variable')==set(['b','g','h','s','w','C','i','j','n']),'exactly the nine variables')
    counts=Counter(n['kind'] for n in nodes if n['kind'] in ('add','sub','mul'))
    need(dict(counts)==body['operation_counts'] and sum(counts.values())==body['total_operations'],'independent operation count')
    cuts={};checked=[]
    def actual(root):
        memo={}
        def rec(q):
            if q in cuts:return cuts[q]
            if q in memo:return memo[q]
            n=nodes[q];k=n['kind']
            if k=='literal':v=P(n['value'])
            elif k=='fixed':v=atom('$'+n['name'])
            elif k=='variable':v=atom(n['name'])
            elif k=='add':v=rec(n['left'])+rec(n['right'])
            elif k=='sub':v=rec(n['left'])-rec(n['right'])
            elif k=='mul':v=rec(n['left'])*rec(n['right'])
            else:raise ValueError('invalid node kind')
            memo[q]=v;return v
        return rec(root)
    def check(name,expected):
        need(name in names,'named polynomial '+name)
        need(actual(names[name])==expected,'exact named-register identity '+name)
        checked.append(name);cuts[names[name]]=atom(name)
    def check_power(name,expected):
        saved=cuts.copy();cuts.clear();cuts[names['B']]=atom('B')
        check(name,expected)
        cuts.clear();cuts.update(saved);cuts[names[name]]=atom(name)
    b,g,s,w,C,i,j,n=[atom(z) for z in ['b','g','s','w','C','i','j','n']]
    hh=atom('h');B=atom('B')
    check('B',atom('$base_scale')*b*b)
    keys={recipe_key(r):name for name,r in fixed_recipes.items()}
    for layer in kern['kernels']:
        expected=P(0)
        for t in layer['terms']:
            rec=t['coefficient']
            co=P(rec[0]['coefficient']) if len(rec)==1 and not any(rec[0]['powers']) else atom('$'+keys[recipe_key(rec)])
            expected+=co*B**t['exponent']
        check('Dcode'+str(layer['degree']),expected)
    check('ell',sum((B**e for e in code['weights']),P(0)))
    check('targets',sum((B**e for e in code['targets_by_row']),P(0)))
    a=atom
    check_power('N0',B**116)
    check('Usource',a('ell')+g)
    check('Gsource',(a('Dcode2')*a('Usource')+a('Dcode1'))*a('Usource')+a('Dcode0'))
    check('mask',a('N0')-1-(b-1)*a('ell'))
    check('Tcode',a('mask')+(B-2)*a('targets')*a('N0'))
    check('Jcode',2*a('Gsource')+a('targets'))
    check('Scode',g+a('Jcode')*a('N0'))
    check_power('L',2**lp*b*B**E)
    check_power('N',a('$threshold_scale')*B**nB)
    check('Rplus1',a('L')*(a('Scode')+a('Tcode')+1)-a('Scode'))
    check('R',a('Rplus1')-1)
    check_power('capbase',b*B**W)
    check('U',a('N')**2*w);check('Y',a('N')**2*s);check('M',a('R')*a('Y'))
    check('MU',a('M')*a('U'));check('P',2*a('M')*a('MU'))
    check('K',a('Rplus1')+hh*(a('P')-1))
    check('A',a('M')+a('MU'));check('B1',2*a('R')+1);check('C',C)
    check('W1',b*w);check('J',4*a('A')-5)
    check('Q',a('W1')*(3*C-2*a('W1'))+2)
    check('V0',a('P')*a('K'));check('a0',a('V0')**2-a('K')**2+1)
    check('margin',a('K')**2*(4*a('capbase')-g)-16*a('capbase')*(C-a('K')*a('Y'))**2)
    check('Omega',a('J')*a('margin'));check('E0',a('J')*(n+a('W1')**2)+a('Q'))
    check('Am1',a('A')**2-1);check('C2',C*C);check('Dm1',a('Am1')*a('C2'));check('D',a('Dm1')+1)
    check('e',i*a('J')*C)
    # r is pruned from the simple graph because its use is factored through e*CD.
    if 'r' in names:check('r',a('e')*C)
    check('CD',C*a('D'));check('F',a('e')**2*a('D')*a('Dm1')+1)
    check('Lambda',a('CD')+1-a('A'));check('G',a('A')+a('F')*a('Lambda'))
    check('Z',a('B1')+(j-1)*C);check('H',C+a('F')*a('Z'))
    check('GH',a('G')*a('H'));check('I',a('GH')**2-a('H')**2+1)
    check('raw_a1',a('D')*a('F')*a('I'))
    if body['majorant']=='simple':
        check('Tmajor',a('A')*a('e')*a('CD'));check('V1',a('Tmajor')*a('GH'))
        # a1 and raw_a1 are the same node: alias without creating a premise.
        need(names['a1']==names['raw_a1'],'simple radicand alias');cuts[names['a1']]=a('a1')
    else:
        pp=read(ROOT/'data/saturated_corrected_P.json');expected=P(0)
        for term in pp['terms']:
            t=P(term['coefficient'])
            for v,e in zip([a('A'),C,i,a('Z')],term['powers']):t=t*v**e
            expected+=t
        saved_cuts=cuts.copy();cuts.clear()
        for name in ['A','C','Z']:cuts[names[name]]=a(name)
        check('V1',expected)
        cuts.clear();cuts.update(saved_cuts);cuts[names['V1']]=a('V1')
        check('scale',1024*a('C2')**2*C*i);check('a1',a('scale')**2*a('raw_a1'))
    check('Theta',a('E0')-a('Omega')*(a('V0')+a('V1')))
    check('inner',a('Theta')**2-a('Omega')**2*(a('a0')+a('a1')))
    check('F9',a('inner')**2-4*a('Omega')**4*a('a0')*a('a1'))
    need(names['F9']==body['output'],'designated polynomial output')
    r=4*E-1;nu=2*nB;adeg=r+4*nu+2
    degree=(88*adeg+4*r+8*W+108 if body['majorant']=='simple' else 59*adeg+4*r+8*W+103)
    need(body['exact_degree']==degree,'resolved exact degree metadata')
    return dict(file=path.name,operations=sum(counts.values()),degree=degree,exact_named_identities=len(checked),fixed_leaves=len(fixed),status='PASS')

def main():
    results=[verify_graph(p) for p in sorted((ROOT/'equations').glob('*.json'))]
    out=dict(status='PASS',graphs=results,scope='Exact finite polynomial, literal coefficient and graph checks; semantic zero-existence equivalence is proved separately.')
    (ROOT/'VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
