"""Read the frozen Coq register-program literals without executing their source."""
from pathlib import Path
from functools import lru_cache
import re,os,hashlib

BASE = Path(os.environ.get('PROVEIT_ZFC254_ROOT', '.'))
REFERENCE_SHA256 = '1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'

def read_dag254():
    text = (BASE / 'coq/prog/Dag254.v').read_text()
    names = {}
    nodes = {}
    def edge(t):
        m = re.fullmatch(r'E(Node|Inc|Decnz|Break|Continue) (\d+)', t)
        if m:
            return ({'Node':'N','Inc':'I','Decnz':'D','Break':'B','Continue':'C'}[m[1]], int(m[2]))
        assert t == 'EHalt', t
        return ('H',)
    for m in re.finditer(r'\| (\d+) => \(([^,]+), ([^)]+)\)\s*\(\* (.*?) \*\)', text):
        i = int(m[1]); nodes[i] = (edge(m[2]), edge(m[3])); names[i]=m[4]
    assert len(nodes) == 219
    return nodes, names

def read_p254():
    path = BASE / 'coq/tm/Prog254.v'
    if not path.is_file():
        raise RuntimeError('Set PROVEIT_ZFC254_ROOT to the pinned source directory ending in ZF/m254.')
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != REFERENCE_SHA256:
        raise RuntimeError('Prog254.v does not match the pinned SHA-256.')
    text = raw.decode()
    body = text.split('Definition p254_tab : list (cedge * cedge) := [', 1)[1].split('].',1)[0]
    def edge(t):
        bits=t.strip().split()
        return (bits[0][1:], int(bits[1])) if len(bits)==2 else ('H',)
    nodes={i:(edge(a),edge(b)) for i,(a,b) in enumerate(re.findall(r'\(([^,]+), ([^)]+)\)',body))}
    assert len(nodes)==6459
    return nodes

def unfold(nodes, root=0):
    @lru_cache(None)
    def visit(e):
        return ('N',visit(nodes[e[1]][0]), visit(nodes[e[1]][1])) if e[0]=='N' else e
    return visit(('N',root))

def interned(t):
    seen={}
    def walk(e):
        if e[0]!='N': return e
        a,b=walk(e[1]),walk(e[2]); pair=(a,b)
        if pair not in seen: seen[pair]=len(seen)
        return ('N',seen[pair])
    root=walk(t)[1]
    return {i:pair for pair,i in seen.items()},root

@lru_cache(None)
def bounds(e):
    if e[0]=='N':
        h0,b0,c0=bounds(e[1]);h1,b1,c1=bounds(e[2])
        return (1+max(h0,h1),max(b0-1,b1),max(c0,c1-1))
    return (0, e[1] if e[0]=='B' else (1 if e[0]=='D' else 0), e[1] if e[0]=='C' else 0)

def closed(e):
    return bounds(e)[1:]==(0,0)

def leaves(t, path=()):
    if t[0]=='N':
        yield from leaves(t[1],path+(0,))
        yield from leaves(t[2],path+(1,))
    else:
        yield path,t

def seq_regions(t):
    """Factor all closed sequential nodes into words; preserve control nodes."""
    seqs={};atoms={}
    def walk(e):
        if e[0]!='N': return e
        if closed(e[1]) and closed(e[2]):
            def flat(f):
                if f[0]=='N' and closed(f[1]) and closed(f[2]):
                    return flat(f[1])+flat(f[2])
                return [walk(f)]
            word=tuple(flat(e))
            if word not in seqs:seqs[word]=len(seqs)
            return ('S',seqs[word])
        pair=(walk(e[1]),walk(e[2]))
        if pair not in atoms:atoms[pair]=len(atoms)
        return ('A',atoms[pair])
    root=walk(t)
    return {i:w for w,i in seqs.items()},{i:p for p,i in atoms.items()},root

if __name__=='__main__':
    for name,nodes in [('dag254',read_dag254()[0]),('p254',read_p254())]:
        t=unfold(nodes); compact,r=interned(t); seqs,atoms,root=seq_regions(t)
        print(name,'stored',len(nodes),'structural',len(compact),'bounds',bounds(t),'leaves',sum(1 for _ in leaves(t)))
        print('control atoms',len(atoms),'sequence regions',len(seqs),'lengths',sorted(map(len,seqs.values()),reverse=True))
