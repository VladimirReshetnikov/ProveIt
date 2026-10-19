#!/usr/bin/env python3
"""Independent finite grammar, projection, lock and source-shape audit.

This checker deliberately does not certify a literal TM or prove the
metatheoretic consistency equivalence. The frozen source emitter and logical
calibrations remain separately attributed inputs.
"""
import argparse,hashlib,json
from functools import lru_cache
from pathlib import Path

HERE=Path(__file__).resolve().parent
def read(p):return json.loads(Path(p).read_text())
def check(path,metadata):
    m=read(metadata);d=read(path);ref=HERE/'vendor'
    base=m['base'];oldax=max(base['roots'],key=len)
    originalax=base.get('source_override',{}).get('original_word',oldax)
    nr=len(m['variants']);order=d['axiom_order'];roles=d['axiom_roles']
    assert sorted(order)==list(range(nr))and len(roles)==nr
    assert all(0<=r<6 for r in roles)
    expected=m['prefix']+''.join(m['variants'][i][roles[i]]for i in order)+m['tail']
    assert max(d['roots'],key=len)==expected
    assert d['source_replacements']=={originalax:expected}
    if 'source_override'in d:assert d['source_override']['new_word']==expected
    assert d['roots']==[expected if w==oldax else w for w in base['roots']]
    grammar={w:(a,b)for w,a,b in d['rules']};term=m['terms']
    assert len(grammar)==len(d['rules'])==d['rules_count']
    for w,(a,b)in grammar.items():
        assert w not in term and a and b and w==a+b
        assert a in grammar or a in term
        assert b in grammar or b in term
        assert a not in term or term[a]&1
        assert b not in term or term[b]&2
    routes={(r['source'],r['read']):r['word']for r in d['routes']}
    lines=(ref/'inputs/canonical-constraints.txt').read_text().splitlines()
    ng=int(lines[0]);p=1;projections=0
    assert len(routes)==len(d['routes'])==ng==11
    for _ in range(ng):
        q,bit,unused,nc=lines[p].split();p+=1
        for _ in range(int(nc)):
            word=routes[int(q),int(bit)];prefix,target=lines[p].split();p+=1
            for c in prefix:word=grammar[word][int(c)]
            assert word==target;projections+=1
    lines=(ref/'inputs/canonical-lock54.txt').read_text().splitlines()
    assert int(lines[0])==len(lines)-1==54
    for row in lines[1:]:
        w,b,t=row.split();assert grammar[w][int(b)]==t
    live=set()
    def visit(w):
        if w in term or w in live:return
        live.add(w)
        for c in grammar[w]:visit(c)
    for w in d['roots']+list(routes.values()):visit(w)
    assert live==set(grammar)
    s=read(ref/'reference_data/reference/grammar/closed-sequence-grammar-next22.json')
    symbols=read(ref/'reference_data/reference/grammar/semantic-symbols.json')
    enc=read(ref/'inputs/canonical-map.json')['physical_atoms']
    canon=lambda w:''.join(enc[c]for c in w)
    ls=(ref/'reference_data/reference/grammar/semantic.txt').read_text().splitlines();n=int(ls[0].split()[0])
    names={int(q):canon(w)for k,w,q in map(str.split,ls[1:n+1])}
    old={canon(w):(canon(w[:int(k)]),canon(w[int(k):]))for k,w,q in map(str.split,ls[1:n+1])}
    byast={int(a):names[int(q)]for q,a in s['sequence_ast_roots'].items()}
    terms={enc[c]:s['atoms'][name]['ast']for c,name in symbols.items()}
    def join(a,b):return 1+a[0],max(1+a[0],a[1],b[1]),1+max(a[2],b[2]),a[3]+b[3]
    @lru_cache(None)
    def wordprop(w):
        w=expected if w==originalax else w
        if w in terms:return astprop(terms[w])
        return join(*(wordprop(x)for x in grammar.get(w,old.get(w))))
    @lru_cache(None)
    def astprop(i):
        if i in byast:return wordprop(byast[i])
        r=s['ast_dag'][i]
        return (0,0,0,1)if r[0]=='L'else join(astprop(r[1]),astprop(r[2]))
    prop=astprop(s['original_ast'])
    assert prop[1]<=6 and prop[2]<=64
    return dict(file=str(path.relative_to(HERE)),sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        rules=len(grammar),route_projections=projections,bootstrap_locks=54,
        full_source_properties=prop,AX_fine_atoms=len(expected),logical_rows=nr,
        scope='Finite source/grammar audit only; no literal-table or consistency endpoint.')

def main():
    manifest=read(HERE/'vendor_manifest.json')
    for name,record in manifest.items():
        raw=(HERE/'vendor'/name).read_bytes()
        assert len(raw)==record['bytes']and hashlib.sha256(raw).hexdigest()==record['sha256']
    records=[]
    for folder,metadata in [(HERE,HERE/'axiom_search_metadata.json'),
        (HERE/'normalized',HERE/'normalized/metadata.json'),
        (HERE/'basis_kbp',HERE/'basis_kbp/metadata.json'),
        (HERE/'basis_ksp',HERE/'basis_ksp/metadata.json')]:
        for file in sorted((folder/'candidates').glob('*.json')):records.append(check(file,metadata))
    for file in sorted((HERE/'refinements').glob('*/best.json')):
        records.append(check(file,HERE/'axiom_search_metadata.json'))
    out=dict(status='PASS_FINITE_GRAMMAR_AUDIT',candidates=len(records),records=records)
    (HERE/'structural_audit.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(dict(status=out['status'],candidates=len(records),counts=sorted({r['rules']for r in records}))))
if __name__=='__main__':main()
