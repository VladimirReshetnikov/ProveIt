"""Four controlled best-basis-plus-NIP source integrations, not binary tables."""
import json,time
import pricing as p

def main():
    p.OUTPUT=p.HERE/'replay_joint_nip';p.OUTPUT.mkdir(exist_ok=True)
    j=json.loads((p.HERE/'nip_source.json').read_text());source=j['structures'];mapping={}
    def intern(n):
        if n in mapping:return mapping[n]
        x=source[n]
        if isinstance(x[0],str):v=p.e.I[tuple(x)]
        else:v=p.e.cons(intern(x[0]),intern(x[1]))
        mapping[n]=v;return v
    p.e.ROOT=intern(j['root'])
    assert p.e.score(p.e.ROOT)==(224,6,48)
    assert 275 in p.e.live(p.e.ROOT)
    p.BASE_SET=p.e.live(p.e.ROOT);p.BASE_STRUCTURES=list(p.e.S)
    p.DICT={bytes(p.word(n)):n for n in sorted(p.BASE_SET)if p.e.closed(n)}
    p.TRIE={}
    for w,n in p.DICT.items():
        root=p.TRIE
        for b in w:root=root.setdefault(b,{})
        root[-1]=n
    rows=[];started=time.monotonic()
    for basis in ('ksp','ksq4','ksqdn','ksdne'):
        meta=json.loads((p.HERE/'best_sources'/f'{basis}.json').read_text())['metadata']
        a,b,c=meta['parameters'];I=p.t.Imp
        third={'ksp':I(I(I(a,b),a),a),
               'ksq4':I(p.t.All(a,b),p.t.All(a,p.t.All(a,b))),
               'ksqdn':I(p.t.Not(p.t.Not(p.t.All(a,b))),p.t.All(a,b)),
               'ksdne':I(p.t.Not(p.t.Not(a)),a)}[basis]
        axioms={'K':I(a,I(b,a)),'S':I(I(a,I(b,c)),I(I(a,b),I(a,c)))}
        order=meta['order'];triple=[axioms.get(k,third)for k in order]
        rest=p.OLD_ROWS[2:];pos=meta['position'];rr=rest[:pos]+triple+rest[pos:]
        program=[166,121,180,176]+[x for f in rr for x in p.t.emit(f)]+p.t.emit(p.BUNDLE)+p.t.TAIL
        got,_=p.t.symbolic(program);assert got==['old_top',p.OLD_ROWS[0],*rr,p.BUNDLE]
        row=p.price(program);p.export(row,dict(meta,basis=basis),'best_'+basis+'.json')
        rows.append(dict(basis=basis,score=row[0],dictionary_calls=row[1]))
        print(rows[-1],flush=True)
    out=dict(status='BOUNDED_SOURCE_DICTIONARY_PRICING',nip_baseline=[224,6,48],cases=len(rows),
             selection='The saved best representative from each288-casecorrelatedrole basis sweep',
             seconds=time.monotonic()-started,rows=rows)
    (p.OUTPUT/'pricing.json').write_text(json.dumps(out,indent=2)+'\n')

if __name__=='__main__':main()
