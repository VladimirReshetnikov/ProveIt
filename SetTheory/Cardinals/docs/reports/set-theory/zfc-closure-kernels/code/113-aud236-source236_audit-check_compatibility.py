"""One exact compatibility check for the new236 source and our NIP lane.

Use --kit for the portable source237_experiments directory and --machines
for the parent's delivered tables/source. No machine candidate is emitted.
"""
from pathlib import Path
from functools import cache
import argparse,hashlib,json,sys

def main():
    here=Path(__file__).resolve().parent
    ap=argparse.ArgumentParser();ap.add_argument('--kit',type=Path,default=here.parent/'source237_experiments')
    ap.add_argument('--machines',type=Path,default=here.parent/'machines')
    ap.add_argument('--output',type=Path,default=here/'compatibility_replay.json')
    args=ap.parse_args();sys.path.insert(0,str(args.kit))
    import source_core as e
    import finite_runtime as r
    import nip_counterexample as nip
    assert __debug__
    baseline=tuple(e.paths(e.ROOT))
    assert e.S[234]==(233,123)and e.S[123]==(122,115)
    assert all(e.closed(n)for n in(233,122,115))
    newroot=e.replace(e.ROOT,234,e.cons(e.cons(233,122),115))
    newrows=tuple(e.paths(newroot))
    supplied_bytes=(args.machines/'sites_logical236.json').read_bytes()
    assert hashlib.sha256(supplied_bytes).hexdigest()=='1ebe9691507b2d3236951a31d6b9a7ef548a2cdf90525cd57051992f8ac2626f'
    supplied=json.loads(supplied_bytes)
    assert [list(x)for x in newrows]==supplied
    oldscore=e.score(e.ROOT);newscore=e.score(newroot)

    def graph_by_path_arithmetic(rows):
        # Independent of the incoming ordered-interval graph check: literally
        # apply the register language's binary increment/strip operations,
        # then decode the resulting word with zero padding through a trie.
        trie={}
        for i,(path,_,_)in enumerate(rows):
            t=trie
            for b in path:t=t.setdefault(b,{})
            assert not t;t['leaf']=i
        def decode(word):
            t=trie;i=0
            while'leaf'not in t:
                assert set(t)=={'0','1'}
                t=t[word[i]if i<len(word)else'0'];i+=1
            return t['leaf']
        out=[]
        for pc,op,k in rows:
            nxt=lambda:decode(r.inc(pc)[0])
            if op=='CI':dest=(nxt(),)
            elif op=='CD':dest=(decode(r.inc(r.strip(pc,'0',1))[0]),nxt())
            elif op=='CB':dest=(decode(r.inc(r.strip(pc,'0',k))[0]),)
            elif op=='CC':dest=(decode(r.strip(pc,'1',k)),)
            elif op=='CH':dest=('HALT',)
            else:raise AssertionError(op)
            out.append((op,k,dest))
        return out
    assert graph_by_path_arithmetic(baseline)==graph_by_path_arithmetic(newrows)

    Q='1110100101'
    P='1110100100110110101010011100001'
    assert not Q.startswith(P)and not P.startswith(Q)
    head=[(Q+p,o,k)for p,o,k in [('00','CD',5),('0100','CD',5),
        ('010100','CD',5),('010101','CC',1),('01011','CB',1),('011','CH',None)]]
    def nip_rewrite(rows):
        return tuple(sorted([x for x in rows if not x[0].startswith(Q)]+head+
            [(Q+'1'+p[len(Q)+2:],o,k)for p,o,k in rows if p.startswith(Q+'11')]))
    def rotation_paths(rows):
        out=[]
        for p,o,k in rows:
            if p.startswith(P):
                z=p[len(P):]
                if z.startswith('0'):p=P+'00'+z[1:]
                elif z.startswith('10'):p=P+'01'+z[2:]
                elif z.startswith('11'):p=P+'1'+z[2:]
                else:raise AssertionError(z)
            out.append((p,o,k))
        return tuple(out)
    assert rotation_paths(baseline)==newrows
    nj=json.loads((args.kit/'nip_source.json').read_text());ns=nj['structures']
    @cache
    def inter(n):
        x=ns[n]
        return e.I[tuple(x)]if isinstance(x[0],str)else e.cons(inter(x[0]),inter(x[1]))
    niproot=inter(nj['root']);niprows=tuple(e.paths(niproot))
    assert nip_rewrite(baseline)==niprows
    joint=e.replace(niproot,234,e.cons(e.cons(233,122),115))
    jointrows=tuple(e.paths(joint))
    assert jointrows==nip_rewrite(newrows)==rotation_paths(niprows)
    assert e.score(joint)==(224,6,49)and len(jointrows)==6449

    table=r.table(args.machines/'zfc236_old.tm')
    attempt=dict(table);attempt.update(nip.PATCH)
    assert len({q for q,b in table})==len({q for q,b in attempt})==236
    site=['01010','CI',8];values=[0]*9;want,_=r.expected(site,values,[0])
    good,ng,_=r.run(table,site[0],values);bad,nb,_=r.run(attempt,site[0],values)
    assert good==want and bad!=want
    receipt=dict(status='PASS_SOURCE_COMPATIBILITY_AND_REJECT_NAIVE_BINARY_GRAFT',
        old_source_score=oldscore,rotated_source_score=newscore,nip_rotated_score=e.score(joint),
        nip_rotated_leaves=len(jointrows),disjoint_prefixes=[P,Q],source_rewrites_commute=True,
        original_ordered_occurrences=6455,changed_rotation_paths=sum(a[0]!=b[0]for a,b in zip(baseline,newrows)),
        independently_equal_control_graphs=True,graph_method='Binary increment/strip followed by zero-padded trie dispatch',
        note='Exact ordered-CFG equality transports register invariants by occurrence index; the separately certified NIP precondition remains required.',
        literal236_sha256=hashlib.sha256((args.machines/'zfc236_old.tm').read_bytes()).hexdigest(),
        counterexample=dict(site=site,logical_registers=values,spares=[0],baseline236_steps=ng,
            altered236_steps=nb,tape_xor=sorted(want[2]^bad[2])),
        conclusion='Source-only combination retains224 DAGnodes. The unchanged five-row NIP graft is invalid even on236; no235-state table is claimed.')
    args.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
