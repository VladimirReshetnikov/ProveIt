#!/usr/bin/env python3
"""Recheck every edge of a supplied register-program bisimulation certificate."""
from pathlib import Path
import argparse,json
import explore as e

def tree_from_sites(sites):
    trie={}
    for p,op,arg in sites:
        cur=trie
        for b in p[:-1]:cur=cur.setdefault(b,{})
        assert p[-1]not in cur
        cur[p[-1]]=('L',(e.EOP[op],)if op=='CH'else(e.EOP[op],arg))
    def go(t):
        if isinstance(t,tuple):return t
        assert set(t)=={'0','1'}
        return('N',go(t['0']),go(t['1']))
    return go(trie)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('certificate',type=Path);ap.add_argument('logical_sites',type=Path);args=ap.parse_args()
    assert __debug__
    new=tree_from_sites(json.loads(args.logical_sites.read_text()))
    data=json.loads(args.certificate.read_text());rows=data['entries']
    assert rows and data['start_pair']==0
    bit=lambda s:[b=='1'for b in s]
    entries=[(bit(a),bit(b),nz,z)for a,b,nz,z in rows]
    a,pa=e.rmpath.seg(e.ORIGINAL,[]);b,pb=e.rmpath.seg(new,[])
    assert e.rmpath.counts(a)==e.rmpath.counts(b)
    assert(pa,pb)==entries[0][:2]
    edges=0;haltpairs=0
    for i,(pa,pb,nz,z)in enumerate(entries):
        a,qa=e.rmpath.site(e.ORIGINAL,pa);b,qb=e.rmpath.site(new,pb)
        assert a==b,(i,a,b)
        if a==('halt',):assert nz is z is None;haltpairs+=1;continue
        assert a[0]=='dec'
        for target,xa,xb in((nz,e.rmpath.inc_path(qa),e.rmpath.inc_path(qb)),
                             (z,e.rmpath.brk(1,qa),e.rmpath.brk(1,qb))):
            assert type(target)==int and 0<=target<len(entries)
            ia,sa=e.rmpath.seg(e.ORIGINAL,xa);ib,sb=e.rmpath.seg(new,xb)
            assert e.rmpath.counts(ia)==e.rmpath.counts(ib),(i,ia,ib)
            assert(sa,sb)==entries[target][:2]
            edges+=1
    print(json.dumps(dict(status='PASS',scope='Register programs only; no TM table claim',pairs=len(entries),edges=edges,halt_pairs=haltpairs)))

if __name__=='__main__':main()
