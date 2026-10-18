#!/usr/bin/env python3
"""Map the single cache-MP continuation change onto existing decoder entries.

The unchanged low-level states at every ancestor remain available. Complete
conditional instruction checks are supplied independently by check_rotation252.
"""
import rotation_search252 as r
from functools import lru_cache
import hashlib,json

def main():
    new={};seen={};entries={}
    def intern(a,b,old):
        if (a,b) not in seen:seen[a,b]=len(new);new[len(new)]=a,b
        n=seen[a,b]
        v=r.OLD['state_entries'][str(old)]
        if str(n) in entries:assert entries[str(n)]==v
        entries[str(n)]=v
        return ('N',n)
    @lru_cache(None)
    def regular(e):return intern(*map(regular,r.NODES[e[1]]),e[1]) if e[0]=='N' else e
    def rec(e,p):
        if p=='111111':return regular(('N',172))
        if e[0]!='N':return e
        if not '111111'.startswith(p):return regular(e)
        return intern(rec(r.NODES[e[1]][0],p+'0'),rec(r.NODES[e[1]][1],p+'1'),e[1])
    root=rec(('N',r.ROOT),'')[1]
    @lru_cache(None)
    def fingerprint(e):
        text='N('+','.join(fingerprint(x) for x in new[e[1]])+')' if e[0]=='N' else ':'.join(map(str,e))
        return hashlib.sha256(text.encode()).hexdigest()
    data={'root':root,'nodes':new,'fingerprints':{str(n):fingerprint(('N',n)) for n in new},'state_entries':entries,'leaf_entries':r.OLD['leaf_entries'],'opaque_cuts':[],'warning':'Entry correspondence transports exact unchanged ancestor states through one decoder-edge edit. Certified only by accompanying complete conditional affine check; no kernel proof.'}
    (r.HERE/'mp-cache-decoder-entries.json').write_text(json.dumps(data,indent=2)+'\n')

if __name__=='__main__':main()
