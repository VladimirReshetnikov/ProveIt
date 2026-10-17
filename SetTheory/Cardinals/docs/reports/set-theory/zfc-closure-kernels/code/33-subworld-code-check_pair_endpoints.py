"""Exhaustive finite regression for raw Kuratowski endpoint uniqueness.

No Extensionality, Foundation, or set axioms are assumed. Enumerate every
binary membership structure with 1,2,3,4 objects, including duplicate incoming
profiles and self-membership. A successful run is supporting finite evidence,
not a proof of the theorem for arbitrary structures.
"""
from collections import defaultdict
import json

def check_size(n):
    result={'objects':n,'structures':0,'ordered_pair_witnesses':0,
            'structures_with_codes':0,'nonextensional_structures_with_codes':0,
            'self_member_structures_with_codes':0,'max_codes_for_same_endpoints':0}
    for table in range(1 << (n*n)):
        extensions=[(table >> (n*j)) & ((1<<n)-1) for j in range(n)]
        reps=defaultdict(list)
        for j,ext in enumerate(extensions): reps[ext].append(j)
        endpoints={}
        codes_by_pair=defaultdict(set)
        witnesses=0
        for a in range(n):
            for b in range(n):
                for u in reps.get(1<<a,[]):
                    for v in reps.get((1<<a)|(1<<b),[]):
                        for t in reps.get((1<<u)|(1<<v),[]):
                            pair=(a,b)
                            if t in endpoints and endpoints[t]!=pair:
                                raise AssertionError((n,table,t,endpoints[t],pair))
                            endpoints[t]=pair
                            codes_by_pair[pair].add(t)
                            witnesses+=1
        result['structures']+=1
        result['ordered_pair_witnesses']+=witnesses
        if endpoints:
            result['structures_with_codes']+=1
            result['nonextensional_structures_with_codes']+=(len(reps)<n)
            result['self_member_structures_with_codes']+=any(
                ext&(1<<i) for i,ext in enumerate(extensions))
            result['max_codes_for_same_endpoints']=max(
                result['max_codes_for_same_endpoints'],
                max(map(len,codes_by_pair.values())))
    return result

if __name__=='__main__':
    print(json.dumps({'status':'PASS','results':[check_size(n) for n in range(1,5)]},
                     indent=2,sort_keys=True))
