"""Ranked boundary matching for action-quotient simulation.

Visible actions may enter any finite silent suffix with the required next
action class. A silent boundary must reduce its exact original jump rank.
This forbids infinite silent stuttering while allowing different PC words.
"""
from action_contract import normalizer

def make_matcher(canon,nodes,quotient,successor):
    normalize=normalizer(nodes,successor)
    def matches(left,right,target):
        l,r=canon(left,right)
        if l!=((1,0,1),) or len(r)<3:return False
        if r[-1]!=('box',('plain',target['effect'])) or r[-2]!=(1,0,1):return False
        gap=r[-3]
        if len(gap)!=3 or gap[0]!=0:return False
        prefix=r[:-3]
        if any(len(s)!=3 or s[0] not in (0,1) or s[1]!=0 for s in prefix):return False
        length=sum(s[2] for s in prefix)
        if gap[1]<0 or gap[2]+length<40:return False
        pc=''.join(str(b)*c for b,a,c in prefix)
        try:_,chain,terminal=normalize(pc)
        except AssertionError:return False
        return (quotient['classes'][terminal[0]]==target['class'] and
                len(chain)<=target['rank_limit'])
    return matches
