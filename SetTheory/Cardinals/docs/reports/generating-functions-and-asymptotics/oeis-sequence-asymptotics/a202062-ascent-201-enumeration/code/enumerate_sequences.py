#!/usr/bin/env python3
"""Independent finite-word checks and exact tree counting for A202062.

These are diagnostics, not the proof of the generating tree or cubic identity.
"""
import argparse
from collections import Counter
parser=argparse.ArgumentParser()
parser.add_argument('--check-length',type=int,default=8)
parser.add_argument('--terms',type=int,default=40)
args=parser.parse_args()

def state(word):
    maximum=max(word)
    ascents=sum(a<b for a,b in zip(word,word[1:]))
    active=[z for z in range(maximum) if not any(word[i]>z>word[j]
        for i in range(len(word)) for j in range(i+1,len(word)))]
    assert word[-1]==maximum or (active and word[-1]==active[-1])
    assert ascents+1-maximum>=1
    return len(active),ascents+1-maximum,'T' if word[-1]==maximum else 'L'

def successors(label):
    k,h,kind=label
    out=Counter({(k,h+(kind=='L'),'T'):1})
    for rank in range(1,k+1):out[rank,h,'L']+=1
    for jump in range(1,h+1):out[k+jump,h+1-jump,'T']+=1
    return out

def direct_children(word):
    ascents=sum(a<b for a,b in zip(word,word[1:]))
    return [word+(z,) for z in range(ascents+2) if not any(word[i]>z>word[j]
        for i in range(len(word)) for j in range(i+1,len(word)))]

words=[(0,)]
for n in range(1,args.check_length+1):
    next_words=[]
    for word in words:
        children=direct_children(word)
        assert Counter(map(state,children))==successors(state(word))
        next_words.extend(children)
    print('Direct transition check length',n,'prefixes',len(words),'PASS')
    words=next_words
labels=Counter({(0,1,'T'):1}); counts=[1]
for n in range(1,args.terms+1):
    counts.append(sum(labels.values())); next_labels=Counter()
    for label,count in labels.items():
        for child,multiplicity in successors(label).items():
            next_labels[child]+=count*multiplicity
    labels=next_labels
print('Exact tree counts a_0 through a_'+str(args.terms)+':')
print(', '.join(map(str,counts)))
