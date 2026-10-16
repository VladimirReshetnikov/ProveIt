#!/usr/bin/env python3
"""Independently replay every state-distinction certificate against the table.

No generator code is imported. Only Python's standard library is needed.
"""
from pathlib import Path
import hashlib, json

HERE=Path(__file__).resolve().parent
SHA='84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95'

def require(condition,message):
    if not condition: raise ValueError(message)

def read_machine():
    raw=(HERE/'zfc_253.tm').read_bytes()
    require(hashlib.sha256(raw).hexdigest()==SHA,'literal table hash')
    transitions={}; start=[]
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '): start.append(int(line[9:]))
        elif line and not line.startswith('#'):
            cells=line.split(); require(len(cells)==5,'row length')
            q,b,w=int(cells[0]),int(cells[1]),int(cells[2])
            d,r=cells[3],int(cells[4])
            require((q,b) not in transitions,'duplicate row')
            require(w in (0,1) and d in ('L','R') and 0<=r<=253,'row output')
            transitions[q,b]=(w,d,r)
    require(start==[0],'blank start state')
    require(set(transitions)=={(q,b) for q in range(253) for b in (0,1)},'all506 rows')
    return transitions

def separates(table,a,b,word,support):
    # Iterative version of the elementary word-length induction.
    for i,symbol in enumerate(word):
        if a==b or a==253 or b==253 or symbol not in '01': return False
        bit=int(symbol)
        if (a,bit) not in support or (b,bit) not in support: return False
        wa,da,ra=table[a,bit]; wb,db,rb=table[b,bit]
        if (wa,da)!=(wb,db): return i+1==len(word)
        a,b=ra,rb
    return (a==253)!=(b==253)

def main():
    table=read_machine()
    package=json.loads((HERE/'quotient_certificate.json').read_text())
    require(package['machine_sha256']==SHA,'certificate source hash')
    all_pairs={(a,b) for a in range(254) for b in range(a+1,254)}
    for name,omitted,allowed in [('complete_table',set(),set()),
                                ('omit_initializer_row',{(0,0)},{(0,2)})]:
        certificate=package[name]; support=set(table)-omitted
        claims={tuple(map(int,key.split(','))):value for key,value in certificate['words'].items()}
        require(set(claims)==all_pairs-allowed,'exact pair coverage: '+name)
        require({tuple(p) for p in certificate['unseparated_pairs']}==allowed,'exception list: '+name)
        for (a,b),word in claims.items():
            require(separates(table,a,b,word,support),f'invalid word for {name}:{a},{b}')
        histogram={}
        for word in claims.values():histogram[str(len(word))]=histogram.get(str(len(word)),0)+1
        require(certificate['word_length_histogram']==histogram,'word histogram: '+name)
        require(certificate['maximum_word_length']==max(map(len,claims.values())),'word maximum: '+name)
        if allowed:
            # Confirm the sole surviving identification really is a quotient
            # of the 505 supported rows; this is conditional on omitting 0/0.
            image={}
            rename=lambda q:0 if q==2 else q
            for (q,bit),(w,d,r) in table.items():
                if (q,bit) not in support: continue
                key=(rename(q),bit);value=(w,d,rename(r))
                require(key not in image or image[key]==value,'surviving quotient conflict')
                image[key]=value
        print(name+': all '+str(len(claims))+' distinction words replayed; working-state exceptions '+str(sorted(allowed)))
    print('PASS: complete table admits no strict literal one-step state quotient.')
    print('This is not a lower bound for all Turing machines with the same halting behavior.')

if __name__=='__main__':main()
