#!/usr/bin/env python3
"""Finite binary tape → literal source input. No simulation in the loader."""
import argparse,json,math,hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parent
SOURCE_SHA256='fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3'

def natural(x,name):
    if type(x) is not int or x<0:raise ValueError(name+' must be an exact natural integer')
    return x

def bits(word):
    if type(word) is not str or any(c not in '01' for c in word):raise ValueError('Tape halves must be finite binary strings')
    return sum((ord(c)-48)<<i for i,c in enumerate(word))

def from_counters(L,R,T=0,cofactor=1):
    for k,v in [('L',L),('R',R),('T',T),('cofactor',cofactor)]:natural(v,k)
    if cofactor<1 or math.gcd(cofactor,2310)!=1:raise ValueError('cofactor must be positive and coprime to 2310')
    return dict(control='START',counter0=cofactor*2**L*3**R*5**T,counter1=0)

def from_tape(left,right):
    """Both halves nearest head first; omitted bits and the scanned bit are zero."""
    return from_counters(bits(left),bits(right))

def target_ledger():
    raw=(ROOT/'source.json').read_bytes()
    if hashlib.sha256(raw).hexdigest()!=SOURCE_SHA256:raise ValueError('Source does not match the audited literal-source pin')
    s=json.loads(raw);m=len(s['controls']);p=sum(e['delta']!=0 for e in s['branches']);a=len(s['branches'])-p;J=s['class_cut']
    D=2*(m+2*p);S=2*D+2;B2=D+1;L=3*D+4;B3=4*D+5;Z=10*B3+10+2*J
    pair=4*p;triple=8*p*D+23*p+m;context=2*p+a
    return dict(m=m,p=p,a=a,J=J,D=D,S=S,B2=B2,L=L,B3=B3,Z=Z,pair_factors=pair,unguarded_triple_factors=triple,contextual_triple_factors=context,factors=pair+triple+context,radius=pair*(6*D+8)+triple*(24*D+32)+context*(Z+J+12*D+16),observer_length=3*D+3,particles=5,alphabet=[0,1])

def five_particle_input(data):
    """Validated clean source input → five-particle coordinates, no gates."""
    if type(data) is not dict or any(type(k) is not str for k in data) or set(data)!=set(('control','counter0','counter1')):raise ValueError('Expected exact source input object')
    if type(data['control']) is not str or data['control']!='START':raise ValueError('Expected START input from this loader')
    A=natural(data['counter0'],'counter0');B=natural(data['counter1'],'counter1')
    if A==0 or B!=0 or A%7==0 or A%11==0:raise ValueError('Clean source input requires A>0, B=0 and no factors 7 or 11')
    g=target_ledger()
    # START is first in controls; hence its plus home gap equals1.
    return sorted((-g['Z']-A,0,g['Z']+B,g['S'],g['S']+1))

if __name__=='__main__':
    a=argparse.ArgumentParser(description=__doc__);a.add_argument('--left',default='');a.add_argument('--right',default='');a.add_argument('--particles',action='store_true');v=a.parse_args();out=from_tape(v.left,v.right)
    # Hex avoids interpreter decimal-string limits; source counters are exact integers in API.
    printable=dict(control=out['control'],counter0_hex=hex(out['counter0']),counter1_hex=hex(out['counter1']))
    if v.particles:printable['five_particle_positions_hex']=[hex(x) for x in five_particle_input(out)]
    print(json.dumps(printable,indent=2))
