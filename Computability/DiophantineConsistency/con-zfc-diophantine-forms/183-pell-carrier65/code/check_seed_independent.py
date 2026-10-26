#!/usr/bin/env python3
"""Independent finite action-stream audit of the reverse-discovery recipe.

Uses successive quotient/remainder extraction rather than prefix-product
floor extraction. Reads the literal from the actual combined TeX.
"""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parents[1]
def need(ok,msg):
    if not ok:raise ValueError(msg)
alphabet='0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
def value(s):
    n=0
    for c in s:n=62*n+alphabet.index(c)
    return n
def literal(path):return ''.join(re.findall(r'^([A-Za-z0-9]+)\\par$',path.read_text(),re.M))
old=value(literal(HERE/'sources/CURRENT_P66.tex'))
newlit=literal(HERE/'equation.tex');new=value(newlit)
need(len(newlit)==399,'Actual printed seed length')
Nold=old%(2**636);Nnew=new%(2**636)
need(Nold==Nnew,'Complete discovery/flag-mask field unchanged')
oldtargets=(old//2**636)%2**1675
oldflags=old//2**2311
payload=new//2**636
sig=0;actions_old=[];actions_new=[];rads=[];digits=[]
for j in range(430):
    discovery=(Nold//2**j)%2
    oldtarget=sig+1 if discovery else (oldtargets//216**(j-sig))%216
    radix=1 if discovery else sig+2
    payload,digit=divmod(payload,radix)
    target=(sig+discovery-digit)%216
    need(target==oldtarget,'Target mismatch at '+str(j))
    need(digit==0 if discovery else 0<=digit<radix,'Digit range')
    rads.append(radix);digits.append(digit)
    actions_old.append(oldtarget);actions_new.append(target)
    sig+=discovery
need(sig==214,'All active states discovered')
need(payload==oldflags,'Complete flag-nibble field unchanged')
need([j for j,u in enumerate(actions_new) if u==215]==[125],'Actual halt index')
need(actions_new[0]==1,'Actual first target')
sigma125=sum((Nold//2**j)%2 for j in range(125))
need(sigma125==80 and digits[125]==81,'Early-halt reverse distance')
P=1;T=0
for d,r in zip(digits,rads):T+=d*P;P*=r
need(0<=T<P,'All digit contribution bounded by terminal prefix')
need(Nold+2**636*(T+P*oldflags)==new,'Independent re-encoding equals printed numeral')
# Validate all write/move flags from the identical recovered field.
def flags(E):
    out=[];qoffset=0
    for q in range(215):
        bit=(Nold//2**(430+q))%2
        word=14+bit*((E//16**qoffset)%16-14)
        out.extend([((word//2**(2*b))%2,(word//2**(2*b+1))%2) for b in (0,1)])
        qoffset+=bit
    return out
need(flags(payload)==flags(oldflags),'All 860 write/move bits unchanged')
result={'status':'PASS','printed_seed_characters':len(newlit),'printed_seed_bits':new.bit_length(),
        'targets_checked':430,'write_move_bits_checked':860,'new_states':sig,
        'unique_halt_action':125,'halt_discovery_count':sigma125,
        'independent_method':'successive divmod, backwards re-encoding',
        'complete_combined_tex_sha256':hashlib.sha256((HERE/'equation.tex').read_bytes()).hexdigest(),
        'scope':'Finite decoder identity; combined front visually checked separately; no native proof replay.'}

print(json.dumps(result,indent=2,sort_keys=True))
