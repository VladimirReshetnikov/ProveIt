#!/usr/bin/env python3
"""Build the complete directly indexed language and its fresh native tuple."""
import argparse
from copy import deepcopy
from hashlib import sha256
import gzip,json
from math import gcd
import sys
sys.dont_write_bytecode=True
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
BASE=ROOT/'candidates/one-page-short10'
ALPHABET='0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
def need(ok,why):
    if not ok:raise ValueError(why)
def decode():
    literal=(BASE/'SEED.txt').read_text().strip();A=0
    for c in literal:A=62*A+ALPHABET.index(c)
    N=A%(1<<636);T=A//(1<<636)%(1<<1675);E=A>>2311
    nu=[N>>j&1 for j in range(430)];mark=[N>>(430+q)&1 for q in range(215)]
    flags=[14*(1-mark[q])+mark[q]*(E//16**sum(mark[:q])%16) for q in range(215)]
    actions=[]
    for j in range(430):
        q,b=divmod(j,2);sig=sum(nu[:j]);u=nu[j]*(1+sig)+(1-nu[j])*(T//216**(j-sig)%216)
        v=flags[q]>>(2*b)&1;d=flags[q]>>(2*b+1)&1;actions.append([q,b,v,2*d-1,u])
    original=json.loads((ROOT/'con-zfc-diophantine-forms/36-small-tuple/coefficients/k215_transitions.json').read_bytes())['transitions'];look={(q,b):t for q,b,v,m,t in original};pi={0:0};order=[0]
    for q in order:
        for b in [0,1]:
            t=look[q,b]
            if t<215 and t not in pi:pi[t]=len(order);order.append(t)
    pi[215]=215;need(len(pi)==216 and actions==sorted([[pi[q],b,v,m,pi[t]] for q,b,v,m,t in original]),'entire430 BFS conjugacy')
    return actions,original,pi

def language(actions,indexed=True):
    R=sorted({t for q,b,v,m,t in actions if m==1});L=sorted({t for q,b,v,m,t in actions if m==-1})
    need((len(R),len(L))==(199,45),'target color domains')
    right={q:j+6 for j,q in enumerate(R)};left={q:j+205 for j,q in enumerate(L)};h=lambda q,b:2*(q+1)+b
    tiles={0:(2,435,3,1),1:(5,0,0,0)}
    for j,(q,b,v,m,u) in enumerate(actions):tiles[j+2]=(0,h(q,b),right[u],v) if m==1 else (left[u],h(q,b),0,v)
    for b in [0,1]:tiles[432+b]=(0,h(215,b),0,h(215,b));tiles[434+b]=(0,b,0,b)
    for q in R:
        for b in [0,1]:tiles[424+2*right[q]+b]=(right[q],b,0,h(q,b))
    for q in L:
        for b in [0,1]:tiles[424+2*left[q]+b]=(0,b,left[q],h(q,b))
    for j in range(4):tiles[924+j]=(0,j+430*(j//2),0,438)
    tiles.update({928:(2,434,2,0),929:(3,436,4,h(actions[0][4],0)),930:(4,436,4,0)})
    for t in [434,435,436]:tiles[497+t]=(1,438,1,t)
    for a in [0,1,4]:
        for b in [0,1,2]:tiles[934+3*a+b-6*(a//4)]=(a,437,b,437)
    need(set(tiles)==set(range(943)) and len(set(tiles.values()))==943,'entire943 explicit exhaustive distinct indices')
    ordered=[tiles[i] for i in range(943)]
    if not indexed:ordered=ordered[:2]+sorted(ordered[2:])
    return ordered,right,left

def construct(tiles):
    rho=1<<67;B=1<<590069;E=set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296}
    c={i:1+(1<<51)-(1<<10)*(w+(1<<8)*n+(1<<17)*e+(1<<25)*s+127*(1<<34)) for i,(w,n,e,s) in enumerate(tiles)}
    copies=[(10,1023,8),(18,1013,9),(27,1003,8),(35,983,9),(44,1031,1),(45,1022,1),(46,1011,1),(47,992,1),(48,1095,1),(49,2195,1),(50,3296,1)]
    for b,e,m in copies:
        for j in range(m):c[e+j]=1<<(b+j)
    c[1063]=c[1064]=0;need(set(c)==E and len(E)==986 and min(c.values())>=0,'complete986 native support')
    dc={e:1 for e in [30,62,1100,2201]}
    for e,v in c.items():
        for t in [4393,5495]:dc[t-e]=dc.get(t-e,0)+v
    DC=sum(v*rho**e for e,v in dc.items());DR=rho**42
    MC=B-1-sum(rho**e for e in E if e!=1)-2*rho**1063
    mf=4+((1<<51)-2)*(rho**4393+rho**5495)+sum(rho**(1013+j) for j in range(10))+sum(rho**(1065+j) for j in range(9))+rho**2195+rho**3296
    mf+=((1<<65)-1)*sum(rho**e for e in range(8792,8805))+((1<<19)-1)*rho**8805
    mass=988*(2*sum(c.values())+6);need(4*mass+8<rho and 0<DC<B and 0<MC<B-1 and 0<mf<B-1,'all native bounds')
    targets=[(1013+j,{983+j},set(),{1013+j}) for j in range(10)]+[(1065+j,{1003+j},{1023+j},set()) for j in range(9)]+[(2195,{1095},set(),{2195}),(3296,{1095},set(),{3296})]
    checks=0
    for t,a,b,cc in targets:
        for e in E:
            need(dc.get(t-e,0)==int(e in a) and int(e+42==t)==int(e in b) and int(e==t)==int(e in cc),'all native-copy overlap identities');checks+=3
    for t in [4393,5495]:
        for e in E:need(dc.get(t-e,0)==c[e] and e+42!=t,'all native-clause overlap identities');checks+=2
    need({(4393-e)%8807 for e in E}.isdisjoint({(5495-e)%8807 for e in E}) and {(2195-e)%8807 for e in E}&{(3296-e)%8807 for e in E}=={0},'whole-cell clause/anchor separation')
    need(MC.bit_count()==590069-986 and mf.bit_count()==986 and MC%4==2 and mf%8==4,'complete mask populations and congruences')
    controller=[]
    for p in [67,8807,581197]:
        bb=B%p;H0=(1+bb*(DC%p)+bb*bb*(DR+1))%p;need((bb*bb-1)%p and H0,'new native rank-controller unit');controller.append(dict(prime=p,B=bb,B2minus1=(bb*bb-1)%p,H0=H0))
    return {'beta':B-1,'K':DC+B*DR,'MC':MC,'MF_source':mf+B-1},dict(native_basis_checks=checks,carry_threshold=4*mass+8,controller=controller)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');args=ap.parse_args()
    pins=json.loads((HERE/'SOURCE_PINS.json').read_bytes())
    for name,h in pins['files'].items():need(sha256((ROOT/name).read_bytes()).hexdigest()==h,'entire frozen dependency '+name)
    actions,old,pi=decode();tiles,nr,nl=language(actions);sortedtiles,_,_=language(actions,False);oldtiles,orr,oll=language(old,False)
    hm={i:i for i in range(6)}|{orr[q]:nr[pi[q]] for q in orr}|{oll[q]:nl[pi[q]] for q in oll};vm={0:0,1:1,**{i:i for i in range(434,439)}}|{2*(q+1)+b:2*(pi[q]+1)+b for q in range(216) for b in [0,1]}
    need(set(hm)==set(hm.values())==set(range(250)) and set(vm)==set(vm.values())==set(range(439)),'complete state-induced color bijections')
    need({(hm[w],vm[n],hm[e],vm[s]) for w,n,e,s in oldtiles}==set(tiles)==set(sortedtiles),'all943 color conjugacies and indexed/sorted language equality')
    ports,audit=construct(tiles);reference,oldnative=construct(sortedtiles)
    need(actions[0][2:]==[1,1,1] and tiles[929]==(3,436,4,4),'literal initializer4 is the actual decoded first target1')
    baseline_audit=json.loads((BASE/'VERIFY.json').read_bytes())['native_finite_audit']
    need(audit['carry_threshold']==oldnative['carry_threshold']==baseline_audit['carry_threshold'],'exact unchanged oldBFS carry sum; original44 colors differ')
    records=[]
    for name,value in ports.items():
        raw=value.to_bytes((value.bit_length()+7)//8,'little');oldraw=gzip.decompress((BASE/'coefficients'/(name+'.bin.gz')).read_bytes())
        need(reference[name].to_bytes((reference[name].bit_length()+7)//8,'little')==oldraw,'complete pinned existingBFS port reconstruction')
        need((raw==oldraw)==(name!='K'),'only K changes under fresh enumeration')
        records.append(dict(port=name,bits=value.bit_length(),sha256=sha256(raw).hexdigest(),unchanged=raw==oldraw))
    def factors(n):
        result=[];p=2
        while p*p<=n:
            if n%p==0:
                result.append(p)
                while n%p==0:n//=p
            p+=1
        if n>1:result.append(n)
        return result
    def prime(n):return n>=2 and factors(n)==[n]
    orders=[];B=1<<590069;lam=581197
    for p,order in [(67,66),(8807,4403),(lam,581196)]:
        need(prime(p) and pow(B,order,p)==1 and all(pow(B,order//f,p)!=1 for f in factors(order)),'exact prime and complete multiplicative-order certificate')
        orders.append(dict(prime=p,order=order,prime_divisors=factors(order)))
    lift=pow(B,lam-1,lam*lam);need(lift==182964883980 and lift!=1 and gcd(67*8807,lam)==1,'unchanged controller lift/cofactor')
    audit.update(old_BFS_carry_threshold=baseline_audit['carry_threshold'],orders=orders,controller_lift=lift,selector_count=943,support_count=986,spatial_temporal_padding_preserved=True)
    artifacts={'TILES.json':(json.dumps(tiles,separators=(',',':'))+'\n').encode(),'SEED.txt':(BASE/'SEED.txt').read_bytes()}
    current=ROOT/'candidates/one-page-index-weight10';parent=json.loads((current/'polynomial.json').read_bytes());binding=deepcopy(parent['coefficient_binding']);binding['tuple']='whole directly indexed BFS943 compact44; Start0/Forbidden1; literal corrected initializer4; MF_source shifted once'
    records=[]
    for logical,physical in [('beta','beta'),('K0','K'),('MC','MC'),('MF','MF_source')]:
        value=ports[physical];raw=value.to_bytes((value.bit_length()+7)//8,'little');filename=physical+'.bin.gz'
        blob=gzip.compress(raw,mtime=0) if physical=='K' else (current/'coefficients'/filename).read_bytes()
        need(gzip.decompress(blob)==raw,'whole coherent regenerated payload')
        info=dict(file=filename,bits=value.bit_length(),gzip_sha256=sha256(blob).hexdigest(),raw_sha256=sha256(raw).hexdigest());binding['ports'][logical]=info;artifacts['coefficients/'+filename]=blob;records.append(dict(port=logical,**info,raw_bytes=len(raw),unchanged_raw=(physical!='K')))
    new=deepcopy(parent);new.update(name='one_page_direct_indexed_tiles_bfs44_degree360',coefficient_binding=binding,parent_sha256=sha256((current/'polynomial.json').read_bytes()).hexdigest(),proof='PROOF.md',proof_status='Whole fresh native selector-permutation/controller equivalence; unchanged free-port arithmeticfront, exactdegree360; no equality of old/new specialized polynomial or native words asserted.')
    artifacts['polynomial.json']=(json.dumps(new,indent=2,sort_keys=True)+'\n').encode();artifacts['coefficients/BINDING.json']=(json.dumps(binding,indent=2,sort_keys=True)+'\n').encode()
    certificate=dict(status='PASS',ports=records,audit=audit,all430_transition_conjugacies=True,all943_color_conjugacies=True,all943_explicit_indices=True,selector_old_to_new=[tiles.index(t) for t in sortedtiles],state_old_to_BFS=[pi[q] for q in range(216)],literal_initializer=list(tiles[929]),old_BFS_K_raw_sha256=sha256(gzip.decompress((BASE/'coefficients/K.bin.gz').read_bytes())).hexdigest(),whole_fresh_native_tuple=True,old_native_words_reused=False)
    artifacts['NATIVE_CERTIFICATE.json']=(json.dumps(certificate,indent=2,sort_keys=True)+'\n').encode()
    for name,blob in artifacts.items():
        target=HERE/name
        if args.check:need(target.read_bytes()==blob,'deterministic full generated artifact '+name)
        else:
            need(not target.exists() or target.read_bytes()==blob,'refuse changed generated artifact overwrite '+name);target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(blob)
    print(json.dumps(dict(status='PASS',optimized_python=bool(sys.flags.optimize),check_mode=args.check,artifacts={n:sha256(b).hexdigest() for n,b in artifacts.items()},whole_fresh_native_tuple=True),indent=2,sort_keys=True))
if __name__=='__main__':main()
