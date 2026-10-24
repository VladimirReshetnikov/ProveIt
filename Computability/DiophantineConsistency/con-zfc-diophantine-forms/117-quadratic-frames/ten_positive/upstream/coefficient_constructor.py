#!/usr/bin/env python3
"""Closed compact44 numerals and full state/color conjugacy; no old emitter."""
import argparse
import gzip
import hashlib
import json
import sys
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'candidates/one-page-ordinary13'
ALPHABET='0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'

def need(ok,message):
    if not ok:raise ValueError(message)
def sha(b):return hashlib.sha256(b).hexdigest()

def decode(literal):
    A=sum(ALPHABET.index(ch)*62**i for i,ch in enumerate(reversed(literal)))
    N=A%2**636;T=A//2**636%2**1675;E=A//2**2311
    D=lambda b,x,j:x//b**j%b
    nu=[D(2,N,j) for j in range(430)];marks=[D(2,N,430+q)for q in range(215)]
    flags=[14*(1-marks[q])+marks[q]*D(16,E,sum(marks[:q]))for q in range(215)]
    actions=[]
    for j in range(430):
        u=nu[j]*(1+sum(nu[:j]))+(1-nu[j])*D(216,T,j-sum(nu[:j]))
        v=D(2,flags[j//2],2*(j%2));right=D(2,flags[j//2],2*(j%2)+1)
        need(0<=u<=215,'decoded target')
        actions.append([j//2,j%2,v,2*right-1,u])
    need(actions[0][2:4]==[1,1],'actual first action is write1/right')
    return actions

def language(actions):
    R=sorted({t for q,b,v,m,t in actions if m==1});L=sorted({t for q,b,v,m,t in actions if m==-1})
    need((len(R),len(L))==(199,45),'right/left target sets')
    right={q:j+6 for j,q in enumerate(R)};left={q:j+205 for j,q in enumerate(L)}
    hd=lambda q,b:2*(q+1)+b
    tiles={(0,hd(q,b),right[t],v)if m==1 else(left[t],hd(q,b),0,v)for q,b,v,m,t in actions}
    tiles.update((0,hd(215,b),0,hd(215,b))for b in (0,1));tiles.update((0,b,0,b)for b in(0,1))
    tiles.update((right[q],b,0,hd(q,b))for q in R for b in(0,1))
    tiles.update((0,b,left[q],hd(q,b))for q in L for b in(0,1))
    tiles.update((0,c,0,438)for c in(0,1,432,433))
    # The constructor executes the actual first action. Its target must be
    # renamed along with the machine; it is not the old literal state93.
    initializer=(3,436,4,hd(actions[0][4],0))
    tiles.update([(2,434,2,0),(2,435,3,1),initializer,(4,436,4,0)])
    tiles.update((1,438,1,c)for c in(434,435,436))
    tiles.update((a,437,b,437)for a in(0,1,4)for b in(0,1,2));tiles.add((5,0,0,0))
    start,forbidden=(2,435,3,1),(5,0,0,0)
    ordered=[start,forbidden]+sorted(tiles-{start,forbidden})
    need(len(ordered)==943,'distinct complete943 language')
    return ordered,right,left,initializer

def construct(actions):
    tiles,right,left,init=language(actions);rho=2**67;B=rho**8807
    need(all(all(0<=t[s]<(256,512,256,512)[s]for s in range(4))for t in tiles),'every native label within its original port width')
    pos=[*range(8),34,*range(8,17),35,*range(17,25),36,*range(25,34),37,38,39,40]
    starts=[0,9,19,28];widths=[9,10,9,10];occupied=[256,512,256,512];offsets=[1023,1013,1003,983]
    c={i:1+2**51-sum(2**(10+pos[starts[s]+j])for s,x in enumerate(t)for j in range(widths[s])if(x+occupied[s])>>j&1)
         -sum(2**(10+pos[j])for j in range(38,41))for i,t in enumerate(tiles)}
    for s in range(4):
        for j in range(widths[s]):c[offsets[s]+j]=2**(10+pos[starts[s]+j])
    for j,e in enumerate([1095,2195,3296]):c[e]=2**(48+j)
    c[1063]=c[1064]=0;E=set(c);need(len(E)==986,'complete support')
    need(all(cc>=0 for cc in c.values()),'all aggregate coefficients nonnegative')
    # Independently expand exactly the page's shorter Phi prescription.
    keys=[2**30*w+2**20*n+2**10*e+s for w,n,e,s in tiles]
    ranks=[0,1]+[2+sum((2**40+keys[i]-keys[j]-1)//2**40 for j in range(2,943))for i in range(2,943)]
    need(ranks==list(range(943)),'printed floor ranks equal complete native order')
    phi={ranks[i]:1+2**51-2**10*(w+2**8*n+2**17*e+2**25*s+127*2**34)
         for i,(w,n,e,s)in enumerate(tiles)}
    copies=[(10,1023,8),(18,1013,9),(27,1003,8),(35,983,9),
            (44,1031,1),(45,1022,1),(46,1011,1),(47,992,1),(48,1095,1),(49,2195,1),(50,3296,1)]
    for b,e,m in copies:
        for j in range(m):phi[e+j]=phi.get(e+j,0)+2**(b+j)
    need(phi=={e:cc for e,cc in c.items()if cc},'every printed Phi coefficient')
    dc={e:1 for e in(30,62,1100,2201)}
    for e,cc in c.items():
        for target in(4393,5495):dc[target-e]=dc.get(target-e,0)+cc
    need(max(dc)+max(E)==8791 and 42+max(E)<8792 and 2*max(E)<8807,'all padding and circumference ranges preserved')
    DC=sum(cc*rho**e for e,cc in dc.items());DR=rho**42
    denominator=rho**3296;numerator=sum(cc*rho**(3296-e)for e,cc in phi.items())
    reciprocal=(rho**4393+rho**5495)*numerator
    need(reciprocal%denominator==0,'printed reciprocal expression exactly integral')
    need(DC+B*DR==sum(rho**e for e in(30,62,1100,2201,8849))+reciprocal//denominator,'entire printed K reciprocal identity')
    MC=B-1-sum(rho**e for e in E if e!=1)-2*rho**1063
    mf=4+(2**51-2)*(rho**4393+rho**5495)
    mf+=sum(rho**(1013+j)for j in range(10))+sum(rho**(1065+j)for j in range(9))+rho**2195+rho**3296
    mf+=(2**65-1)*sum(rho**e for e in range(8792,8805))+(2**19-1)*rho**8805
    ports={'beta':B-1,'K':DC+B*DR,'MC':MC,'MF_source':mf+B-1}
    mass=988*(2*sum(c.values())+6);need(4*mass+8<rho and 2*(2**51-2)+4<rho,'uniform carry bound')
    need(0<DC<B and 0<MC<B-1 and 0<mf<B-1,'authentic coefficient bounds')
    need(MC.bit_count()==590069-986 and mf.bit_count()==986,'balanced mask populations')
    need(MC%4==2 and mf%8==4,'source congruences')
    targets=[(1013+j,{983+j},set(),{1013+j})for j in range(10)]
    targets +=[(1065+j,{1003+j},{1023+j},set())for j in range(9)]+[(2195,{1095},set(),{2195}),(3296,{1095},set(),{3296})]
    checks=0
    for t,aa,bb,cc in targets:
        for e in E:
            need(dc.get(t-e,0)==int(e in aa) and int(e+42==t)==int(e in bb) and int(e==t)==int(e in cc),'complete native overlap')
            checks+=3
    for t in(4393,5495):
        for e in E:
            need(dc.get(t-e,0)==c[e] and e+42!=t,'complete clause overlap');checks+=2
    need({(4393-e)%8807 for e in E}.isdisjoint({(5495-e)%8807 for e in E}),'two clause bands')
    need({(2195-e)%8807 for e in E}&{(3296-e)%8807 for e in E}=={0},'anchor alignment')
    controller=[]
    for p in(67,8807,581197):
        BB=B%p;bracket=(1+BB*DC+BB*BB*(DR+1))%p
        need((BB*BB-1)%p and bracket,'native rank controller unit')
        controller.append({'prime':p,'B':BB,'B2minus1':(BB*BB-1)%p,'bracket':bracket})
    return ports,tiles,{'basis_convolution_checks':checks,'mass':mass,'carry_threshold':4*mass+8,'radix':rho,
      'controller':controller,'initializer':list(init),'initializer_sorted_rank':tiles.index(init),
      'all943_floor_ranks_exact':True,'every_printed_Phi_coefficient_exact':True,'entire_reciprocal_K_exact':True,
      'label_widths_and_padding_geometry_preserved':True}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=OUT);args=ap.parse_args();out=args.output;out.mkdir(exist_ok=True,parents=True)
    literal=(out/'SEED.txt').read_text().strip();new=decode(literal)
    src=ROOT/'con-zfc-diophantine-forms/36-small-tuple/coefficients/k215_transitions.json'
    old=json.loads(src.read_text())['transitions'];d={(q,b):(v,m,t)for q,b,v,m,t in old};order=[0];pi={0:0}
    for q in order:
        for b in(0,1):
            t=d[q,b][2]
            if t<215 and t not in pi:pi[t]=len(order);order.append(t)
    pi[215]=215;need(len(pi)==216 and pi[0]==0 and pi[215]==215,'complete start/halt-preserving BFS bijection')
    expected=sorted([[pi[q],b,v,m,pi[t]]for q,b,v,m,t in old]);need(new==expected,'every430 transition conjugacy')
    oldports,oldtiles,_=construct(old);ports,tiles,audit=construct(new)
    oldlang,orr,oll,_=language(old);newlang,nrr,nll,_=language(new)
    hm={c:c for c in range(6)};hm.update({orr[q]:nrr[pi[q]]for q in orr});hm.update({oll[q]:nll[pi[q]]for q in oll})
    vm={0:0,1:1,**{c:c for c in range(434,439)}}
    vm.update({2*(q+1)+b:2*(pi[q]+1)+b for q in range(216)for b in(0,1)})
    need(set(hm)==set(range(250)) and set(hm.values())==set(range(250)),'complete horizontal color bijection')
    need(set(vm)==set(range(439)) and set(vm.values())==set(range(439)),'complete vertical color bijection')
    mapped={(hm[w],vm[n],hm[e],vm[s])for w,n,e,s in oldlang};need(mapped==set(newlang),'every943 tile color conjugacy')
    need(sha((json.dumps(oldtiles,separators=(',',':'))+'\n').encode())=='66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f','original literal943 language')
    for name,value in oldports.items():
        raw=value.to_bytes((value.bit_length()+7)//8,'little')
        need(raw==gzip.decompress((ROOT/'con-zfc-diophantine-forms/44-b4-sparse/native/coefficients'/(name+'.bin.gz')).read_bytes()),'original whole compact44 numeral')
    records=[];(out/'coefficients').mkdir(exist_ok=True)
    for name,value in ports.items():
        raw=value.to_bytes((value.bit_length()+7)//8,'little');(out/'coefficients'/(name+'.bin.gz')).write_bytes(gzip.compress(raw,mtime=0))
        records.append({'port':name,'bits':value.bit_length(),'raw_bytes':len(raw),'raw_sha256':sha(raw),'unchanged_original_bytes':value==oldports[name]})
    receipt={'status':'PASS','python_optimization':sys.flags.optimize,
      'scope':'Closed finite coefficient construction and full state/color conjugacy. Ordinary uniform native and adaptive/Pell arguments remain mathematical dependencies; no Lean/internal-ZFC proof.',
      'source_transition_sha256':sha(src.read_bytes()),'seed_characters':len(literal),'all430_transition_conjugacies':True,'all943_tile_conjugacies':True,'first_action':new[0],
      'original44_whole_tuple_bytes_authenticated':True,
      'original44_raw_hashes':{n:sha(v.to_bytes((v.bit_length()+7)//8,'little'))for n,v in oldports.items()},
      'horizontal_colors':250,'vertical_colors':439,'both_color_maps_bijective':True,
      'ports':records,'native_finite_audit':audit,'old_to_new':[pi[q]for q in range(216)]}
    (out/('VERIFY_OPTIMIZED.json'if not __debug__ else'VERIFY.json')).write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
