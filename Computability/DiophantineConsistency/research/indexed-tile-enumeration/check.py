#!/usr/bin/env python3
"""Independent complete table/native/whole-numeral/PDF audit; no builder import."""
import argparse
from collections import Counter
import gzip
from hashlib import sha256
import json
from math import gcd
from pathlib import Path
import re,subprocess,sys,tempfile
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
BASE=ROOT/'candidates/one-page-index-weight10'
OLD=ROOT/'candidates/one-page-short10'
ALPHABET='0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
def need(ok,why):
    if not ok:raise ValueError(why)
def load(path):return json.loads(path.read_bytes())
def digest(path):return sha256(path.read_bytes()).hexdigest()
def factors(n):
    result=[];p=2
    while p*p<=n:
        if n%p==0:
            result.append(p)
            while n%p==0:n//=p
        p+=1
    if n>1:result.append(n)
    return result
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    for name,h in load(HERE/'SOURCE_PINS.json')['files'].items():need(digest(ROOT/name)==h,'complete immutable dependency '+name)
    if (HERE/'MANIFEST.json').exists():
        files=load(HERE/'MANIFEST.json')['files'];need({str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file() and p!=HERE/'MANIFEST.json'}==set(files),'closed own inventory')
        for name,h in files.items():need(digest(HERE/name)==h,'sealed whole member '+name)
    old=load(ROOT/'con-zfc-diophantine-forms/36-small-tuple/coefficients/k215_transitions.json')['transitions'];targets={(q,b):u for q,b,v,d,u in old};order=[0];pi={0:0}
    for q in order:
        for b in [0,1]:
            u=targets[q,b]
            if u<215 and u not in pi:pi[u]=len(order);order.append(u)
    pi[215]=215;need(len(pi)==216 and set(pi.values())==set(range(216)),'full start/halt-preserving state bijection')
    actions=sorted([[pi[q],b,v,d,pi[u]] for q,b,v,d,u in old])
    seed=(HERE/'SEED.txt').read_text().strip();need(len(seed)==436 and (HERE/'SEED.txt').read_bytes()==(BASE/'SEED.txt').read_bytes()==(OLD/'SEED.txt').read_bytes(),'whole literal436 seed preserved')
    A=0
    for ch in seed:A=62*A+ALPHABET.index(ch)
    N=A%(2**636);T=A//2**636%2**1675;E=A//2**2311;decoded=[];sigma=0;tau=0;flags={}
    for q in range(215):
        m=(N//2**(430+q))%2;flags[q]=14*(1-m)+m*((E//16**tau)%16);tau+=m
    for j in range(430):
        q,b=divmod(j,2);nu=(N//2**j)%2;u=nu*(sigma+1)+(1-nu)*((T//216**(j-sigma))%216);sigma+=nu
        v=(flags[q]//2**(2*b))%2;d=2*((flags[q]//2**(2*b+1))%2)-1;decoded.append([q,b,v,d,u])
    need(decoded==actions and actions[0][2:]==[1,1,1],'every430 printed decoder transition and literalinitializer target1')
    right_targets=sorted({u for q,b,v,m,u in actions if m==1});left_targets=sorted({u for q,b,v,m,u in actions if m==-1});right={q:6+j for j,q in enumerate(right_targets)};left={q:205+j for j,q in enumerate(left_targets)}
    need((len(right),len(left))==(199,45),'entire target sets and color bounds')
    tiles=[tuple(t) for t in load(HERE/'TILES.json')];need(len(tiles)==len(set(tiles))==943 and all(len(t)==4 and all(type(v) is int for v in t) for t in tiles),'full943 distinct integer tuples')
    h=lambda q,b:2*(q+1)+b;expected={0:(2,435,3,1),1:(5,0,0,0)}
    for q,b,v,m,u in actions:expected[2+2*q+b]=((1-m)//2*left.get(u,0),h(q,b),(1+m)//2*right.get(u,0),v)
    for b in range(2):expected[432+b]=(0,h(215,b),0,h(215,b));expected[434+b]=(0,b,0,b)
    for q,r in right.items():
        for b in range(2):expected[424+2*r+b]=(r,b,0,h(q,b))
    for q,l in left.items():
        for b in range(2):expected[424+2*l+b]=(0,b,l,h(q,b))
    for j,t in enumerate([0,1,432,433]):expected[924+j]=(0,t,0,438)
    expected.update({928:(2,434,2,0),929:(3,436,4,4),930:(4,436,4,0)})
    for j,t in enumerate([434,435,436]):expected[931+j]=(1,438,1,t)
    for j,a in enumerate([0,1,4]):
        for b in range(3):expected[934+3*j+b]=(a,437,b,437)
    need(set(expected)==set(range(943)) and all(tiles[i]==expected[i] for i in range(943)),'ALL explicit index formulas versus independent contiguous group collector')
    need(all(all(0<=t[s]<(256,512,256,512)[s] for s in range(4)) for t in tiles),'every original edge label width')
    literal=[tuple(t) for t in load(ROOT/'con-zfc-diophantine-forms/36-small-tuple/coefficients/wang943_tiles.json')]
    need(sha256((json.dumps(literal,separators=(',',':'))+'\n').encode()).hexdigest()=='66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f','complete original943 literal language')
    oright={q:j+6 for j,q in enumerate(sorted({u for q,b,v,m,u in old if m==1}))};oleft={q:j+205 for j,q in enumerate(sorted({u for q,b,v,m,u in old if m==-1}))}
    hm={i:i for i in range(6)}|{oright[q]:right[pi[q]] for q in oright}|{oleft[q]:left[pi[q]] for q in oleft};vm={0:0,1:1,**{i:i for i in range(434,439)}}|{h(q,b):h(pi[q],b) for q in range(216) for b in range(2)}
    need(set(hm)==set(hm.values())==set(range(250)) and set(vm)==set(vm.values())==set(range(439)) and {(hm[w],vm[n],hm[e],vm[s]) for w,n,e,s in literal}==set(tiles),'all943 complete typed-color conjugacies and fixedstart/forbidden')
    sorted_BFS=tiles[:2]+sorted(tiles[2:]);permutation=[tiles.index(t) for t in sorted_BFS];need(permutation[:2]==[0,1] and set(permutation)==set(range(943)),'full selector permutation fixesStart0/Forbidden1')
    # Independent bit-position expansion, rather than the producer's densev formula.
    pos=[*range(8),34,*range(8,17),35,*range(17,25),36,*range(25,34),37,38,39,40];starts=[0,9,19,28];widths=[9,10,9,10];occupied=[256,512,256,512];offsets=[1023,1013,1003,983]
    c={}
    for i,t in enumerate(tiles):
        c[i]=1+2**51-sum(2**(10+pos[starts[s]+j]) for s,x in enumerate(t) for j in range(widths[s]) if (x+occupied[s])>>j&1)-sum(2**(10+pos[j]) for j in range(38,41))
        dense=t[0]+2**8*t[1]+2**17*t[2]+2**25*t[3]+127*2**34
        need(c[i]==1+2**51-2**10*dense and 1<=dense<2**41,'every full41-bit complement payload')
    for side in range(4):
        for j in range(widths[side]):c[offsets[side]+j]=2**(10+pos[starts[side]+j])
    for j,e in enumerate([1095,2195,3296]):c[e]=2**(48+j)
    c[1063]=c[1064]=0;support=set(c);need(len(support)==986 and min(c.values())>=0,'all986 support/copy/anchor/dummy positions')
    rho=2**67;B=2**590069;beta=B-1
    DC=sum(rho**e for e in [30,62,1100,2201])+sum(v*(rho**(4393-e)+rho**(5495-e)) for e,v in c.items());DR=rho**42
    MC=beta-sum(rho**e for e in support if e!=1)-2*rho**1063
    mf=4
    for e in [4393,5495]:mf|=(2**51-2)<<67*e
    for e in [*range(1013,1023),*range(1065,1074),2195,3296]:mf|=1<<67*e
    for e in range(8792,8805):mf|=(2**65-1)<<67*e
    mf|=(2**19-1)<<67*8805
    ports={'beta':beta,'K0':DC+B*DR,'MC':MC,'MF':mf+beta};physical={'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'};binding=load(HERE/'coefficients/BINDING.json');records=[]
    need(binding['path']=='coefficients/' and set(binding['ports'])==set(ports),'whole fixedport signature')
    for name,n in ports.items():
        filename=physical[name]+'.bin.gz';blob=(HERE/'coefficients'/filename).read_bytes();raw=gzip.decompress(blob);pin=binding['ports'][name]
        need(int.from_bytes(raw,'little')==n and len(raw)==(n.bit_length()+7)//8 and pin==dict(file=filename,bits=n.bit_length(),gzip_sha256=sha256(blob).hexdigest(),raw_sha256=sha256(raw).hexdigest()),'EVERY byte of whole regenerated coherent port '+name)
        oldraw=gzip.decompress((BASE/'coefficients'/filename).read_bytes());need((raw==oldraw)==(name!='K0'),'onlyK numericalchange, completeoldBFS bytescomparison')
        if name!='K0':need(blob==(BASE/'coefficients'/filename).read_bytes(),'unchanged compressed fixedport bytes')
        records.append(dict(port=name,bits=n.bit_length(),raw_bytes=len(raw),sha256=sha256(raw).hexdigest()))
    actualK=int.from_bytes(gzip.decompress((HERE/'coefficients/K.bin.gz').read_bytes()),'little');need(actualK%B==DC and actualK//B==DR and 0<DC<B,'actualmaterializedK nativequotient/remainder')
    digits={};rest=actualK%B;j=0
    while rest:
        digit=rest&(rho-1)
        if digit:digits[j]=digit
        rest>>=67;j+=1
    targets=[(1013+j,{983+j},set(),{1013+j}) for j in range(10)]+[(1065+j,{1003+j},{1023+j},set()) for j in range(9)]+[(2195,{1095},set(),{2195}),(3296,{1095},set(),{3296})];checks=0
    for t,a,b,cc in targets:
        for e in support:need(digits.get(t-e,0)==int(e in a) and int(e+42==t)==int(e in b) and int(e==t)==int(e in cc),'nativecopy identity from actualK digits');checks+=3
    for t in [4393,5495]:
        for e in support:need(digits.get(t-e,0)==c[e] and e+42!=t,'complete clause identity from actualKdigits');checks+=2
    need(checks==66062 and {(4393-e)%8807 for e in support}.isdisjoint({(5495-e)%8807 for e in support}) and {(2195-e)%8807 for e in support}&{(3296-e)%8807 for e in support}=={0},'allbasis and wholecell intersections')
    threshold=4*988*(2*sum(c.values())+6)+8;oldthreshold=load(OLD/'VERIFY.json')['native_finite_audit']['carry_threshold'];need(threshold==oldthreshold==118788496120850159560<rho,'exactoldBFS carryinvariance')
    need(MC.bit_count()==590069-986 and mf.bit_count()==986 and MC%4==2 and mf%8==4 and 0<MC<beta<ports['MF']<2*beta,'maskpopulation,congruence and sourceportbox')
    need(2*max(support)<8807 and max(digits)+max(support)==8791 and max(support)+42<8792 and 2*(2**51-2)+4<rho,'entirepadding geometry')
    orders=[];controller=[];lam=581197
    for p,order in [(67,66),(8807,4403),(lam,lam-1)]:
        need(factors(p)==[p] and pow(B,order,p)==1 and all(pow(B,order//r,p)!=1 for r in factors(order)),'complete prime/order certificates')
        H0=(1+B*DC+B*B*(DR+1))%p;need(gcd(H0,p)==gcd((B*B-1)%p,p)==1,'newwholecontrollerunits')
        orders.append(dict(prime=p,order=order));controller.append(dict(prime=p,H0=H0,B=B%p,B2minus1=(B*B-1)%p))
    need([r['H0'] for r in controller]==[23,3359,404489] and pow(B,lam-1,lam*lam)==182964883980!=1 and gcd(67*8807,lam)==1,'newH0 and unchangedlifting valuation')
    cert=load(HERE/'NATIVE_CERTIFICATE.json');certificate_ports=[dict(port=n,**binding['ports'][n],raw_bytes=(ports[n].bit_length()+7)//8,unchanged_raw=n!='K0') for n in ports]
    expected_certificate=dict(status='PASS',ports=certificate_ports,audit=dict(native_basis_checks=checks,carry_threshold=threshold,controller=controller,old_BFS_carry_threshold=oldthreshold,orders=[dict(**r,prime_divisors=factors(r['order'])) for r in orders],controller_lift=182964883980,selector_count=943,support_count=986,spatial_temporal_padding_preserved=True),all430_transition_conjugacies=True,all943_color_conjugacies=True,all943_explicit_indices=True,selector_old_to_new=permutation,state_old_to_BFS=[pi[q] for q in range(216)],literal_initializer=[3,436,4,4],old_BFS_K_raw_sha256=sha256(gzip.decompress((BASE/'coefficients/K.bin.gz').read_bytes())).hexdigest(),whole_fresh_native_tuple=True,old_native_words_reused=False)
    need(cert==expected_certificate,'ENTIRE independently reconstructed finite certificate and semantic boundaries')
    poly=load(HERE/'polynomial.json');parent=load(BASE/'polynomial.json');need(poly['coefficient_binding']==binding and poly['parent_sha256']==digest(BASE/'polynomial.json'),'actualwholepolynomialbinding provenance')
    for key in ['source','domain','witnesses','fixed_numerals','operations','operation_breakdown','register_degrees','exact_degree','syntactic_degree','output']:need(poly[key]==parent[key],'unchangedcompletefreeportkernel '+key)
    need(poly['operations']==98 and poly['exact_degree']==360 and poly['domain']=='strictly positive integers' and len(poly['witnesses'])==10,'currentarithmeticfrontier preserved')
    tex=(HERE/'equation.tex').read_text();oldtex=(BASE/'equation.tex').read_text();marker=r'\textbf{The four fixed integers.}';table=r'\textbf{The 943 indexed fixed tiles.}';decoder=r'\textbf{A closed decoder for the 430 actions.}'
    need(tex[:tex.index(marker)]==oldtex[:oldtex.index(marker)] and tex[tex.index(decoder):]==oldtex[oldtex.index(decoder):],'wholeprintedfront plusdecoder/alphabet/seed unchanged')
    need(tex[tex.index(marker):tex.index(table)]==oldtex[oldtex.index(marker):oldtex.index(r'\textbf{The 943 fixed tiles and their ranks.}')].replace(r'\sum_{t\in\mathcal T}v(t)x^{\varrho(t)}',r'\sum_{i=0}^{942}v(t_i)x^i'),'completePhi/mask/fixedcoefficientrecipe change is ONLYdirectindices')
    tab=tex[tex.index(table):tex.index(decoder)];required=[r'0,1&(2,435,3,1),\ (5,0,0,0)',r'j+2\ (j=2q+b<430)',r'432+b\ (b=0,1)',r'434+b\ (b=0,1)',r'424+2r_q+b\ (q\in\mathcal R,b=0,1)',r'424+2l_q+b\ (q\in\mathcal L,b=0,1)',r'924+j\ (0\le j<4)&(0,j+430\fl{j/2},0,438)',r'928&(2,434,2,0)',r'929&(3,436,4,4)',r'930&(4,436,4,0)',r'497+t\ (t=434,435,436)&(1,438,1,t)',r'934+3a+b-6\fl{a/4}',r'a\in\{0,1,4\},\ b=0,1,2',r'v(t)=w+2^8n+2^{17}e+2^{25}s+127\,2^{34}']
    need(all(x in tab for x in required) and all(x not in tex for x in [r'\kappa(t)',r'\varrho',r'\mathcal T\setminus']),'ALLliteralprintedindexgroups andeliminatedsorting floor')
    need(sha256(tab.encode()).hexdigest()=='e741734922c1a80ec69dc63abc71dce22487e3b839ed74c94daa6e856aa907b7','ENTIRE reviewed printed table, all definitions and every left/right body')
    # Reciprocal Phi is exactly integral, with every one of its986 coefficients.
    reciprocal=sum(v*rho**(3296-e) for e,v in c.items())*(rho**4393+rho**5495);need(reciprocal%rho**3296==0 and reciprocal//rho**3296+sum(rho**e for e in [30,62,1100,2201,8849])==ports['K0'],'entireprintedreciprocalKidentity')
    with tempfile.TemporaryDirectory(prefix='indexed-tiles-pdf-audit-') as directory:
        out=Path(directory)/'page.txt';subprocess.run(['pdftotext','-raw',str(HERE/'equation.pdf'),str(out)],check=True);text=out.read_text();need(text==(HERE/'equation.txt').read_text(),'actualentirePDFtextextraction')
        info=subprocess.check_output(['pdfinfo',str(HERE/'equation.pdf')],text=True);need(int(re.search(r'^Pages:\s+(\d+)',info,re.M)[1])==1,'actual PDF is one page')
    compact=lambda t:''.join(t.split());need(seed in compact(text) and ALPHABET in compact(text),'all436seed and62alphabet symbols actuallyprinted')
    oldtext=(BASE/'equation.txt').read_text();recipe=lambda t:t[t.index('The four fixed integers.'):t.index('The ordinary state/color')];nonwhite=lambda t:len(compact(t))
    need((nonwhite(recipe(oldtext)),nonwhite(recipe(text)),nonwhite(oldtext),nonwhite(text))==(2393,2343,3217,3167),'entirecompleteprintedrecipe andpagecounts')
    rejected=[]
    def reject(name,action):
        try:action()
        except (ValueError,KeyError,IndexError,TypeError):rejected.append(name)
        else:raise ValueError('corruptionaccepted '+name)
    wrong=list(tiles);wrong[0],wrong[1]=wrong[1],wrong[0]
    reject('swapStartForbiddenselectors',lambda:need(wrong==[expected[i] for i in range(943)],'mustfix0/1'))
    wrong=list(tiles);wrong[929]=(3,436,4,188)
    reject('retainunrenamedinitializer93',lambda:need(wrong==[expected[i] for i in range(943)],'literalinitializer4'))
    reject('reuseoldBFSK',lambda:need(gzip.decompress((BASE/'coefficients/K.bin.gz').read_bytes())==gzip.decompress((HERE/'coefficients/K.bin.gz').read_bytes()),'completeKactuallychanges'))
    reject('reuseoldcontrollerH0',lambda:need([x['H0'] for x in controller]==[46,4050,31053],'newDCrequiresfreshunits'))
    reject('assumeoldFCRpointwisemap',lambda:need(cert['old_native_words_reused'] is True,'freshnative/controllercompletion'))
    reject('shiftMFtwice',lambda:need(ports['MF']+beta==mf+beta,'exactlyonesourceshift'))
    reject('omitlastseedcharacters',lambda:need(seed[:-2]==seed,'all436required'))
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),all430_transition_conjugacies=True,all943_typed_color_conjugacies=True,all943_explicit_indices=True,selector_permutation_fixes=[0,1],native_basis_checks=checks,controller=controller,orders=orders,carry_threshold=threshold,old_BFS_carry_threshold=oldthreshold,ports=records,whole_fresh_native_tuple=True,old_native_words_reused=False,complete_printed_recipe_nonwhite=2343,baseline_recipe_nonwhite=2393,whole_page_nonwhite=3167,baseline_page_nonwhite=3217,net_printed_gain=50,full_standalone_pdf_sha256=digest(HERE/'equation.pdf'),operations=98,exact_degree=360,rejected_corruptions=rejected,source_pins={n:digest(HERE/n) for n in ['PROOF.md','SOURCE_PINS.json','build.py','render.py','check.py','polynomial.json','equation.tex','TILES.json']},builder_or_parent_checker_or_incoming_code_or_lean_executed=False,canonical_page_modified=False,scope='Complete finitepremises for whole new native/selector/controller proof; unbounded argument inPROOF.md. No old specialized polynomial or native-word equality.')
    output=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output.exists():need(args.output.read_text()==output,'refusechangedreceipt overwrite')
    else:args.output.write_text(output)
    print(output,end='')
if __name__=='__main__':main()
