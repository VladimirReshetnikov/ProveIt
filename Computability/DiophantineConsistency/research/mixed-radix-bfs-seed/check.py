#!/usr/bin/env python3
"""Closed mixed-radix seed comparison; all output stays in this research sibling."""
import argparse
from hashlib import sha256
import gzip
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
BASE=ROOT/'candidates/one-page-short10'
ALPHABET='0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
def need(ok,message):
    if not ok:raise ValueError(message)
def sha(b):return sha256(b).hexdigest()
def b62(v):
    out=''
    while v:v,d=divmod(v,62);out=ALPHABET[d]+out
    return out or '0'
def integer(s):
    v=0
    for c in s:v=v*62+ALPHABET.index(c)
    return v
def flags(N,E,j):
    q,b=divmod(j,2);m=N>>(430+q)&1;tau=sum(N>>(430+k)&1 for k in range(q))
    F=14*(1-m)+m*(E//16**tau%16)
    return F>>2*b&1,2*(F>>(2*b+1)&1)-1

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--render',action='store_true');ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    pins=json.loads((HERE/'SOURCE_PINS.json').read_bytes())
    for name,h in pins['files'].items():need(sha((ROOT/name).read_bytes())==h,'whole frozen source pin '+name)
    if (HERE/'MANIFEST.json').exists():
        inventory=json.loads((HERE/'MANIFEST.json').read_bytes())['files']
        need({str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file() and p.name!='MANIFEST.json'}==set(inventory),'closed research inventory')
        for name,h in inventory.items():need(sha((HERE/name).read_bytes())==h,'sealed member '+name)
    literal=(BASE/'SEED.txt').read_text().strip();A=integer(literal)
    N=A%(1<<636);T=A//(1<<636)%(1<<1675);E=A>>(2311)
    nu=[N>>j&1 for j in range(430)];sig=[sum(nu[:j]) for j in range(431)]
    actions=[]
    for j in range(430):
        target=nu[j]*(1+sig[j])+(1-nu[j])*(T//216**(j-sig[j])%216)
        v,m=flags(N,E,j);actions.append([j//2,j%2,v,m,target])
    original=json.loads((ROOT/'con-zfc-diophantine-forms/36-small-tuple/coefficients/k215_transitions.json').read_bytes())['transitions']
    lookup={(q,b):(v,m,t) for q,b,v,m,t in original};order=[0];pi={0:0}
    for q in order:
        for b in [0,1]:
            t=lookup[q,b][2]
            if t<215 and t not in pi:pi[t]=len(order);order.append(t)
    pi[215]=215
    need(len(pi)==216 and actions==sorted([[pi[q],b,v,m,pi[t]] for q,b,v,m,t in original]),'all430 exact BFS transition conjugacies')
    halts=[j for j,a in enumerate(actions) if a[4]==215]
    need(halts==[125] and sig[125]==80,'unique halt before full discovery, not silently bounded by sigma')
    spec=importlib.util.spec_from_file_location('reviewed_closed_tuple44',ROOT/'tools/verify_one_page_tuple44.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    reference_ports,reference_tiles,native=mod.construct(actions)
    ports=[]
    for name,v in reference_ports.items():
        raw=v.to_bytes((v.bit_length()+7)//8,'little')
        need(raw==gzip.decompress((BASE/'coefficients'/(name+'.bin.gz')).read_bytes()),'every coherent compact44 coefficient byte')
        ports.append(dict(port=name,bits=v.bit_length(),bytes=len(raw),sha256=sha(raw)))
    source=(BASE/'equation.tex').read_text();begin=source.index(r'\textbf{A closed decoder for the 430 actions.}');end=source.index(r'\textbf{The integer $\mathcal A$.}',begin)
    intro=r'''\textbf{A closed decoder for the 430 actions.}
Put $D_b(A,k)=\fl{A/b^k}\bmod b$, where
$a\bmod b=a-b\fl{a/b}$. For $0\le q<215$, $b=0,1$, $j=2q+b$:
\[
\begin{gathered}
N=\mathcal A\bmod2^{636},\quad S=\fl{\mathcal A/2^{636}},\\
\nu_j=D_2(N,j),\quad \sigma_j=\sum_{k=0}^{j-1}\nu_k,\\
'''
    tail=r'''
m_q=D_2(N,430+q),\quad \tau_q=\sum_{k=0}^{q-1}m_k,\\
F_q=14(1-m_q)+m_qD_{16}(E_0,\tau_q),\\
TARGET
v_j=D_2(F_q,2b),\quad d_j=D_2(F_q,2b+1).
\end{gathered}
\]
Empty sums are zero and empty products are one. Here
$(v_0,d_0,u_0)=(1,1,1)$; the constructor tile
uses this actual first target, including its state renaming.

'''
    variants=[('generic-sigma2',False,False),('fixed-halt-sigma1',True,False),('omitted-halt-sigma1',True,True)]
    records=[]
    for name,fixed,omit in variants:
        radix=[1 if nu[j] or omit and j==125 else sig[j]+(1 if fixed else 2) for j in range(430)]
        powers=[1]
        for r in radix:powers.append(powers[-1]*r)
        digits=[0 if nu[j] or fixed and j==125 else actions[j][4] if actions[j][4]<215 else sig[j]+1 for j in range(430)]
        need(all(0<=d<r for d,r in zip(digits,radix)),'all mixed digits inside explicit finite radix bounds')
        packed=sum(d*p for d,p in zip(digits,powers));need(packed<powers[-1],'no target overflow into flag stream')
        newA=N+(1<<636)*(packed+powers[-1]*E);newlit=b62(newA)
        NN=newA%(1<<636);S=newA>>636;decodedE=S//powers[-1]
        need(NN==N and decodedE==E,'complete fields decode exactly')
        decoded=[]
        for j in range(430):
            small=S//powers[j]%(sig[j]+(1 if fixed else 2))
            old=small if fixed else small+(214-sig[j])*(small//(sig[j]+1))
            target=215 if fixed and j==125 else nu[j]*(1+sig[j])+(1-nu[j])*old
            v,m=flags(NN,decodedE,j);decoded.append([j//2,j%2,v,m,target])
        need(decoded==actions,'every430 full decoded actions identical, including halt125')
        pp,tt,nn=mod.construct(decoded)
        need(tt==reference_tiles and pp==reference_ports,'all943 tiles and complete coherent coefficient tuple identical')
        if fixed:
            product=r'P_j=\prod_{k=0}^{j-1}(\sigma_k+1)^{1-\nu_k}\quad(0\le j\le430),\\'
            if omit:product=r'P_j=\prod_{\substack{0\le k<j\\k\ne125}}(\sigma_k+1)^{1-\nu_k}\quad(0\le j\le430),\\'
            target=r'u_j=\nu_j(1+\sigma_j)+(1-\nu_j)(\fl{S/P_j}\bmod(\sigma_j+1))\ (j\ne125),\\'+'\n'+r'u_{125}=215,\\'
        else:
            product=r'P_j=\prod_{k=0}^{j-1}(\sigma_k+2)^{1-\nu_k}\quad(0\le j\le430),\\'
            target=r'a_j=\fl{S/P_j}\bmod(\sigma_j+2),\\'+'\n'+r'u_j=\nu_j(1+\sigma_j)+(1-\nu_j)\bigl(a_j+(214-\sigma_j)\fl{a_j/(\sigma_j+1)}\bigr),\\'
        decoder=(intro+product+'\n'+r'E_0=\fl{S/P_{430}},\\'+tail.replace('TARGET',target)).replace('S','\\mathcal S')
        tex=source[:begin]+decoder+source[end:]
        tex=tex.replace('436 characters',str(len(newlit))+' characters').replace('e_{435}','e_{'+str(len(newlit)-1)+'}').replace('j=0}^{435}','j=0}^{'+str(len(newlit)-1)+'}').replace('62^{435-j}','62^{'+str(len(newlit)-1)+'-j}')
        block=tex.index(r'\begingroup\fontsize{7.7}{8.2}\selectfont\ttfamily',tex.index(r'\textbf{The integer $\mathcal A$.}'));stop=tex.index(r'\endgroup',block)
        tex=tex[:block]+r'\begingroup\fontsize{7.7}{8.2}\selectfont\ttfamily'+'\n'+'\n'.join(newlit[i:i+62]+r'\par' for i in range(0,len(newlit),62))+'\n'+tex[stop:]
        out=HERE/name;out.mkdir(exist_ok=True)
        outputs={'SEED.txt':newlit+'\n','equation.tex':tex,'FIELDS.json':json.dumps(dict(seed_decimal=str(newA),seed_base62=newlit,mixed_target=str(packed),total_product=str(powers[-1]),target_bits=packed.bit_length(),product_bits=powers[-1].bit_length(),packed_bits=newA.bit_length(),halt_action=125,halt_sigma=80,radices=radix,digits=digits),indent=2,sort_keys=True)+'\n'}
        for file,text in outputs.items():
            p=out/file
            if p.exists() and (HERE/'MANIFEST.json').exists():need(p.read_text()==text,'deterministic existing artifact '+name+'/'+file)
            else:p.write_text(text)
        row=dict(name=name,seed_symbols=len(newlit),seed_bits=newA.bit_length(),target_bits=packed.bit_length(),product_bits=powers[-1].bit_length(),all430_actions_exact=True,all943_tiles_exact=True,whole_tuple_bytes_exact=True,tex_nonwhite=sum(not c.isspace() for c in tex),decoder_tex_nonwhite=sum(not c.isspace() for c in decoder))
        if args.render:
            p=subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error','-output-directory='+str(out),str(out/'equation.tex')],capture_output=True,text=True)
            need(p.returncode==0,'full standalone TeX render '+name)
            subprocess.run(['pdftotext','-raw',str(out/'equation.pdf'),str(out/'equation.txt')],check=True)
            text=(out/'equation.txt').read_text();base_text=(BASE/'equation.txt').read_text()
            metric=lambda x:sum(not c.isspace() for c in x[x.index('The four fixed integers.'):x.index('The ordinary state/color')])
            seedpart=text[text.index('The integer A.'):text.index('The ordinary state/color')]
            recovered=''.join(line.strip() for line in seedpart.splitlines() if re.fullmatch('[0-9A-Za-z]{10,}',line.strip()))
            need(recovered==newlit,'all printed seed symbols exact '+name)
            info=subprocess.check_output(['pdfinfo',str(out/'equation.pdf')],text=True)
            row.update(recipe_nonwhite=metric(text),baseline_recipe_nonwhite=metric(base_text),net_recipe_change=metric(text)-metric(base_text),page_nonwhite=sum(not c.isspace() for c in text),baseline_page_nonwhite=sum(not c.isspace() for c in base_text),overfull='Overfull' in p.stdout,pages=int(re.search(r'^Pages:\s+(\d+)',info,re.M)[1]),all_seed_pdf_symbols_exact=True)
        for suffix in ['.aux','.log']:
            scratch=out/('equation'+suffix)
            if scratch.exists():scratch.unlink()
        records.append(row)
    rejected=[]
    def reject(label,action):
        try:action()
        except ValueError:rejected.append(label)
        else:raise ValueError('corruption accepted '+label)
    reject('bound early halt215 by sigma80',lambda:need(215<sig[125]+1,'actual halt exceeds active-target radix'))
    reject('omit generic halt-symbol expansion',lambda:need(sig[125]+1==215,'generic halt requires expansion'))
    reject('retain old1675bit target field',lambda:need(S//(1<<1675)==E,'flags now follow actual mixed product'))
    reject('overflow mixed target into flags',lambda:need((packed+powers[-1]+powers[-1]*E)//powers[-1]==E,'strict target-product bound required'))
    reject('change one literal base62 symbol',lambda:need(integer(newlit[:-1]+ALPHABET[(ALPHABET.index(newlit[-1])+1)%62])==newA,'entire literal numeral checked'))
    wrong_tiles=set(reference_tiles);wrong_tiles.remove((3,436,4,4));wrong_tiles.add((3,436,4,188))
    reject('retain old unrenamed initializer93',lambda:need(wrong_tiles==set(reference_tiles),'full943 tile identity includes initialization'))
    if (HERE/'MANIFEST.json').exists():
        for name,h in inventory.items():need(sha((HERE/name).read_bytes())==h,'deterministic sealed replay '+name)
    result=dict(status='PASS',rejected_corruptions=rejected,optimized_python=bool(sys.flags.optimize),baseline_seed_symbols=len(literal),baseline_seed_bits=A.bit_length(),halt_actions=halts,halt_sigma=80,variants=records,ports=ports,native_finite_audit=native,source_builder_optimizer_archive_or_lean_executed=False,canonical_files_edited=False)
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output.exists():need(args.output.read_text()==text,'deterministic existing receipt')
    else:args.output.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
