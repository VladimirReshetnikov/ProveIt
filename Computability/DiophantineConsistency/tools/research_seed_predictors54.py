#!/usr/bin/env python3
"""Further closed seed/notation experiments; no Lean or archive mutation.

The frozen771-digit checkpoint is read only. New output goes exclusively to
candidates/one-page-compression/{merged-mask-decimal,merged-mask-base62,
original-base62-collected}. Bit/information changes and positional-notation
changes are recorded separately.
"""
from pathlib import Path
import argparse
from collections import Counter
import gzip
import importlib.util
import json
import re
import subprocess

ROOT=Path(__file__).resolve().parents[1]
ALPHABET="0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"


def need(ok,message):
    if not ok:raise ValueError(message)


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    value=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


seed54=module("frozen_seed54",ROOT/"tools/research_seed_compression54.py")
tuple54=module("frozen_tuple54",ROOT/"tools/verify_one_page_tuple54.py")


def radix_digits(value):
    chars=[]
    while value:
        value,d=divmod(value,62)
        chars.append(ALPHABET[d])
    return ''.join(reversed(chars)) or "0"


def from_digits(literal):
    need(len(ALPHABET)==62 and len(set(ALPHABET))==62,"complete distinct alphabet")
    need(all(ALPHABET.index(c)==i for i,c in enumerate(ALPHABET)),"every alphabet index")
    return sum(ALPHABET.index(c)*62**j for j,c in enumerate(reversed(literal)))


def merged_encode(c,actions):
    discovery,targets,mask,_=seed54.unpack(c)
    flags=[actions[2*q]//256+4*(actions[2*q+1]//256)for q in range(215)]
    literals=[f for f in flags if f!=14]
    exceptions=sum(f*16**k for k,f in enumerate(literals))
    low=discovery+2**430*mask
    need([low.bit_length(),targets.bit_length(),exceptions.bit_length()]==[636,1675,283],"exact field dimensions")
    return low+2**636*targets+2**2311*exceptions


def merged_decode(c):
    low=c%2**636
    targets=c//2**636%2**1675
    exceptions=c//2**2311
    nu=[seed54.digit(low,2,j)for j in range(430)]
    sigma=[sum(nu[:j])for j in range(430)]
    marks=[seed54.digit(low,2,430+q)for q in range(215)]
    tau=[sum(marks[:q])for q in range(215)]
    flags=[14*(1-marks[q])+marks[q]*seed54.digit(exceptions,16,tau[q])for q in range(215)]
    result=[]
    for j in range(430):
        target=nu[j]*(1+sigma[j])+(1-nu[j])*seed54.digit(targets,216,j-sigma[j])
        result.append(target+256*seed54.digit(flags[j//2],4,j%2))
    return result


DECODER=r'''For fixed indices $j=2q+r$, $0\le q<215$, $r\in\{0,1\}$, put
\[
\begin{gathered}
D_b(A,k)=\fl{A/b^k}\bmod b,\\
\mathcal N=\mathcal A\bmod2^{636},\quad
\mathcal T=\fl{\mathcal A/2^{636}}\bmod2^{1675},\\
\mathcal E=\fl{\mathcal A/2^{2311}},\\
\nu_j=D_2(\mathcal N,j),\quad \sigma_j=\sum_{k=0}^{j-1}\nu_k,\\
m_q=D_2(\mathcal N,430+q),\quad \tau_q=\sum_{k=0}^{q-1}m_k,\\
F_q=14(1-m_q)+m_qD_{16}(\mathcal E,\tau_q),\\
u_j=\nu_j(1+\sigma_j)+(1-\nu_j)D_{216}(\mathcal T,j-\sigma_j),\\
v_{2q+r}=D_2(F_q,2r),\quad d_{2q+r}=D_2(F_q,2r+1).
\end{gathered}
\]
Empty sums are zero; $a\bmod b=a-b\fl{a/b}$. Set
\[
t_{2+j}=\bigl((1-d_j)(512+u_j),\ 512+j,\ d_j(256+u_j),\ v_j\bigr).
\]
'''


def original_collected_tex():
    tex=(ROOT/"candidates/one-page/equation.tex").read_text()
    tex=tex.replace(r"\input{seed-display.tex}",(ROOT/"candidates/one-page/seed-display.tex").read_text())
    old=r"\Phi(x)={}&\sum_{i=0}^{456}c_i x^{r_i}\\"
    new=r'''\Phi(x)={}&O G_{457}(x)+\lambda\sum_{i=0}^{456}\ell_i x^{r_i}\\
 &-(255\,2^9+2^{27})x^{374}-(255\,2^{18}+2^{27})x^4\\'''
    need(old in tex,"original selector display")
    tex=tex.replace(old,new)
    tex=tex.replace(r"\textbf{The constants $r_i,c_i$.}",r"\textbf{The ranks $r_i$ and labels $\ell_i$.}")
    delta=r"\delta_{ij}&=\fl{\frac{Q-(i-j)^2}{Q}},\\"+"\n"
    need(delta in tex,"original delta display");tex=tex.replace(delta,"")
    coeff=r'''O&=1+255\,2^9+255\,2^{18}+2^{27}+\lambda,\\
c_i&=O+\lambda\ell_i-255\,2^9\delta_{i,455}-255\,2^{18}\delta_{i,456}\\
 &\qquad -2^{27}(\delta_{i,455}+\delta_{i,456}).'''
    need(coeff in tex,"original local coefficients")
    return tex.replace(coeff,r"O&=1+255\,2^9+255\,2^{18}+2^{27}+\lambda.")


def put_literal(tex,value,base62):
    literal=radix_digits(value)if base62 else str(value)
    need(from_digits(literal)==value if base62 else int(literal)==value,"complete positional round trip")
    start=tex.index(r'\fontsize{8}{9.1}\selectfont\ttfamily')+len(r'\fontsize{8}{9.1}\selectfont\ttfamily')
    stop=tex.index(r'\endgroup',start)
    tex=tex[:start]+'\n'+'\n'.join(literal[j:j+62]+r'\par'for j in range(0,len(literal),62))+'\n'+tex[stop:]
    if base62:
        old=r'\textbf{The integer $\mathcal A$.} Concatenate the following lines in order:'
        new=r'''\textbf{The integer $\mathcal A$.} Digit values are $0,\ldots,61$ in this alphabet:
{\fontsize{8}{9.1}\selectfont\ttfamily
'''+ALPHABET+r'''\par}
For the following '''+str(len(literal))+r''' characters, put
$\mathcal A=\sum_{j=0}^{'''+str(len(literal)-1)+r'''}\epsilon_j62^{'''+str(len(literal)-1)+r'''-j}$,
where $\epsilon_j$ is the value of character $j$ (starting at zero).
'''
        need(old in tex,"literal header");tex=tex.replace(old,new)
    return tex,literal


def render(tex,path,literal,base62):
    path.mkdir(parents=True,exist_ok=True)
    (path/'equation.tex').write_text(tex)
    result=subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error','-output-directory='+str(path),str(path/'equation.tex')],capture_output=True,text=True)
    need(result.returncode==0,"pdflatex successful")
    need('Overfull'not in result.stdout,"no overfull boxes")
    metrics=seed54.text_metrics(path/'equation.pdf',path/'equation.txt')
    need(metrics['pages']==1,"single Letter page")
    text=(path/'equation.txt').read_text()
    # The printed payload consists only of lines of the known alphanumeric
    # alphabet. Full alphabet header is removed explicitly before joining.
    lines=text.splitlines()
    found=[line.strip()for line in lines if line.strip()and all(c in ALPHABET for c in line.strip())and len(line.strip())>=2]
    if base62:
        need(ALPHABET in found,"every printed alphabet character")
        found=[line for line in found if line!=ALPHABET]
    # Require the exact expected wrapped lines as a contiguous subsequence;
    # explanatory prose and formula symbols may also be alphanumeric lines.
    expected=[literal[j:j+62]for j in range(0,len(literal),62)]
    need(any(found[k:k+len(expected)]==expected for k in range(len(found))),"every PDF payload character")
    metrics.update(no_overfull_boxes=True,all_printed_payload_characters_exact=True,
                   all_printed_alphabet_characters_exact=base62)
    return metrics


def predictor_probes(original,bfs,c):
    nu,_,_,_=seed54.unpack(c)
    old=[(j,bfs[j]%256,bfs[j]//256,j//2,j%2)for j in range(430)if not seed54.digit(nu,2,j)]
    rows={}
    for name,actions in [('original',original),('bfs',bfs)]:
        rows[name]={"q_minus_one_matches":sum(actions[j]%256==j//2-1 for j in range(430)),
                    "q_matches":sum(actions[j]%256==j//2 for j in range(430)),
                    "q_plus_one_matches":sum(actions[j]%256==j//2+1 for j in range(430)),
                    "best_fixed_target_matches":max(Counter(a%256 for a in actions).values())}
    for first in (0,1):
        order=[];rename={215:215}
        def visit(q):
            if q in rename:return
            rename[q]=len(order);order.append(q)
            for r in (first,1-first):visit(original[2*q+r]%256)
        visit(0)
        actions=[rename[original[2*q+r]%256]+256*(original[2*q+r]//256)for q in order for r in range(2)]
        rows['dfs_read'+str(first)+'_first']={"q_plus_one_matches":sum(actions[j]%256==j//2+1 for j in range(430)),"active_states":len(order)}
    rows['bfs_stored216']={"q_matches":sum(t==q for j,t,f,q,r in old),"q_minus_one_matches":sum(t==q-1 for j,t,f,q,r in old),"q_plus_one_matches":sum(t==q+1 for j,t,f,q,r in old),"best_flag_conditioned_constant_matches":sum(max(Counter(t for j,t,f,q,r in old if f==flag).values())for flag in range(4)),"mask_bits_for_another_predictor":216}
    def affine_by_group(entries,group):
        result=[]
        for label in sorted({group(e)for e in entries}):
            selected=[e for e in entries if group(e)==label]
            choices=[]
            for slope in (0,1):
                offset,count=Counter(e[1]-slope*e[3]for e in selected).most_common(1)[0]
                choices.append((count,slope,offset))
            count,slope,offset=max(choices)
            result.append(dict(group=label,slope=slope,offset=offset,matches=count))
        return dict(matches=sum(r['matches']for r in result),pieces=result)
    for name,actions in [('original',original),('bfs',bfs)]:
        entries=[(j,actions[j]%256,actions[j]//256,j//2,j%2)for j in range(430)]
        rows[name]['best_read_conditioned_affine']=affine_by_group(entries,lambda e:e[4])
    rows['bfs_stored216']['best_flag_conditioned_affine']=affine_by_group(old,lambda e:e[2])
    rows['bfs_stored216']['best_flag_read_conditioned_affine']=affine_by_group(old,lambda e:2*e[2]+e[4])
    return rows


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--render',action='store_true')
    args=parser.parse_args()
    original_file=ROOT/'candidates/one-page/COMPACT54_SEED.txt'
    old_seed=int(original_file.read_text())
    original=[seed54.digit(old_seed,1024,j)for j in range(430)]
    old_c,bfs,order,rename,_=seed54.encode_bfs(original)
    merged=merged_encode(old_c,bfs)
    need(merged_decode(merged)==bfs,"all430 merged actions equal frozen BFS")
    frozen=(ROOT/'candidates/one-page-compression/bfs-collected')
    need(old_c==int((frozen/'SEED.txt').read_text()),"frozen771 value unchanged")
    reference=json.loads((frozen/'VERIFY.json').read_text())
    bfs_ports,*_=tuple54.construct(seed54.row_seed(bfs))
    decoded_ports,*_=tuple54.construct(seed54.row_seed(merged_decode(merged)))
    original_ports,*_=tuple54.construct(old_seed)
    mode_conjugacy=seed54.check_mode_conjugacy(original,bfs,rename,tuple54)
    for name in bfs_ports:
        need(bfs_ports[name]==decoded_ports[name],"complete merged coefficient equality")
        raw=bfs_ports[name].to_bytes((bfs_ports[name].bit_length()+7)//8,'little')
        need(seed54.sha(raw)==next(p['sha256']for p in reference['ports']if p['port']==name),"frozen BFS whole tuple byte equality")
        path=ROOT/'candidates/split116-compact/compact54-sharp/coefficients/compact_tuple'/(name+'.bin.gz')
        oldraw=gzip.decompress(path.read_bytes())
        need(original_ports[name].to_bytes((original_ports[name].bit_length()+7)//8,'little')==oldraw,"original whole tuple byte equality")
    seed54.check_collected_phi(original,original_ports,tuple54)
    seed54.check_collected_phi(bfs,bfs_ports,tuple54)
    source=(frozen/'equation.tex').read_text()
    source=source[:source.index('For fixed indices')]+DECODER+source[source.index('The remaining quadruples'):]
    variants=[('merged-mask-decimal',source,merged,False,False),('merged-mask-base62',source,merged,True,False),('original-base62-collected',original_collected_tex(),old_seed,True,True)]
    records=[]
    for name,tex,value,base62,preserves in variants:
        path=ROOT/'candidates/one-page-compression'/name;path.mkdir(parents=True,exist_ok=True)
        tex,literal=put_literal(tex,value,base62)
        (path/'SEED.txt').write_text(literal+'\n')
        (path/'equation.tex').write_text(tex)
        ports=original_ports if preserves else bfs_ports
        data={"status":"PASS","base":62 if base62 else 10,"seed_decimal_digits":len(str(value)),"seed_characters":len(literal),"seed_bits":value.bit_length(),"alphabet":ALPHABET if base62 else "0123456789","all_alphabet_indices_checked":True,"positional_sum_equals_seed":True,"all430_actions_exact":True,"original_state_labels_preserved":preserves,"all_original_tuple_bytes_preserved":preserves,"all_frozen_BFS_tuple_bytes_preserved":not preserves,"source_seed_sha256":seed54.sha(original_file.read_bytes()),"ports":[{"port":k,"bits":v.bit_length(),"bytes":(v.bit_length()+7)//8,"sha256":seed54.sha(v.to_bytes((v.bit_length()+7)//8,'little'))}for k,v in ports.items()],"notation_only":base62 and preserves,"information_note":"Base62 changes notation, not information. Merged masks add33 bits to the frozen BFS seed while shortening its decoder."if not preserves else "The original seed integer and original tuple are unchanged; only numeral notation and the proved selector display change.","scope":"Exact finite seed/action/coefficient bytes and inherited ordinary state conjugacy. No Lean or object-ZFC calibration claimed."}
        data['mode_conjugacy']=mode_conjugacy
        data['initialization_corrected']=not preserves
        if args.render:data['render']=render(tex,path,literal,base62)
        (path/('VERIFY.optimized.json'if not __debug__ else'VERIFY.json')).write_text(json.dumps(data,indent=2)+'\n')
        records.append({k:v for k,v in data.items()if k not in ('ports','alphabet')})
    report={"status":"PASS","variants":records,"predictor_probes":predictor_probes(original,bfs,old_c)}
    out=ROOT/'candidates/one-page-compression/PREDICTOR_REVIEW.json';out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
