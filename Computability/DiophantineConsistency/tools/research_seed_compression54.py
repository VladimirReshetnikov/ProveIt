#!/usr/bin/env python3
"""Finite compression experiments for the complete compact54 page.

The printed decoder is closed arithmetic. BFS and the original seed are
used only to derive/certify its literal numeral, not to decode that numeral.
This script changes no original candidate, delivered archive, or Lean file.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import importlib.util
import json
import re
import subprocess
import time

RESEARCH = Path(__file__).resolve().parents[1]


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def digit(value, radix, index):
    return value // radix**index % radix


def unpack(c):
    return (c % 2**426, c // 2**426 % 2**1675,
            c // 2**2101 % 2**206, c // 2**2307)


def decode(c):
    """Exactly the fixed-sum/quotient formulas printed in the new TeX."""
    discovery, targets, mask, exceptions = unpack(c)
    nu = [digit(discovery, 2, j) for j in range(430)]
    sigma = [sum(nu[k] for k in range(j)) for j in range(430)]
    marks = [digit(mask, 2, q) for q in range(215)]
    tau = [sum(marks[k] for k in range(q)) for q in range(215)]
    rowflags = []
    for q in range(215):
        e = digit(exceptions, 12, tau[q])
        exceptional = e + e//9 + e//10 + 2*(e//11)
        rowflags.append(14*(1-marks[q]) + marks[q]*exceptional)
    actions = []
    for j in range(430):
        t = nu[j]*(1+sigma[j]) + (1-nu[j])*digit(targets, 216, j-sigma[j])
        flags = digit(rowflags[j//2], 4, j % 2)
        actions.append(t + 256*flags)
    return actions


def flags_encode(actions):
    rows = [actions[2*q]//256 + 4*(actions[2*q+1]//256) for q in range(215)]
    alphabet = [0,1,2,3,4,5,6,7,8,10,12,15]
    mask = sum((flags != 14)*2**q for q, flags in enumerate(rows))
    exceptional = [flags for flags in rows if flags != 14]
    require(all(flags in alphabet for flags in exceptional), "row flag alphabet")
    require(all(e+e//9+e//10+2*(e//11) == flags for e, flags in enumerate(alphabet)),
            "closed exception alphabet decoder")
    seed = sum(alphabet.index(flags)*12**k for k, flags in enumerate(exceptional))
    return mask, seed, len(exceptional)


def encode_bfs(original):
    order = [0]
    rename = {0: 0}
    for q in order:
        for action in original[2*q:2*q+2]:
            t = action % 256
            if t < 215 and t not in rename:
                rename[t] = len(order)
                order.append(t)
    require(len(order) == 215 and set(order) == set(range(215)), "all active states reachable")
    rename[215] = 215
    actions = [rename[action % 256] + 256*(action//256)
               for q in order for action in original[2*q:2*q+2]]
    # Finite one-step bisimulation, retaining start0 and the sole halt215.
    require(rename[0] == 0 and rename[215] == 215, "start/halt fixed")
    for q in range(215):
        for read in range(2):
            old = original[2*q+read]
            new = actions[2*rename[q]+read]
            require(new % 256 == rename[old % 256] and new//256 == old//256,
                    "state renaming conjugacy")
    seen = {0}
    discovery = 0
    oldtargets = []
    mixed_targets = 0
    mixed_scale = 1
    for j, action in enumerate(actions):
        target = action % 256
        s = len(seen)-1
        if target < 215 and target not in seen:
            require(target == s+1, "canonical first-discovery numbering")
            seen.add(target)
            discovery += 2**j
        else:
            oldtargets.append(target)
            symbol = target if target < 215 else s+1
            mixed_targets += symbol*mixed_scale
            mixed_scale *= s+2
    require(len(seen) == 215 and len(oldtargets) == 216, "214 discoveries/216 stored targets")
    targets = sum(t*216**k for k, t in enumerate(oldtargets))
    mask, exceptions, exception_count = flags_encode(actions)
    fields = discovery, targets, mask, exceptions
    require([value.bit_length() for value in fields] == [426,1675,206,254], "exact field widths")
    c = discovery + 2**426*targets + 2**2101*mask + 2**2307*exceptions
    require(unpack(c) == fields and decode(c) == actions, "closed decoder exact equality")
    return c, actions, order, rename, {
        "fields_bits": [value.bit_length() for value in fields],
        "fields_decimal_digits": [len(str(value)) for value in fields],
        "discovery_count": 214, "stored_target_count": 216,
        "default_flag_rows": 215-exception_count, "exception_flag_rows": exception_count,
        "mixed_product_variant_target_digits": len(str(mixed_targets)),
        "mixed_product_variant_total_separate_digits":
            len(str(discovery))+len(str(mixed_targets))+len(str(mask))+len(str(exceptions)),
    }


def row_seed(actions):
    return sum(action*1024**j for j, action in enumerate(actions))


def make_tex(c, output, collected):
    tex = (RESEARCH / "candidates/one-page/equation.tex").read_text()
    start = tex.index("From the integer $\\mathcal A$ printed below")
    end = tex.index("The remaining quadruples are", start)
    decoder = r"""For fixed indices $j=2q+r$, $0\le q<215$, $r\in\{0,1\}$, put
\[
\begin{gathered}
D_b(A,k)=\fl{A/b^k}\bmod b,\\
\mathcal N=\mathcal A\bmod2^{426},\quad
\mathcal T=\fl{\mathcal A/2^{426}}\bmod2^{1675},\\
\mathcal M=\fl{\mathcal A/2^{2101}}\bmod2^{206},\quad
\mathcal E=\fl{\mathcal A/2^{2307}},\\
\nu_j=D_2(\mathcal N,j),\quad \sigma_j=\sum_{k=0}^{j-1}\nu_k,\\
m_q=D_2(\mathcal M,q),\quad \tau_q=\sum_{k=0}^{q-1}m_k,\\
e_q=D_{12}(\mathcal E,\tau_q),\\
F_q=14(1-m_q)+m_q\bigl(e_q+\fl{e_q/9}+\fl{e_q/10}+2\fl{e_q/11}\bigr),\\
u_j=\nu_j(1+\sigma_j)+(1-\nu_j)D_{216}(\mathcal T,j-\sigma_j),\\
v_{2q+r}=D_2(F_q,2r),\quad d_{2q+r}=D_2(F_q,2r+1).
\end{gathered}
\]
Empty sums are zero; $a\bmod b=a-b\fl{a/b}$. Set
\[
t_{2+j}=\bigl((1-d_j)(512+u_j),\ 512+j,\ d_j(256+u_j),\ v_j\bigr).
\]
"""
    tex = tex[:start] + decoder + tex[end:]
    lines = [str(c)[i:i+62] for i in range(0,len(str(c)),62)]
    seed_display = "\n".join(line + r"\par" for line in lines)
    tex = tex.replace(r"\input{seed-display.tex}", seed_display)
    tex = tex.replace("{\\large\\bfseries A completely specified Diophantine consistency equation}",
                      "{\\large\\bfseries A shorter complete consistency equation}")
    old_note = """Absence of positive integer solutions is equivalent to $\\mathrm{Con}(\\mathrm{ZFC})$
by the inherited native/Pell argument and the checked P69--P67 reduction.
The full native calibration and its internal ZFC formalization remain open
Lean obligations. This page specifies the equation, not its proof."""
    new_note = """The state-renamed native/P69 argument gives unsolvability iff
$\\mathrm{Con}(\\mathrm{ZFC})$. Native calibration and its internal ZFC proof
remain open in Lean. This page specifies the equation."""
    require(old_note in tex,"original boundary note")
    tex = tex.replace(old_note,new_note)
    if collected:
        old_phi = r"\Phi(x)={}&\sum_{i=0}^{456}c_i x^{r_i}\\"
        new_phi = r"""\Phi(x)={}&O G_{457}(x)+\lambda\sum_{i=0}^{456}\ell_i x^{r_i}\\
 &-(255\,2^9+2^{27})x^{374}-(255\,2^{18}+2^{27})x^4\\"""
        require(old_phi in tex,"original selector polynomial")
        tex = tex.replace(old_phi,new_phi)
        tex = tex.replace(r"\textbf{The constants $r_i,c_i$.}",
                          r"\textbf{The ranks $r_i$ and labels $\ell_i$.}")
        delta = r"\delta_{ij}&=\fl{\frac{Q-(i-j)^2}{Q}},\\"+"\n"
        require(delta in tex,"original delta definition")
        tex = tex.replace(delta,"")
        old_coefficient = r"""O&=1+255\,2^9+255\,2^{18}+2^{27}+\lambda,\\
c_i&=O+\lambda\ell_i-255\,2^9\delta_{i,455}-255\,2^{18}\delta_{i,456}\\
 &\qquad -2^{27}(\delta_{i,455}+\delta_{i,456})."""
        require(old_coefficient in tex,"original coefficient definition")
        tex = tex.replace(old_coefficient,r"O&=1+255\,2^9+255\,2^{18}+2^{27}+\lambda.")
    output.write_text(tex)
    return tex, decoder


def text_metrics(pdf, txt):
    subprocess.run(["pdftotext","-raw",str(pdf),str(txt)], check=True)
    text = txt.read_text()
    info = subprocess.run(["pdfinfo",str(pdf)], check=True, capture_output=True, text=True).stdout
    pages = int(re.search(r"^Pages:\s+(\d+)",info,re.M)[1])
    start = text.index("Fixed coefficients.")
    stop = text.index("The state-renamed") if "The state-renamed" in text else text.index("Absence")
    recipe = text[start:stop]
    return {"pages": pages,"extracted_text_characters": len(text),
            "extracted_nonwhitespace_characters": sum(not ch.isspace() for ch in text),
            "extracted_numeric_digits": sum(ch.isdigit() for ch in text),
            "coefficient_recipe_characters":len(recipe),
            "coefficient_recipe_nonwhitespace_characters":sum(not ch.isspace() for ch in recipe),
            "coefficient_recipe_numeric_digits":sum(ch.isdigit() for ch in recipe)}


def check_collected_phi(actions, ports, module):
    _, _, modes, ranks = module.construct(row_seed(actions))
    require(ranks[455] == 374 and ranks[456] == 4,"fixed receiver ranks")
    h = 2**29
    ordinary = 1+255*2**9+255*2**18+2**27+h
    collected = {rank:ordinary for rank in range(457)}
    for rank,(w,n,e,s) in zip(ranks,modes):
        collected[rank] += h*(2*w+2**11*n+2**22*e+2**32*s)
    collected[374] -= 255*2**9+2**27
    collected[4] -= 255*2**18+2**27
    native = {}
    for i,((w,n,e,s),rank) in enumerate(zip(modes,ranks)):
        right,left = int(i == 455),int(i == 456)
        native[rank] = (1+255*2**9*(1-right)+255*2**18*(1-left)+
            2**27*(1-right-left)+h*(1+2*w+2**11*n+2**22*e+2**32*s))
    require(collected == native,"all457 collected selector coefficients")
    rho = 2**89
    selector_original = sum(c*(rho**(2409-rank)+rho**(3015-rank)) for rank,c in native.items())
    selector_collected = sum(c*(rho**(2409-rank)+rho**(3015-rank)) for rank,c in collected.items())
    require(selector_original == selector_collected,"exact collected selector evaluation")
    # Keep the unchanged auxiliary/bare part from the independently checked
    # native construction, and compare the entire resulting K as bytes.
    k = ports["K"]-selector_original+selector_collected
    require(k.to_bytes((k.bit_length()+7)//8,"little") ==
        ports["K"].to_bytes((ports["K"].bit_length()+7)//8,"little"),"collected full K bytes")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir",type=Path,default=RESEARCH/"candidates/one-page-compression/bfs-fixed216")
    parser.add_argument("--render",action="store_true")
    parser.add_argument("--collected-phi",action="store_true")
    args = parser.parse_args()
    begin = time.monotonic()
    out = args.output_dir
    out.mkdir(parents=True,exist_ok=True)
    source = RESEARCH/"candidates/one-page/COMPACT54_SEED.txt"
    original_seed = int(source.read_text())
    original = [digit(original_seed,1024,j) for j in range(430)]
    c, actions, order, rename, measurements = encode_bfs(original)
    spec = importlib.util.spec_from_file_location("frozen_page54",RESEARCH/"tools/verify_one_page_tuple54.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    direct_ports, _, _, _ = module.construct(row_seed(actions))
    decoded_ports, _, _, _ = module.construct(row_seed(decode(c)))
    old_ports, _, _, _ = module.construct(original_seed)
    check_collected_phi(actions,direct_ports,module)
    check_collected_phi(original,old_ports,module)
    port_records = []
    for name in direct_ports:
        raw = direct_ports[name].to_bytes((direct_ports[name].bit_length()+7)//8,"little")
        decoded = decoded_ports[name].to_bytes((decoded_ports[name].bit_length()+7)//8,"little")
        reference = RESEARCH/"candidates/split116-compact/compact54-sharp/coefficients/compact_tuple"/(name+".bin.gz")
        old_raw = gzip.decompress(reference.read_bytes())
        require(old_ports[name].to_bytes((old_ports[name].bit_length()+7)//8,"little") == old_raw,
                "unchanged source reference identity")
        require(raw == decoded,"whole port byte equality")
        require((raw == old_raw) == (name != "K"),"only K changes under state renaming")
        port_records.append({"port":name,"bits":direct_ports[name].bit_length(),
            "bytes":len(raw),"sha256":sha(raw),"decoded_equals_direct_all_bytes":True,
            "equals_original_tuple":raw == old_raw})
    require(len(str(c)) == 771,"compressed numeral length")
    (out/"SEED.txt").write_text(str(c)+"\n")
    (out/"SEEDS.json").write_text(json.dumps({"C":str(c),"fields":
        dict(zip(["discovery","targets","flag_mask","flag_exceptions"],map(str,unpack(c))))},indent=2)+"\n")
    (out/"STATE_RENAMING.json").write_text(json.dumps({"new_to_old":order+[215],
        "old_to_new":[rename[q] for q in range(216)],"all430_transition_conjugacies":True},indent=2)+"\n")
    tex, decoder = make_tex(c,out/"equation.tex",args.collected_phi)
    same_mask, same_exception, _ = flags_encode(original)
    same_targets = sum((v%256)*216**j for j,v in enumerate(original))
    receipt = {"status":"PASS","original_payload_digits":1294,
        "compressed_payload_digits":len(str(c)),"compressed_payload_bits":c.bit_length(),
        "payload_digit_reduction":1294-len(str(c)),"seed_ascii_sha256":sha((str(c)+"\n").encode()),
        "source_seed_ascii_sha256":sha(source.read_bytes()),
        "decoder_uses_only":"fixed finite sums, integer quotient/remainder, powers, addition and multiplication",
        "all430_decoded_actions_equal_renamed_actions":True,
        "state_permutation_bijective":True,"start0_and_halt215_fixed":True,
        "all430_transition_conjugacies":True,"measurements":measurements,"ports":port_records,
        "collected_selector_all457_coefficients_equal":True,
        "collected_selector_full_K_bytes_equal":True,
        "collected_phi_display":args.collected_phi,
        "same_label_variant_separate_payload_digits":sum(len(str(v)) for v in
            [same_targets,same_mask,same_exception]),
        "decoder_tex_characters":len(decoder),
        "complete_tex_characters":len(tex),"complete_tex_utf8_bytes":len(tex.encode()),
        "scope":"Finite numeral and transition-conjugacy checks. No Lean proof or native/object-ZFC calibration claimed."}
    if args.render:
        latex = subprocess.run(["pdflatex","-interaction=nonstopmode","-halt-on-error",
            "-output-directory="+str(out),str(out/"equation.tex")],capture_output=True,text=True)
        (out/"RENDER.log").write_text(latex.stdout+latex.stderr)
        require(latex.returncode == 0,"pdflatex compilation")
        receipt["render"] = text_metrics(out/"equation.pdf",out/"equation.txt")
        receipt["render"]["overfull_boxes"] = "Overfull" in latex.stdout
        receipt["original_render"] = text_metrics(RESEARCH/"candidates/one-page/equation.pdf",out/"original-equation.txt")
        printed = (out/"equation.txt").read_text()
        seed_block = printed[printed.index("The integer A."):printed.index("The state-renamed")]
        extracted = "".join(line.strip() for line in seed_block.splitlines() if line.strip().isdigit())
        require(extracted == str(c),"all771 seed digits survive PDF text extraction exactly")
        require(r"\input{" not in tex and r"\include{" not in tex,"standalone TeX has all data inline")
        receipt["all_seed_digits_in_pdf_equal"] = True
        receipt["standalone_tex_data_inline"] = True
        receipt["tex_sha256"] = sha((out/"equation.tex").read_bytes())
        receipt["pdf_sha256"] = sha((out/"equation.pdf").read_bytes())
    receipt["seconds"] = round(time.monotonic()-begin,3)
    (out/"VERIFY.json").write_text(json.dumps(receipt,indent=2)+"\n")
    print(json.dumps(receipt,indent=2))


if __name__ == "__main__":
    main()
