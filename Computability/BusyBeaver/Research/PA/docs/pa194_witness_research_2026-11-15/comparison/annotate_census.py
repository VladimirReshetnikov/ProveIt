#!/usr/bin/env python3
"""Attach attributed mechanism/evidence labels to the pinned census.

These labels summarize reports, not mathematical certifications. Exact table
class matching is mechanical; the mechanism/evidence descriptions are a manual
review of each newly encountered current principal or research artifact.
"""
from pathlib import Path
import collections,csv,json,re
HERE=Path(__file__).resolve().parent
CUR=HERE/'current'
NEW={
 '00a47ad79ce40':('PA194AX11GH = PA194AX11QGH','reported principal construction','Eleven-entry four-field AX, explicit generalization binder, Q head, no-push MP and cache-only Shift. Repeated in five current deliveries.','Written relative iPRA proof and absolute corollary importing revised AX11H calibration; no new full Lean build.'),
 '009b9846cc52':('PA194AX11GHS','reported principal construction','Same new AX11GH command semantics with reversed destructive comparison, removing three primitive source sites.','Written relative iPRA proof and inherited absolute corollary; no new full Lean build.'),
 '006b209abfd4':('PA194AX11GHF','reported principal construction','Two incoming-context physical shortcuts of AX11GH; each changed transition represents three parent transitions.','Written direct relative iPRA proof with time factor three; imports GH calibration.'),
 '02c76c1b81fd':('PA194AX11GHSF','reported principal construction','The same two physical shortcuts applied to AX11GHS.','Written direct relative iPRA proof with time factor three; imports GHS calibration.'),
 '009facf5ad81':('PA194LC','reported principal construction','Reassociates recurring constructor loops and their counted continuation; all 3673 primary source instructions preserved.','Written relative iPRA proof to original primary; its absolute primary calibration is not completed by this packet.'),
 '016cdb4815b5':('PA194LC_A','reported principal construction','First sibling loop-continuation implementation of the original primary source.','Written relative iPRA proof to original primary.'),
 '0057acbb37a3':('PA194LC_B','reported principal construction','Second sibling loop-continuation implementation of the original primary source.','Written relative iPRA proof to original primary.'),
 '00750aa2aa1b':('PA194LC_C','reported principal construction','Third sibling loop-continuation implementation of the original primary source.','Written relative iPRA proof to original primary.'),
 '00ec2a3bc207':('PA194LC_AX11H','reported principal construction','Three-row loop-continuation patch preserving all 3671 resolved AX11H source instructions.','Written relative iPRA polynomial-clock proof; absolute corollary imports revised AX11H written calibration.'),
 '0083cb92da6f':('PA194SEL','reported principal construction','Simultaneous reorganization of two recurring decoder pairs through history selectors; eight native transition rows change.','Written direct relative iPRA proof to original primary with factor-three clock; absolute primary calibration remains separate.'),
 '02582e3f9ce9':('PA194AX11HR','reported principal construction','Permutes nine physical register positions with ten active routing changes; exact AX11H startup falls to 48320 transitions.','Written source/physical iPRA proof and absolute corollary importing revised AX11H calibration.'),
 '00a2c8b94d4f':('Primary append-zero exploratory edit','research auxiliary','Changes primary native (74,0) from writing one to zero; used as a contraction-search input, without a consistency calibration.','No calibrated consistency claim.'),
}

def escape(s):
    return ''.join({'&':r'\&','%':r'\%','$':r'\$','#':r'\#','_':r'\_','{':r'\{','}':r'\}','~':r'\textasciitilde{}','^':r'\textasciicircum{}','\\':r'\textbackslash{}'}.get(c,c) for c in str(s))

def main():
    rows=json.loads((CUR/'classes194.json').read_text())
    for r in rows:
        for prefix,values in NEW.items():
            if r['table_class'].startswith(prefix):
                r.update(zip(('historical_name','historical_evidence','mechanism','calibration_status'),values));break
        if 'historical_name' not in r:
            path=r['representative']
            if '/scanner_composition/loop' in path:
                loop=re.search(r'/scanner_composition/(loop\d+)/',path)[1]
                r.update(historical_name='Rejected scanner/continuation '+loop,historical_evidence='rejected',mechanism='Source graph preserved, but shortened-scanner composition fails exactly 47 of 4780 symbolic source outcomes.',calibration_status='Rejected source implementation; not a consistency machine.')
            elif '/inputs/selectors/' in path:
                name=Path(path).name.replace('.native','').removesuffix('.tm')
                r.update(historical_name='Selector research '+name,historical_evidence='research auxiliary',mechanism='Single or composite history-selector input to finite stuttering/contraction searches; not a separately promoted principal machine.',calibration_status='Auxiliary research input; source packet does not promote it to a new absolute consistency theorem.')
            else:raise ValueError('Unannotated new class: '+path)
        r.setdefault('calibration_status','Attributed historical packet claim. Consult its proof and current formal status; table recognition is not an arithmetic proof.')
        r['claim_scope']='Mechanism and evidence labels summarize attributed source reports, not independent full arithmetic proof certificates.'
    rows.sort(key=lambda r:(not r['spanning'],r['historical_evidence'],r['historical_name']))
    (CUR/'comparison194_annotated.json').write_text(json.dumps(rows,indent=2)+'\n')
    keys=list(dict.fromkeys(k for r in rows for k in r))
    with (CUR/'comparison194_annotated.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=keys);w.writeheader();w.writerows(rows)
    counts=dict(collections.Counter(r['historical_evidence'] for r in rows if r['spanning']))
    (CUR/'evidence_categories.json').write_text(json.dumps({'scope':'Attributed historical claims; categories are not verified arithmetic theorems.','spanning194':counts,'nonspanning194_literal_identities':sum(not r['spanning'] for r in rows)},indent=2)+'\n')
    tex=[r'\begin{longtable}{@{}p{.25\textwidth}p{.17\textwidth}p{.51\textwidth}@{}}',r'\toprule',r'Design / class prefix & Attributed status & Mechanism \\',r'\midrule\endhead']
    for r in rows:
        if not r['spanning']:continue
        tex.append(escape(r['historical_name'])+r'\newline{\ttfamily\footnotesize '+r['table_class'][:12]+'} & '+escape(r['historical_evidence'])+' & '+escape(r['mechanism'])+r'\\[3pt]')
    tex += [r'\bottomrule',r'\end{longtable}']
    (CUR/'frontier194_table.tex').write_text('\n'.join(tex)+'\n')
    packets=json.loads((HERE/'packet_ledger93.json').read_text())
    keys=list(dict.fromkeys(k for r in packets for k in r))
    with (HERE/'packet_ledger93.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=keys);w.writeheader();w.writerows(packets)
    print(json.dumps(counts,indent=2))
if __name__=='__main__':main()
