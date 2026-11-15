#!/usr/bin/env python3
"""Check every packaged digest and independently extract both TeX tables."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent
EXPECTED={
 'LCSF3':('construction/candidate/machine.tm','2e5684567cd6e6e59fd99b5b093071533bcef6a01012dd2c6e41d52c645d2768'),
 'MP':('mp_construction/candidate/machine.tm','b634f75f4969a68513c5460a2e6bf8fd9bb0a72ab1f3dd03ec88b348ce2c6272')}
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    assert __debug__
    count=0
    for line in (ROOT/'SHA256SUMS').read_text().splitlines():
        h,name=line.split('  ',1);p=ROOT/name
        assert p.is_file() and digest(p)==h,name;count+=1
    tex=(ROOT/'pa194_research_report.tex').read_text();results={}
    for tag,(name,h) in EXPECTED.items():
        p=ROOT/name;assert digest(p)==h
        section=tex.split('% BEGIN_'+tag+'_TABLE\n',1)[1].split('% END_'+tag+'_TABLE',1)[0]
        rows={}
        for line in section.splitlines():
            if not re.match(r'^\d+\s*&',line):continue
            cells=line.rstrip().removesuffix('\\\\').strip().split('&');assert len(cells)==9
            for i in (0,3,6):
                if not cells[i].strip():continue
                q=int(cells[i].strip())
                for bit in (0,1):
                    m=re.fullmatch(r'\s*\\texttt\{([01])([LR])(\d+)\}\s*',cells[i+1+bit]);assert m
                    assert (q,bit)not in rows;rows[q,bit]=(int(m[1]),m[2],int(m[3]))
        assert set(rows)=={(q,b)for q in range(194)for b in(0,1)}
        literal=''.join(f'{q} {b} {w} {d} {n}\n'for(q,b),(w,d,n)in sorted(rows.items()))
        assert literal.encode()==p.read_bytes(),tag
        results[tag]={'working_states':194,'rows':388,'sha256':h,'TeX_table_equal':True}
    print(json.dumps({'status':'PASS','manifest_files':count,'machines':results},indent=2))
if __name__=='__main__':main()
