"""Assemble the selected mathematical report from locally authored proof text."""
from pathlib import Path
import json,re,subprocess
H=Path(__file__).resolve().parent; R=H.parent

def readable(text, section):
    mapping={}
    for i,line in enumerate([x for x in text.splitlines() if x.startswith("## ")],1):
        m=re.match(r"## +([0-9]+)\. +",line)
        if m:mapping[m.group(1)]=str(section)+"."+str(i)
    text=re.sub(r"\b([Ss]ection) *([0-9]+)(?![0-9.])",lambda m:m.group(1)+" "+mapping.get(m.group(2),m.group(2)),text)
    text=re.sub(r'^# .+\n','',text,count=1)
    text=re.sub(r"The coefficient\s+worker's complete adapter", "The complete coefficient adapter", text)
    # Source prose sometimes omits spaces before numerals. Preserve equations.
    words='full|negative|are|lines|Therefore|all|and|at|by|degree|degrees|exactly|for|from|has|in|integer|integers|is|mod|modulo|of|on|operations|package|packages|proof|rank|Section|section|the|than|to|uses|variables|versus|with'
    text=re.sub(r'\b('+words+r')(?=[0-9])',r'\1 ',text)
    text=re.sub(r'(?<=[0-9])(and|bits|bytes|for|integers|mod|operations|or|raw|to|versus|with)\b',r' \1',text)
    text=text.replace('𝜌', 'ρ')
    text=text.replace('negativeR', 'negative R').replace('full58,905', 'full 58,905').replace('sums,6,144', 'sums, 6,144')
    text=text.replace('Choose wroot=2^((2R+1-k)/2). All subsequent constructions in', 'Choose\n\n    wroot=2^((2R+1-k)/2).\n\nAll subsequent constructions in')
    text=text.replace('rawbytes',' raw bytes').replace('bytes/gzip','bytes / gzip')
    text=text.replace('isneverzero','is never zero').replace('neverzero','never zero')
    text=text.replace('\u2011','-').replace('\u2014','; ').replace('\u2013','--')
    # Preserve complete multi-line ASCII equation paragraphs before Markdown parsing.
    blocks=[]
    for block in text.split('\n\n'):
        first=block.splitlines()[0] if block else ''
        if (re.match(r'^ ?[A-Za-z][A-Za-z0-9_]*(?:\([^)]*\))?\s*=',first) or first.startswith(' (epsilon,') or first.startswith(' d_r=') or first.startswith(' S=') or first.startswith(' b=')) and '$' not in block and not block.startswith('```'):
            block='```text\n'+block+'\n```'
        if block.startswith('|'):
            block=re.sub(r',(?=[0-9])',', ',block)
            block=re.sub(r'(?<=\|) *(b\+[^|]+) *(?=\|)',lambda m:' `'+m.group(1).strip()+'` ',block)
        blocks.append(block)
    text='\n\n'.join(blocks)
    lines=[]; in_fence=False; in_math=False
    for line in text.splitlines():
        if line.strip().startswith('```'):
            in_fence=not in_fence;lines.append(line);continue
        if line.strip()=='$$':
            in_math=not in_math;lines.append(line);continue
        if line.strip()=='\\[':
            in_math=True;lines.append(line);continue
        if line.strip() in ('\\]','$$') and in_math:
            in_math=False;lines.append(line);continue
        if in_math or in_fence or line.startswith('    '):
            lines.append(line);continue
        line=re.sub(r'^(#{2,5}) +[0-9]+(?:\.[0-9]+)*\.? +',r'\1 ',line)
        line=re.sub(r'(?<![A-Za-z0-9`])([a-f0-9]{32,64})(?![A-Za-z0-9`])',r'`\1`',line)
        chunks=re.split(r'(`[^`]*`)',line)
        for j,c in enumerate(chunks):
            if c.startswith('`'):continue
            c=re.sub(r'(?<=[A-Za-z]),(?=[0-9])', ', ', c)
            c=re.sub(r'(?<!\*)\*(?!\*)',r'\\*',c)
            if c.startswith('\\* '):c='* '+c[3:]
            c=re.sub(r'[^\s`]{16,}',lambda m:'`'+m.group(0).replace('\\*','*')+'`' if any(x in m.group(0) for x in ('*','^','=')) else m.group(0),c)
            chunks[j]=c
        line=''.join(chunks)
        # Preserve dense ASCII arithmetic as literal equations, not markdown.
        if line and '=' in line and not line.startswith(('- ','* ','#','|','`')) and not re.search(r'\b(the|The|is|are|gives|let|Let|where|Put|Then|then|with|so|If|if|and|for|For|Its|This|Thus|Use|Write|Take|Define|Set|Hence|Also|At|on|in|Suppose|When|Every|Each)\b',line):
            line='    '+line.replace('\\*','*')
        lines.append(line)
    return '\n'.join(lines)+'\n'

def main():
    config=json.loads((H/'REPORT_CONFIG.json').read_text())
    text=(H/'MAIN.md').read_text()
    for token,rel in config['proof_replacements'].items():
        section=len(re.findall(r'^# ',text.split(token)[0],re.M))
        text=text.replace(token,readable((R/rel).read_text(),section))
    for token,value in config['text_replacements'].items():text=text.replace(token,value)
    if re.search(r'\b[A-Z]+_SUMMARY\b|RESULTS_TABLE',text):raise RuntimeError('Unfilled report token')
    # ASCII equations are intentionally literal; TeX display blocks stay math.
    (H/'synthesis_report.md').write_text(text)
    cmd=['pandoc',str(H/'synthesis_report.md'),'--from=markdown+tex_math_single_backslash-superscript-subscript',
         '--standalone','--number-sections','--toc','--toc-depth=2',
         '--lua-filter='+str(H/'code_breaks.lua'),'--no-highlight',
         '-V','documentclass:article','-V','fontsize:10pt',
         '-V','geometry:margin=0.8in','-V','mainfont:DejaVu Serif',
         '-V','sansfont:DejaVu Sans','-V','monofont:DejaVu Sans Mono',
         '-V','colorlinks:true','-H',str(H/'header.tex'),'-o',str(H/'synthesis_report.tex')]
    subprocess.run(cmd,check=True)
    for _ in range(3):
        with (H/'build_pdf.log').open('w') as log:
            subprocess.run(['xelatex','-interaction=nonstopmode','-halt-on-error','synthesis_report.tex'],cwd=H,stdout=log,stderr=subprocess.STDOUT,check=True)
    print('Built synthesis_report.tex and synthesis_report.pdf')
if __name__=='__main__':main()
