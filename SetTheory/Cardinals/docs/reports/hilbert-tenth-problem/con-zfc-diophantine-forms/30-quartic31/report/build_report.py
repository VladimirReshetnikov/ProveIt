if not __debug__: raise SystemExit('Optimized Python is not permitted: assertions are audit checks.')
"""Locally authored report assembler. Treats proof text as text; no received code runs."""
from pathlib import Path
import re,subprocess
H=Path(__file__).resolve().parent;R=H.parent

def normalize_appendix(text):
    text=re.sub(r'Packaging caveat:.*', 'Packaging note: the final release uses one shared compact-coefficient directory. All active positive, integer and nine-variable bindings resolve within the archive and their exact payload hashes are checked before replay.',text)
    text=re.sub(r'\b(degree|coefficient|on|of|has|at|by|all|in|with|for|over|from|into|and|than|package|Section|exactly|passed|operations|modulo|variable|rank)(?=[0-9])',r'\1 ',text)
    text=text.replace('polynomialdegree','polynomial degree').replace('ofdegree','of degree').replace('the compressor worker\nseparately audits','the nine-variable audit\nseparately verifies')
    # Preserve ASCII arithmetic: Pandoc's superscript/emphasis syntax is not math.
    lines=[]
    for line in text.splitlines():
        if line.startswith('    ') or line.startswith('#'):
            lines.append(line);continue
        line=re.sub(r'(?<![A-Za-z0-9`])([a-f0-9]{32,64})(?![A-Za-z0-9`])',r'`\1`',line)
        chunks=re.split(r'(`[^`]*`)',line)
        for j,c in enumerate(chunks):
            if c.startswith('`'):continue
            c=re.sub(r'(?<!\*)\*(?!\*)',r'\\*',c)
            if c.startswith('\\* '):c='* '+c[3:]
            c=re.sub(r'[^\s`]{24,}',lambda m:'`'+m.group(0).replace('\\*','*')+'`' if any(x in m.group(0) for x in ('*','^','=')) else m.group(0),c)
            chunks[j]=c
        line=''.join(chunks)
        # Standalone unformatted arithmetic paragraphs become wrapping literal blocks.
        if line and '=' in line and not line.startswith(('- ','* ')) and not re.search(r'\b(the|The|is|are|gives|gives|let|Let|where|Put|Then|then|with|with|so|If|if|and|for|For|Its|This|Thus|Use|Write|Take|Define|Set|Hence|Also|At|on|in)\b',line) and not line.startswith('`'):
            line='    '+line.replace('\\*','*')
        lines.append(line)
    return ('\n'.join(lines)+'\n').replace('| Construction | Integer unknowns | Degree | Binary gates | Multiplications | Add/subtract |','| Form | Vars | Degree | Ops | Mul | Add/sub |').replace('|---|---:|---:|---:|---:|---:|','|----------------------------------------|------:|------:|------:|------:|------:|')

parts=[(H/'MAIN.md').read_text()]
appendices=[
 ('A. Complete positive-variable proof','positive/POSITIVE12_PROOF.md'),
 ('B. Complete integer-family proof','integers/SIGNED_ODD_SCALE_FAMILY_PROOF.md'),
 ('C. Complete quartic reduction','arithmetic/QUARTIC31_PROOF.md'),
 ('D. Complete nine-variable construction','nine/COMPACT_NINE_PROOF.md'),
 ('E. Independent nine-variable audit','review/FINAL_NINE_REVIEW.md'),
 ('F. Independent Pell and signed-domain audit','audit/pell_independent_audit.md'),
 ('G. Retained-system tradeoff and rejected shortcuts','arithmetic/LOW_OPERATION_REPORT.md')]
for appendix_index,(title,path) in enumerate(appendices,13):
 text=(R/path).read_text();mapping={};counters=[0,0,0,0]
 for line in text.splitlines():
  m=re.match(r'^(#{2,5}) +(.*)',line)
  if not m:continue
  level=len(m.group(1))-2;counters[level]+=1
  for j in range(level+1,4):counters[j]=0
  number=re.match(r'([0-9]+(?:\.[0-9]+)*)\.? +',m.group(2))
  if number:mapping[number.group(1)]=str(appendix_index)+'.'+'.'.join(map(str,counters[:level+1]))
 text=re.sub(r'\b([Ss]ection) ?([0-9]+(?:\.[0-9]+)*)',lambda m:m.group(1)+' '+mapping.get(m.group(2),m.group(2)),text)
 text=normalize_appendix(text);text=re.sub(r'^# .+\n','',text,count=1)
 text=re.sub(r'^(#{2,5}) +[0-9]+(?:\.[0-9]+)*\.? +',r'\1 ',text,flags=re.M)
 parts+=['\n# Appendix '+title+'\n\n'+text]
content='\n'.join(parts)
# Normalize only typography; mathematical source files remain byte-for-byte separate.
content=content.replace('\u2011','-').replace('\u2014','; ').replace('\u2013','--')
(H/'synthesis_report.md').write_text(content)
cmd=['pandoc',str(H/'synthesis_report.md'),'--from=markdown-superscript-subscript','--standalone','--number-sections','--toc','--toc-depth=2',
     '--lua-filter='+str(H/'code_breaks.lua'),'--pdf-engine=xelatex','-V','documentclass:article','-V','fontsize:10pt','-V','geometry:margin=0.8in',
     '-V','mainfont:DejaVu Serif','-V','sansfont:DejaVu Sans','-V','monofont:DejaVu Sans Mono',
     '-V','colorlinks:true','-H',str(H/'header.tex'),'--syntax-highlighting=none','-o',str(H/'synthesis_report.tex')]
# Support the installed Pandoc version's older flag.
cmd[cmd.index('--syntax-highlighting=none')]='--no-highlight'
subprocess.run(cmd,check=True)
p=H/'synthesis_report.tex';tex=p.read_text()
# Comma-separated degree ledgers in prose need ordinary break opportunities.
tex=re.sub(r',(?=[A-Za-z])',', ',tex)
p.write_text(tex)
for _ in range(3):
 subprocess.run(['xelatex','-interaction=nonstopmode','-halt-on-error','synthesis_report.tex'],cwd=H,check=True,stdout=(H/'build_pdf.log').open('w'),stderr=subprocess.STDOUT)
print('Created synthesis_report.tex and synthesis_report.pdf')
