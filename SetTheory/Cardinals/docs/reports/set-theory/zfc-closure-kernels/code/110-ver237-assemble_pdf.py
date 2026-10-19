#!/usr/bin/env python3
"""Combine the reports, preserving resolved links and outlines (PyMuPDF)."""
from pathlib import Path
import argparse
import fitz

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();root=Path(__file__).resolve().parent
    inputs=[root/'report237.pdf',root/'composition238/report.pdf']
    writer=fitz.open();toc=[];offset=0;link_count=0
    titles=['Verified 237-state endpoint and independent transfer proof','Complete 238-state construction and formalism research']
    counts=[]
    for path,title in zip(inputs,titles):
        reader=fitz.open(path);counts.append(len(reader));toc.append([1,title,offset+1])
        writer.insert_pdf(reader,links=False,annots=True)
        for source_page in reader:
            for link in source_page.get_links():
                if link['kind']==fitz.LINK_GOTO:
                    dest={'kind':fitz.LINK_GOTO,'from':link['from'],'page':offset+link['page'],
                          'to':link.get('to',fitz.Point(0,0))}
                elif link['kind']==fitz.LINK_NAMED and 0 <= link.get('page',-1) < len(reader):
                    # Resolved named destinations expose PDF coordinates. Convert
                    # them to the target page's top-origin MuPDF coordinates.
                    target_page=reader[link['page']]
                    target_point=link['to'] * target_page.transformation_matrix
                    dest={'kind':fitz.LINK_GOTO,'from':link['from'],'page':offset+link['page'],
                          'to':target_point}
                elif link['kind']==fitz.LINK_URI:
                    dest={'kind':fitz.LINK_URI,'from':link['from'],'uri':link['uri']}
                else:raise ValueError('Unrecognized source link kind')
                writer[offset+source_page.number].insert_link(dest);link_count+=1
        for level,label,page in reader.get_toc():toc.append([level+1,label,offset+page])
        offset+=len(reader)
    if len(writer)!=sum(counts):raise ValueError('Incomplete combined PDF')
    writer.set_toc(toc)
    writer.set_metadata({'title':'Verified 237-state ZFC consistency construction and 238-state research companion',
        'author':'Research prepared for Vladimir Reshetnikov and ProveIt',
        'subject':'Exact binary machines, ordinary mathematical proofs, source calibration and logical-basis obstruction'})
    args.output.parent.mkdir(parents=True,exist_ok=True)
    writer.save(args.output,garbage=4,deflate=True)
    check=fitz.open(args.output)
    if sum(len(p.get_links()) for p in check)!=link_count:raise ValueError('Combined link count differs')
    print('Combined PDF pages:',counts,'=',sum(counts),'; preserved links:',link_count)

if __name__=='__main__':main()
