# PDF visual review

Rendered all 42 pages at 150 dpi with:

```sh
python /home/oai/skills/pdfs/scripts/render_pdf.py \
  paper/fiber_ipra_framework.pdf --out_dir <render-dir> --dpi 150
```

Inspected seven contact sheets covering every page and full-resolution samples
including the title, tables, theorem pages, code listings, appendices, and
references.

Result:

- no clipped text;
- no overlapping text or figures;
- no black boxes or broken glyphs;
- code listings fit within their frames;
- long tables continue correctly across pages;
- hyperlinks, table of contents, page headers, and page numbers render cleanly.

`pdf_preflight.py` reports 42 pages, openable, unencrypted, and not scanned.
All fonts reported by `pdf_inspect.py` are embedded.
