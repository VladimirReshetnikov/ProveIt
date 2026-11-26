"""Assemble the four self-contained papers in reading order with PDF bookmarks."""
from pathlib import Path

import fitz


ROOT = Path(__file__).resolve().parent
PARTS = [
    ("Research overview", "overview.pdf"),
    ("O’Hara’s finiteness questions", "cubic/ohara.pdf"),
    ("Uniform Rasmussen–Tamagawa bounds", "heavenly/heavenly.pdf"),
    ("Paired Euler products and the inverse spectral problem", "critical-line/critical-line.pdf"),
    ("Ratios of geometric progressions", "progressions/syndetic.pdf"),
]


def main():
    with fitz.open() as report:
        bookmarks = []
        labels = []
        for title, relative_path in PARTS:
            with fitz.open(ROOT / relative_path) as part:
                start = len(report)
                report.insert_pdf(part, links=False)
                # Each independent LaTeX paper reuses destination names such
                # as equation.1. Rebuild the resolved targets as page links.
                for index, page in enumerate(part):
                    destination = report[start + index]
                    for link in page.get_links():
                        if link["kind"] == fitz.LINK_URI:
                            destination.insert_link(dict(
                                kind=fitz.LINK_URI, uri=link["uri"],
                                **{"from": link["from"]},
                            ))
                        elif link.get("page", -1) >= 0:
                            destination.insert_link(dict(
                                kind=fitz.LINK_GOTO, page=start + link["page"],
                                to=link.get("to", fitz.Point(0, 0)),
                                **{"from": link["from"]},
                            ))
                bookmarks.append([1, title, start + 1])
                for level, section, page in part.get_toc():
                    if page > 0:
                        bookmarks.append([level + 1, section, start + page])
                prefix = Path(relative_path).stem + " "
                labels.append(dict(startpage=start, prefix=prefix, style="D", firstpagenum=1))
        report.set_toc(bookmarks)
        report.set_page_labels(labels)
        report.set_metadata(dict(
            title="Beyond Dirichlet GRH",
            subject="Heavenly elliptic curves, critical-line Euler products and geometric progressions",
            keywords="Dirichlet GRH, Rasmussen–Tamagawa, partial Euler products, Behrend sets",
        ))
        report.save(ROOT / "report.pdf", garbage=4, deflate=True)


if __name__ == "__main__":
    main()
