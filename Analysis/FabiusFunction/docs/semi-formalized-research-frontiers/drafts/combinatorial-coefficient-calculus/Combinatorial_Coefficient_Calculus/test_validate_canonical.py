"""Focused regressions for duplicate formal-crosswalk diagnostics.

Run directly with ``python -B test_validate_canonical.py``. The fixtures stay
in memory and require neither a repository checkout nor a TeX installation.
"""

from pathlib import Path
import unittest

from validate_canonical import (
    Report,
    environment_blocks,
    strip_comments,
    validate_duplicate_crosswalks,
    validate_register_totals,
)


def remark(body: str, title: str = "Formal crosswalk") -> str:
    return f"\\begin{{remark}}[{title}]\n{body}\n\\end{{remark}}\n"


class DuplicateCrosswalkTests(unittest.TestCase):
    def diagnose(self, *remarks: str):
        path = Path("fixture.tex")
        clean = strip_comments("\\begin{document}\n" + "".join(remarks) + "\\end{document}\n")
        report = Report(Path.cwd())
        blocks = environment_blocks(path, clean, report)
        self.assertEqual(report.findings, [], "fixture must have balanced environments")
        validate_duplicate_crosswalks(path, clean, blocks, report)
        return report.findings

    def test_exact_duplicate_reports_both_locations(self):
        findings = self.diagnose(remark("Same body."), remark("Same body."))
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].code, "DUPLICATE_FORMAL_CROSSWALK")
        self.assertEqual(findings[0].level, "ERROR")
        self.assertEqual(findings[0].line, 5)
        self.assertIn("line 2", findings[0].message)

    def test_comments_and_whitespace_do_not_hide_duplicate(self):
        first = remark("% first revision\nKnown \\lean{Fabius.example} result.")
        second = remark("Known  \\lean{Fabius.example}\t% revised attribution\n result.")
        self.assertEqual(len(self.diagnose(first, second)), 1)

    def test_shared_declarations_with_distinct_claims_are_allowed(self):
        first = remark(r"\lean{Fabius.example} proves the forward formula.")
        second = remark(r"\lean{Fabius.example} also proves its specialization.")
        self.assertEqual(self.diagnose(first, second), [])

    def test_escaped_percent_is_part_of_the_body(self):
        first = remark(r"The error is at most 1\% on this domain.")
        second = remark(r"The error is at most 1\% on another domain.")
        self.assertEqual(self.diagnose(first, second), [])

    def test_other_remark_titles_are_not_crosswalks(self):
        first = remark("Same body.", "Historical context")
        self.assertEqual(self.diagnose(first, first, remark("Same body.")), [])

    def test_crosswalks_need_not_be_consecutive(self):
        first = remark("Repeated body.")
        middle = remark("An independent result.")
        self.assertEqual(len(self.diagnose(first, middle, first)), 1)

    def test_nested_environments_remain_part_of_the_body(self):
        first = remark("A list:\n\\begin{itemize}\n\\item One.\n\\end{itemize}")
        second = remark("A list:\n\\begin{itemize}\n\\item Two.\n\\end{itemize}")
        self.assertEqual(self.diagnose(first, second), [])
        self.assertEqual(len(self.diagnose(first, first)), 1)

    def test_each_repeat_points_to_first_occurrence(self):
        item = remark("Repeated body.")
        findings = self.diagnose(item, item, item)
        self.assertEqual([finding.line for finding in findings], [5, 8])
        self.assertTrue(all("line 2" in finding.message for finding in findings))


class RegisterTotalsTests(unittest.TestCase):
    def diagnose(self, summary: str, rows: str):
        report = Report(Path.cwd())
        source = (r"\section{Lean formalization register}" + "\n" + summary + "\n" + rows
                  + "\n" + r"\backmatter")
        validate_register_totals(Path("fixture.tex"), strip_comments(source), report)
        return report.findings

    def test_counts_labelled_and_unlabelled_rows(self):
        rows = (r"\Cref{a} & A & Lean & proof \\" + "\n"
                + r"lemma (unlabelled, no.~1) & B & none &  \\" + "\n"
                + r"\Cref{c} & C & partial & partial proof \\")
        self.assertEqual(self.diagnose(
            "Current totals: 1 Lean, 1 partial, 1 none, of 3 results.", rows), [])

    def test_stale_distribution_with_correct_total_is_rejected(self):
        rows = r"\Cref{a} & A & Lean & proof \\"
        findings = self.diagnose("Current totals: 0 Lean, 1 partial, 0 none, of 1 results.", rows)
        self.assertEqual([finding.code for finding in findings], ["LEAN_REGISTER_TOTALS"])

    def test_wrong_total_is_rejected(self):
        findings = self.diagnose("Current totals: 0 Lean, 0 partial, 0 none, of 1 results.", "")
        self.assertEqual([finding.code for finding in findings], ["LEAN_REGISTER_TOTALS"])

    def test_comments_do_not_count_as_rows(self):
        rows = "% " + r"\Cref{old} & Old & Lean & proof \\"
        self.assertEqual(self.diagnose(
            "Current totals: 0 Lean, 0 partial, 0 none, of 0 results.", rows), [])

    def test_missing_summary_is_rejected(self):
        findings = self.diagnose("No totals.", "")
        self.assertEqual([finding.code for finding in findings], ["LEAN_REGISTER_SUMMARY"])

    def test_missing_register_is_rejected(self):
        report = Report(Path.cwd())
        validate_register_totals(Path("fixture.tex"), "No register.", report)
        self.assertEqual([finding.code for finding in report.findings], ["LEAN_REGISTER_MISSING"])


if __name__ == "__main__":
    unittest.main()
