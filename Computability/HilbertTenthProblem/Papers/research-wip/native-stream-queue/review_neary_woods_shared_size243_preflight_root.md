# Retained literal-guard correction in the independent243 review

**Review remark 1.** The independent review initially expected the literal
lower-transport row `6 * hist__linear_group__169`. In both complete244
and complete243 arrays the actual unchanged record is

    [hist__linear_coefficient__170, *, hist__linear_group__169, 6].

The expected operand order was therefore a false claim about the saved
record. The reviewer corrected its fresh metadata guard before its audit
passed and retained the event in the frozen review. Root additionally
records it here as a numbered remark, as required for review-stage errors.
Root independently inspected all four literal records as inert data.

This correction changes neither source, ring identity nor operation count:
commutative multiplication gives the same polynomial, but literal-record
identity requires the actual operand order. The final independent review
and original author bytes remain unchanged. No author mathematical claim
was corrected. No saved array or scientific helper was evaluated.
