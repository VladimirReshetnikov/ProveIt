# Independent equation6-35 display audit

This final audit independently matches all 145 Lean, candidate and printed
gates, including 35 variable and four fixed-port input bindings. It invokes
the exact sparse-polynomial validator for 44 definitions and 22 squared
residuals, checks four mutations, and regenerates the candidate and full TeX
in a temporary directory. Two clean PDF builds match the supplied PDF byte
for byte, SHA `8d39b9411e005cb9e98d30ae55092d51d19da8218a28a93d947a5ee10b8cde99`.

Both pages were rendered and visually inspected: the content is complete,
with dense small text on page two. The retained TeX log has no overfull
warnings but reports small font size substitutions. Earlier failed and
metadata-defective drafts remain separately preserved. This audits the
presentation and finite gate computations; the native proof's historical
provider and inherited ancestry are separate qualifications.
