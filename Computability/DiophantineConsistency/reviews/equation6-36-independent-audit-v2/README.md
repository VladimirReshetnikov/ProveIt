# Independent equation6-36 display audit

The final audit independently matches all 148 Lean, candidate and printed
gates, including the 36-variable and four-port input bindings. It invokes the
separate exact sparse-polynomial validator for 44 displayed definitions and
23 squared residuals, then checks four mutations including a printed-gate
operand mutation. It regenerates the candidate and full TeX in a temporary
directory and obtains two clean PDF builds byte-identical to the supplied PDF,
SHA `b63eb57ed20008e1b6667703e8ce557c8494a78b98596b1cd9490e87d676fc4e`.

Both pages were rendered and visually inspected: the displayed content is
complete, with dense small text on page two. The retained TeX log has no
overfull warnings but reports small font size substitutions. This audits the
presentation and finite gate computations; the native theorem's historical
provider and inherited ancestry limitations are documented separately. The
preliminary packet is preserved separately.
