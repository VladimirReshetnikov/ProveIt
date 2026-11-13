# Independent audit of the 27-variable author-status refresh

[`audit.py`](audit.py) checked the revised status documentation and display in
tool session `37742`, with observed exit 0. Its [receipt](receipt.json) pins
the audited inputs and confirms that both the TeX and generator differ from
the version at commit `50ff01847d` only by the stated disclosure sentence.
The old PDF SHA-256 was `181e6b6dea3c1bd9433e3a5f93fa4b10894616463b94d23f0fe717d290bb04e2`;
the refreshed PDF SHA-256 is
`2f05619dba9240de671d8734dc6d96ef5161364ceca9ebf198dacd0f36cab4c6`.

The finite display validator checked 40 definitions, 18 residual squares and
129 circuit rows. The separate literal checker matched the AQ28/AQ27/AQ26
Lean gate lists to their pinned graphs, and their source hashes were bound to
the successful author's additions manifest. Two clean PDF builds matched the
refreshed PDF byte-for-byte without overfull, underfull or font warnings. The
second page's layout-extracted text and first page's pre-disclosure text agree
with the earlier PDF. The [first page](page-1.png) was visually inspected;
no clipping or overlapping text was apparent. The earlier full [independent
display audit](../equation8-27-independent-audit/README.md) remains historical
evidence for the previous PDF.

The changed wording accurately describes the independently audited
[single historical author run](../aq26-author-independent-audit/README.md) and
the still-pending paired replay. It does not establish a second Lean replay,
current-source or package/dynamic dependency authentication, or a Lean degree
theorem. The script uses assertions and refuses optimized Python; both `-O`
and `-OO` negative controls exited 1.
