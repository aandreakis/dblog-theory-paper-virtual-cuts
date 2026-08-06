# Paper sources

LaTeX sources of **“A Theoretical Study of DBLog: Certified Virtual Cuts for a
Snapshot-Equivalent Replay of Live Databases”**, exactly as submitted to arXiv
for version 2 ([arXiv:2605.31475](https://arxiv.org/abs/2605.31475),
12 June 2026).

| File | Contents |
|---|---|
| `main.tex` | the paper |
| `refs.bib` | bibliography source |
| `main.bbl` | the bibliography as submitted (arXiv builds from the `.bbl`) |
| `figures/fig0{1..5}_*/fig0N.tex` | the five figures, TikZ sources included by `main.tex` |
| `dblog_virtual_cuts_v2.pdf` | arXiv's own build of this source, carrying the `arXiv:2605.31475v2 [cs.DB] 12 Jun 2026` margin stamp |

## Building

```bash
pdflatex main && bibtex main && pdflatex main && pdflatex main
```

No external image files are required — every figure is TikZ, drawn from the
shared palette and `tikzset` defined in the preamble of `main.tex`.

## Differences from the arXiv submission tarball

One omission: the submitted tarball carries the formal development a second
time, as an ancillary directory `anc/dblog_virtual_cuts_formal/` of 42 files.
It is left out here for two reasons — the development lives in
[`../formal/`](../formal/) in full, byte-identical to its archived Zenodo
deposit, and the ancillary copy is the **2.0** corpus (37 theories), the version
current when the paper was posted, whereas `../formal/` is 2.1.

## Licence

Creative Commons Attribution 4.0 International (CC BY 4.0), matching the arXiv
posting. See [`../LICENSES/CC-BY-4.0.txt`](../LICENSES/CC-BY-4.0.txt).
