# Paper sources

Manuscript files from the exact source bundle of **“A Theoretical Study of
DBLog: Certified Virtual Cuts for a Snapshot-Equivalent Replay of Live
Databases”**, arXiv version 4
([arXiv:2605.31475v4](https://arxiv.org/abs/2605.31475v4), 13 August 2026).

| File | Contents |
|---|---|
| `main.tex` | the paper |
| `refs.bib` | bibliography source |
| `main.bbl` | the bibliography as submitted (arXiv builds from the `.bbl`) |
| `figures/fig0{1..5}_*/fig0N.tex` | the five figures, TikZ sources included by `main.tex` |
| `dblog_virtual_cuts_v4.pdf` | arXiv's own build of this source, carrying the `arXiv:2605.31475v4 [cs.DB] 13 Aug 2026` margin stamp |

## Building

```bash
pdflatex main && bibtex main && pdflatex main && pdflatex main
```

No external image files are required — every figure is TikZ, drawn from the
shared palette and `tikzset` defined in the preamble of `main.tex`.

## Differences from the arXiv submission tarball

The arXiv bundle also carries processing metadata (`00README.json`) and the
formal development as the 43-file ancillary directory
`anc/DBLog_Virtual_Cuts-2.1/`. They are not duplicated here: the development
lives in [`../formal/`](../formal/) and is byte-identical to both the v4
ancillary and the archived version 2.1 Zenodo deposit
([10.5281/zenodo.21732790](https://doi.org/10.5281/zenodo.21732790)).

## Licence

Creative Commons Attribution 4.0 International (CC BY 4.0), matching the arXiv
posting. See [`../LICENSES/CC-BY-4.0.txt`](../LICENSES/CC-BY-4.0.txt).
