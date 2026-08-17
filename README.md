# A Theoretical Study of DBLog

### Certified Virtual Cuts for a Snapshot-Equivalent Replay of Live Databases

[![Paper (arXiv)](https://img.shields.io/badge/paper-arXiv%3A2605.31475-b31b1b)](https://arxiv.org/abs/2605.31475)
[![Artifact 2.1 DOI](https://img.shields.io/badge/artifact-10.5281%2Fzenodo.21732790-1682D4)](https://doi.org/10.5281/zenodo.21732790)

Sources for the paper **“A Theoretical Study of DBLog: Certified Virtual Cuts
for a Snapshot-Equivalent Replay of Live Databases”** (Andreas Andreakis, 2026)
and the machine-checked Isabelle/HOL development that accompanies it.

The paper supplies a correctness object for the DBLog change-data-capture
backfill mechanism — a *certified virtual cut* — and proves nine headline
theorems about it in Isabelle/HOL, `sorry`-free and axiom-free. Each result
holds under the premises its own statement names; deployment obligations and
the faithfulness of the source observation are hypotheses, not results. The
work verifies a model of the mechanism, not any implementation of it.

**Links** — [paper on arXiv](https://arxiv.org/abs/2605.31475) ·
[archived artifact (Zenodo)](https://doi.org/10.5281/zenodo.21732790) ·
[theorem index](docs/THEOREMS.md) ·
[provenance](docs/PROVENANCE.md) ·
[AGENTS.md](AGENTS.md) for AI tools

## Repository map

| Path | What it is |
|---|---|
| [`paper/`](paper/) | Manuscript sources from the exact arXiv v4 bundle (`main.tex`, `refs.bib`, `main.bbl`, TikZ figure sources), plus arXiv's built PDF. |
| [`formal/`](formal/) | The Isabelle/HOL session `DBLog_Virtual_Cuts` — **byte-identical to the archived Zenodo artifact**. Do not edit. |
| [`formal/README.md`](formal/README.md) | The artifact's own README: theory-by-theory contents, witnesses, release metadata. |
| [`docs/THEOREMS.md`](docs/THEOREMS.md) | The nine theorems: verbatim statements, premises, and per-theorem “what this does *not* say”. |
| [`docs/PROVENANCE.md`](docs/PROVENANCE.md) | Paper and artifact version history, DOIs. |
| [`AGENTS.md`](AGENTS.md) | Orientation file for AI assistants and automated readers. |

## The paper

- **arXiv v4:** [abs](https://arxiv.org/abs/2605.31475v4) · [PDF](https://arxiv.org/pdf/2605.31475v4) — 29 pages, 5 figures, cs.DB + cs.LO, CC BY 4.0.
- **In this repository:** [`paper/dblog_virtual_cuts_v4.pdf`](paper/dblog_virtual_cuts_v4.pdf) — arXiv's own build of v4, carrying its margin stamp.
- **Build it yourself** (figures are TikZ sources under `paper/figures/`; no external image files are needed):

  ```bash
  cd paper && pdflatex main && bibtex main && pdflatex main && pdflatex main
  ```

## The proofs

Requires [Isabelle2025-2](https://isabelle.in.tum.de/). The session depends only
on `HOL-Library` from the distribution — no Archive of Formal Proofs entry.

```bash
isabelle build -d formal DBLog_Virtual_Cuts
```

All 38 theories check `sorry`-free, and the session builds its own PDF
document, which requires a LaTeX toolchain. To check proofs without LaTeX,
remove the `document = pdf, document_output = "output"` options from
`formal/ROOT` first — session options take precedence over `-o document=false`
on the command line.

Nothing is axiomatized: there is no `axiomatization`, `typedecl` or `consts`
declaration, and the single `typedef` (the source coordinate type) is a
conservative extension over a provably non-empty set.

To check this tree against the archived deposit:

```bash
curl -sL https://zenodo.org/records/21732790/files/DBLog_Virtual_Cuts-2.1.tar.gz | tar xz
diff -r DBLog_Virtual_Cuts-2.1 formal   # no output means identical
```

## Versions and DOIs

| | Paper | Formal development |
|---|---|---|
| Current | [arXiv:2605.31475v4](https://arxiv.org/abs/2605.31475v4) (13 Aug 2026) | `2.1` — [10.5281/zenodo.21732790](https://doi.org/10.5281/zenodo.21732790), repo tag [`v2.1`](../../tree/v2.1) |
| Previous | [v3](https://arxiv.org/abs/2605.31475v3) (8 Aug 2026) · [v2](https://arxiv.org/abs/2605.31475v2) (12 Jun 2026) · [v1](https://arxiv.org/abs/2605.31475v1) (29 May 2026) | `2.0` — [10.5281/zenodo.20652511](https://doi.org/10.5281/zenodo.20652511), tag [`v2.0`](../../tree/v2.0) · `1.0` — [10.5281/zenodo.20389697](https://doi.org/10.5281/zenodo.20389697), tag [`v1.0`](../../tree/v1.0) |
| Always-latest DOI | — | [10.5281/zenodo.20389696](https://doi.org/10.5281/zenodo.20389696) (concept DOI) |

ArXiv v4 cites formal artifact 2.1 and carries `DBLog_Virtual_Cuts-2.1` as an
ancillary directory. That ancillary, the Zenodo 2.1 deposit, and this
repository's `formal/` tree are byte-identical. The concept DOI always resolves
to the newest version; version DOIs name exact bytes — cite the version DOI when
the bytes matter. Full history: [`docs/PROVENANCE.md`](docs/PROVENANCE.md).

## Citing

The paper:

```bibtex
@misc{andreakis2026dblog_virtual_cuts_paper,
  author = {Andreas Andreakis},
  title  = {A Theoretical Study of {DBLog}: Certified Virtual Cuts for a
            Snapshot-Equivalent Replay of Live Databases},
  year   = {2026},
  eprint = {2605.31475},
  archivePrefix = {arXiv},
  primaryClass  = {cs.DB},
  doi    = {10.48550/arXiv.2605.31475}
}
```

The formal development (cite the version you used):

```bibtex
@misc{andreakis2026dblog_virtual_cuts,
  author    = {Andreas Andreakis},
  title     = {{DBLog\_Virtual\_Cuts}: {Isabelle/HOL} formal development for
               ``{A Theoretical Study of DBLog}''},
  year      = {2026},
  publisher = {Zenodo},
  version   = {2.1},
  doi       = {10.5281/zenodo.21732790},
  note      = {Software, BSD 3-Clause License.}
}
```

GitHub's *Cite this repository* button reads [`CITATION.cff`](CITATION.cff).

## Background

- **DBLog: A Watermark Based Change-Data-Capture Framework** — Andreakis &
  Papapanagiotou, 2020. [arXiv:2010.12597](https://arxiv.org/abs/2010.12597).
  The original mechanism paper; this work is its theoretical follow-up.
- **DBLog: A Generic Change-Data-Capture Framework** — Netflix Tech Blog, 2019.
  [Post](https://netflixtechblog.com/dblog-a-generic-change-data-capture-framework-69351fb9099b).

## Licence

- **Paper text and figures** (`paper/`, `docs/`) — Creative Commons Attribution
  4.0 International (CC BY 4.0), matching the arXiv posting. See
  [`LICENSES/CC-BY-4.0.txt`](LICENSES/CC-BY-4.0.txt).
- **Isabelle/HOL development** (`formal/`) — BSD 3-Clause. See
  [`LICENSE`](LICENSE), a copy of `formal/LICENSE` as it ships inside the
  archived deposit.

## Author

**Andreas Andreakis** — independent researcher.
[ORCID 0009-0003-9025-9402](https://orcid.org/0009-0003-9025-9402)
