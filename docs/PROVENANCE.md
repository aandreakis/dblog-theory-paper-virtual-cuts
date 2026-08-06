# Provenance: paper versions, artifact versions, and how they line up

Two objects evolve on separate clocks: the **paper** on arXiv and the **formal
development** on Zenodo. This file records both and explains the one place they
appear to disagree.

## Identifiers

| Object | Identifier |
|---|---|
| Paper | [arXiv:2605.31475](https://arxiv.org/abs/2605.31475) — cs.DB primary, cs.LO cross-list, CC BY 4.0 |
| Artifact, always-latest | [10.5281/zenodo.20389696](https://doi.org/10.5281/zenodo.20389696) (concept DOI) |
| Artifact, this repository | `formal/` — byte-identical to version 2.1 |
| Prior work | [arXiv:2010.12597](https://arxiv.org/abs/2010.12597) (2020 DBLog paper) |

## Paper versions

| Version | Date | Notes |
|---|---|---|
| v1 | 2026-05-29 | first posting |
| **v2** | **2026-06-12** | current version; 31 pages, 5 figures. The sources in `paper/` are this version. |

## Artifact versions

| Version | DOI | Date | Theories | What changed |
|---|---|---|---|---|
| 1.0 | [10.5281/zenodo.20389697](https://doi.org/10.5281/zenodo.20389697) | 2026-05-26 | 17 | first deposit; witnesses and counterexample fixtures were introduced by `axiomatization` |
| 2.0 | [10.5281/zenodo.20652511](https://doi.org/10.5281/zenodo.20652511) | 2026-06-12 | 37 | foundations rebuilt conservatively and **axiom-free** — every witness and fixture is now a constructed instance. **The nine headline theorem statements unchanged.** |
| **2.1** | [10.5281/zenodo.21732790](https://doi.org/10.5281/zenodo.21732790) | 2026-08-01 | 38 | fixture repair (below). **The nine headline theorem statements unchanged**; the repaired control's own statement is strictly strengthened. |

Each version is also a tag in this repository: [`v1.0`](../../../tree/v1.0),
[`v2.0`](../../../tree/v2.0), [`v2.1`](../../../tree/v2.1). The tags preserve
the layout each version was published with; the corpus moved under `formal/`
only when this repository became the paper's information hub.

## The 2.0 / 2.1 question

**The paper cites artifact version 2.0** (`10.5281/zenodo.20652511`) — printed
twice in the body and once in the bibliography of arXiv v2. **No version of the
paper references 2.1**, which was published on 2026-08-01, seven weeks after
arXiv v2 went up on 2026-06-12. Following the paper's DOI lands on 2.0; this
repository ships 2.1. That is not a discrepancy, and here is exactly what
differs.

An external review of the 2.0 artifact found that one negative control in the
Layer 3 fixtures was **vacuous**: the same-evidence control failed to
materialize its run, so the accessor-agreement comparison it advertised was
never actually reached. The control passed for the wrong reason. No theorem
statement was affected, and no proof depended on it.

Version 2.1 makes two changes and no others:

1. the control in `Layer3_Fixtures_Inst.thy` now materializes its run, so the
   comparison it advertises is genuinely exercised;
2. a new kernel-checked theory `Layer3_Defect_Regressions.thy` pins that
   reachability permanently, so the defect cannot silently return.

The nine headline theorem statements are identical across 2.0 and 2.1. A reader
comparing the paper's cited DOI with this repository will find version 2.1 and
should expect exactly this difference.

## Which identifier to cite

- **Concept DOI** `10.5281/zenodo.20389696` — when you mean "the formal
  development" and want the reader to land on the newest version.
- **Version DOI** — when the bytes matter: a build log, a review, a
  reproduction, a claim about a specific theory file.
- **This repository** — for reading and browsing. The Zenodo deposit remains
  the archival identifier; the repository is a convenience mirror plus context.

## Checking the mirror

```bash
curl -sL https://zenodo.org/records/21732790/files/DBLog_Virtual_Cuts-2.1.tar.gz | tar xz
diff -r DBLog_Virtual_Cuts-2.1 formal    # no output means identical
```

## Verification environment

Both 2.0 and 2.1 are checked with **Isabelle2025-2**
(`ISABELLE_IDENTIFIER=Isabelle2025-2`), using `HOL-Library` from the
distribution only — no Archive of Formal Proofs entry is required. The session
builds `sorry`-free and generates its own entry document, which needs a LaTeX
toolchain.
