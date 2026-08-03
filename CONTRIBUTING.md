# Contributing to the research notes

## Editing locally

The source of truth is the Markdown in this repository. Mathematics uses
LaTeX delimiters:

```markdown
Inline mathematics: \(T_e X\)

Display mathematics:

\[
T_eT_fX \longrightarrow T_{e\cdot f}X
\]
```

With MyST installed, start a live preview from the repository root:

```text
myst start
```

Build the static site with:

```text
myst build --html
```

## Status discipline

Every mathematical statement should be marked as one of:

- Established
- Derived
- Conjecture
- Candidate
- Question
- Rejected

Use a stable ID in `claims-ledger.md` for claims that affect more than one
page. Do not silently strengthen a theorem or weaken an assumption; record the
change in `work-log.md`.

## GitHub Pages

Every push to `main` builds and deploys the MyST site. In the repository's
GitHub settings, set **Pages → Build and deployment → Source** to
**GitHub Actions**.

