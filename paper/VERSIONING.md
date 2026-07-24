# Paper versioning convention

Every time the paper is bumped to a new version, the changed files are
snapshotted into the working `paper/` tree, with each file carrying the
version as a suffix. The folder layout uses `current/` for the latest
and `old/` for everything else, so the active version is always obvious
at a glance.

This file lives at `paper/VERSIONING.md` at the project root and
describes the working tree. The parallel
`share/v<N>/paper/versions/{current,old}/` inside frozen share bundles
uses the same convention but is a static snapshot.

## Layout

```
paper/
├── paper.tex            ← latest working copy (unsuffixed; used by orchestrator.py)
├── paper.pdf            ← latest compiled output
├── paper.md             ← latest markdown export
├── CHANGELOG.md         ← rolling changelog (all versions, newest first)
├── README.md, CITATION.cff, LICENSE     (unsuffixed; versioned only when they change)
├── orchestrator.py, reproduce/, figures/, OEIS/, digests/   (unsuffixed)
├── VERSIONING.md        ← this file
├── current/             ← the latest snapshot (currently v<X.Y>)
│   ├── paper_v<X.Y>.tex
│   ├── paper_v<X.Y>.pdf
│   ├── paper_v<X.Y>.md
│   └── CHANGELOG_v<X.Y>.md
└── old/                 ← every previous snapshot AND any migrated draft tree
    ├── v<prev>_snapshot/   (one subdir per older version)
    ├── ...
    └── (legacy DRAFT_*/, V*/ etc. if migrated from a pre-versioning tree)
```

`current/` always contains the latest version's files at the top level
(no nested `current/v<X.Y>/`). Under `old/`, version snapshots use the
naming `v<X.Y>_snapshot/` to distinguish them from any migrated
pre-versioning draft tree (`DRAFT_*/`, `V*/`, etc.).

## Rules

1. **`paper/<file>` is always the latest.** Reproduction scripts and
   `orchestrator.py` reference unsuffixed filenames; never put a suffix
   on the working copy.

2. **`paper/current/` always holds the latest snapshot, flat.** Files
   carry the version suffix (e.g. `paper_v<X.Y>.tex`). When a new
   version ships, the previous `current/` contents move into
   `paper/old/v<prev>_snapshot/` as a single move.

3. **Inside `current/` or `old/v<X.Y>_snapshot/`, every file that
   *changed* in that version is present with a `_v<X.Y>` suffix.**
   Files that didn't change in that version are not duplicated — look
   back through `old/` or to the unsuffixed working copies at the top
   of `paper/`.

4. **Files that always change with a paper bump:**
   - `paper.tex` → `paper_v<X.Y>.tex`
   - `paper.pdf` → `paper_v<X.Y>.pdf`
   - `paper.md`  → `paper_v<X.Y>.md`
   - `CHANGELOG.md` → `CHANGELOG_v<X.Y>.md`

5. **Files that occasionally change:** `README.md`, `CITATION.cff`,
   `figures/<name>.pdf`, individual `digests/<name>.txt`, `OEIS/<file>`.
   When one of these changes in version `v<X.Y>`, snapshot it into the
   relevant version folder with the `_v<X.Y>` suffix.

6. **Files that essentially never change:** `LICENSE`, `orchestrator.py`,
   the `reproduce/*.py` scripts. Same rule applies if they ever do
   change.

7. **Code under `code/`** has its own lifecycle and is NOT versioned in
   lockstep with the paper. If a code change is tied to a paper version,
   mention it in that version's `CHANGELOG_v<X.Y>.md` entry.

8. **Distinction inside `old/`:**
   - `old/v<X.Y>_snapshot/` — versioned snapshots produced by the bump
     procedure.
   - `old/DRAFT_*/`, `old/V*/`, etc. — migrated historical
     pre-versioning tree (if any).

## How to bump the version

Suppose `current/` is at v<prev> and you want to bump to v<next>, from
the project root:

```bash
cd paper
mkdir -p old/v<prev>_snapshot
mv current/* old/v<prev>_snapshot/
# (make edits to paper.tex, paper.pdf, paper.md, CHANGELOG.md)
cp paper.tex      current/paper_v<next>.tex
cp paper.pdf      current/paper_v<next>.pdf
cp paper.md       current/paper_v<next>.md
cp CHANGELOG.md   current/CHANGELOG_v<next>.md
# plus any other file that changed in this bump, e.g.:
#   cp README.md  current/README_v<next>.md
```

If you also need to ship the new version as a share bundle, mirror the
new state into `share/v<N+1>/paper/` and re-zip — but do NOT mutate any
already-shipped `share/v<K>/`, which are frozen.

## Current version

| Where | Version | Date |
|---|---|---|
| `paper/current/` | **v<X.Y>** | <YYYY-MM-DD> |
| `paper/old/v<X.Y>_snapshot/` | (one subdir per older snapshotted version) |
| `paper/old/DRAFT_*/, V*/` | (migrated pre-versioning tree, if any) |

Earlier paper versions (pre-`current/`) are NOT retrospectively
snapshotted as `v<X.Y>_snapshot/`; their full history lives in
`CHANGELOG.md` and inside any migrated `DRAFT_*/` or `V*/` directories
under `old/`. From the first version under this scheme onward, the
convention above is followed.
