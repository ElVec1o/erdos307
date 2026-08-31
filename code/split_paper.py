#!/usr/bin/env python3
"""Split the note into a core paper and a companion, from the single source erdos307.tex.

Rule 12 asks for dry, precise, minimal. A single document carrying the barrier, the closures, the
square sieve and the exploratory lenses is a record, not a paper. This script derives two documents
from the one source so they cannot drift (Rule 9):

  erdos307-core.tex       the results: rigidity, the bridge, the barrier, the Thabit rule, the
                          coprime relaxation and its link to #313, level finiteness, Lean, status,
                          prior work.
  erdos307-companion.tex  the exploratory and negative material: the heuristic model, the
                          function-field lens, the breeder form, the deviation ladder, the two
                          closures, the square sieve and its appendix.

Cross-references are handled by `xr`, not by rewriting prose: each document declares the other as an
external document under a prefix, and a reference crossing the boundary is emitted as
\\ref{X-label}, which prints the other document's own number. Both documents therefore have to be
built twice, and the build order is companion, core, companion, core.

Usage:  cd paper && python3 ../code/split_paper.py && \\
        pdflatex erdos307-companion && pdflatex erdos307-core && \\
        pdflatex erdos307-companion && pdflatex erdos307-core
"""
import re
from pathlib import Path

SRC = Path("erdos307.tex")

CORE_SECS = ["sec:intro", "sec:rigidity", "sec:bridge", "sec:barrier", "sec:frame",
             "sec:computations", "sec:lean", "sec:coprime", "sec:status", "sec:prior"]

def main():
    src = SRC.read_text()
    pre_end = src.index("\\begin{document}")
    preamble = src[:pre_end]
    body = src[pre_end:]

    abs_a = body.index("\\begin{abstract}")
    abs_b = body.index("\\end{abstract}") + len("\\end{abstract}")
    abstract = body[abs_a:abs_b]
    head = body[:abs_a]

    bib_a = body.index("\\begin{thebibliography}")
    bib_b = body.index("\\end{thebibliography}") + len("\\end{thebibliography}")
    bib = body[bib_a:bib_b]

    matter = body[abs_b:bib_a]
    app_at = matter.find("\\appendix")

    # split into (label, text) blocks at section boundaries
    marks = [(m.start(), m.group(1)) for m in
             re.finditer(r"\\section\{(?:[^{}]|\{[^{}]*\})*\}\\label\{([^}]*)\}", matter)]
    blocks = []
    for i, (pos, lab) in enumerate(marks):
        end = marks[i + 1][0] if i + 1 < len(marks) else len(matter)
        blocks.append((lab, matter[pos:end]))
    lead = matter[:marks[0][0]] if marks else matter

    core_blocks = [(l, t) for l, t in blocks if l in CORE_SECS]
    comp_blocks = [(l, t) for l, t in blocks if l not in CORE_SECS]

    core_labels = set()
    comp_labels = set()
    for l, t in core_blocks:
        core_labels |= set(re.findall(r"\\label\{([^}]*)\}", t))
    for l, t in comp_blocks:
        comp_labels |= set(re.findall(r"\\label\{([^}]*)\}", t))
    core_labels |= set(re.findall(r"\\label\{([^}]*)\}", lead))

    def retarget(text, foreign, prefix):
        """Point references that leave this document at the other one, via xr."""
        def sub(m):
            lab = m.group(1)
            return "\\ref{" + prefix + lab + "}" if lab in foreign else m.group(0)
        return re.sub(r"\\ref\{([^}]*)\}", sub, text)

    xr = "\\usepackage{xr}\n"

    core_body = lead + "".join(t for _, t in core_blocks)
    core_body = retarget(core_body, comp_labels, "C-")
    core = (preamble.replace("\\usepackage[expansion=false]{microtype}",
                             "\\usepackage[expansion=false]{microtype}\n" + xr)
            + "\\externaldocument[C-]{erdos307-companion}\n"
            + head + abstract + "\n" + core_body + "\n" + bib + "\n\\end{document}\n")
    core = core.replace("\\title{On the equation", "\\title{On the equation")

    comp_body = "".join(t for _, t in comp_blocks)
    # the appendix marker travels with the companion, which is where the appendix lives
    if app_at != -1 and "\\appendix" not in comp_body:
        comp_body = comp_body.replace("\\section{The square sieve: the argument",
                                      "\\appendix\n\\section{The square sieve: the argument")
    comp_body = retarget(comp_body, core_labels, "K-")
    comp_title = ("\\title{Companion to \\emph{On the equation $n''=n$ and a problem of "
                  "Erd\\H{o}s and Barbeau}:\\\\ explorations, closures and the square sieve}")
    comp_pre = preamble.replace("\\usepackage[expansion=false]{microtype}",
                                "\\usepackage[expansion=false]{microtype}\n" + xr)
    comp_pre = re.sub(r"\\title\{.*?\}\n", lambda _m: comp_title + "\n", comp_pre, flags=re.S)
    comp_abs = (r"""\begin{abstract}
This companion collects the exploratory and negative material of the note
\emph{On the equation $n''=n$ and a problem of Erd\H{o}s and Barbeau on products of
prime--reciprocal sums}, cited below as the core note. Nothing here is needed for the results
stated there; what is here is the record of which routes were tried and where each fails. It
contains the local heuristic model, the function--field lens locating the obstruction as
archimedean, the breeder form, the deviation ladder and the plus layer, two closures on the
existence route, and the square sieve at the mass--two wall together with the point at which its
analytic input does not close.
\end{abstract}""")
    comp = (comp_pre + "\\externaldocument[K-]{erdos307-core}\n"
            + head + comp_abs + "\n" + comp_body + "\n" + bib + "\n\\end{document}\n")

    Path("erdos307-core.tex").write_text(core)
    Path("erdos307-companion.tex").write_text(comp)
    print(f"core      : {len(core_blocks)} sections, {core_body.count(chr(10))} lines")
    print(f"companion : {len(comp_blocks)} sections, {comp_body.count(chr(10))} lines")

if __name__ == "__main__":
    main()
