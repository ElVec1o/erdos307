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

CORE_ABSTRACT = r"""\begin{abstract}
Erd\H{o}s Problem~\#307 (Barbeau 1976; Erd\H{o}s--Graham 1980) asks whether there are finite sets
$P,Q$ of primes with $\bigl(\sum_{p\in P}\tfrac1p\bigr)\bigl(\sum_{q\in Q}\tfrac1q\bigr)=1$.
Writing $a=\prod P$ and $b=\prod Q$, a solution exists exactly when the arithmetic derivative has a
two--cycle $a'=b$, $b'=a$ with $a\neq b$. The reformulation is due to Ufnarovski and \AA hlander,
whose Conjecture~4 states \#307 in these terms; the identification of the two problems is recorded
in neither literature.

We prove a rigidity lemma, that each prime--reciprocal sum is already in lowest terms and hence
$P\cap Q=\varnothing$, and a barrier: any solution has $|P\cup Q|\ge60$ and
$\min(\prod P,\prod Q)>3.50\times10^{57}$, for both members and without hypotheses. This is the
first valid unconditional bound of its kind; the only prior candidate rests on an invalid step, for
which we give an explicit model. The barrier is uniform in the period, so it bounds the whole
Ufnarovski--\AA hlander cycle conjecture and not only its period--two case, and a parity dichotomy
shows that an all--odd cycle would need at least $1412$ primes.

Each level of the problem is finite and effectively decidable: for every pair of cardinalities there
are only finitely many solutions, so the infinitude of admissible supports above level $59$ bounds
the search space and not the solution set. At level $61$, the first open one,
$\prod(P\cup Q)<10^{567}$. No fixed--shape family of any growth rate can produce a solution, which
closes the Th\=abit--Euler programme that is the classical technique for problems of this kind.

For the coprime relaxation recorded with the problem we show that the solutions containing the
element $1$ are exactly the primary pseudoperfect numbers, so that case is equivalent to Erd\H{o}s
Problem~\#313; the $1$--free case needs $1414$ members and carries an obstruction \#313 does not.

The results are formalised in Lean~4, with every declaration depending only on the standard axioms
and no appeal to kernel--external evaluation. A companion note records the exploratory and negative
material, and one positive result: both Pythagorean layers have density zero on the squarefree
stratum, with a rate. The problem remains open.
\end{abstract}"""



CORE_SECS = ["sec:intro", "sec:rigidity", "sec:bridge", "sec:barrier", "sec:frame",
             "sec:computations", "sec:lean", "sec:coprime", "sec:status", "sec:prior"]

# The companion material divides by technique and by audience, so it is emitted as three
# documents rather than one. A single 107-page companion carrying the level-60 computation,
# the obstruction theorems and the analytic machinery is a record, not a paper.
COMP_A_SECS = ["sec:certificate", "sec:anatomy", "sec:breeder"]   # the level-60 computation
COMP_B_SECS = ["sec:ff", "sec:exclosure"]                          # why methods fail
COMP_C_SECS = ["sec:ladderplus", "sec:sqsieve", "app:sieve"]       # the analytic route

COMP_A_ABSTRACT = r"""\begin{abstract}
A solution of Erd\H{o}s Problem~\#307 is a two--cycle of the arithmetic derivative, and any solution
has $|P\cup Q|\ge60$. This note records the computation that decides the level--$60$ families.
The certificate of Proposition~\ref{prop:tailkill} empties $31{,}219$ of the $49{,}961$ admissible
bases by a Jacobi symbol, and trial division to $10^{6}$ leaves $7{,}713$. For the rest we give the
split sieve: writing a cycle on a family $S\cup M$ as $a=\prod(T\cup M)$, $b=\prod(S\setminus T)$,
the two cycle equations give $\prod T\mid\partial(\prod(S\setminus T))$ together with an identity
free of the tail. The divisibility is the identity read modulo $\prod T$, so it is a consequence
rather than a hypothesis, and by the anatomy lemma it is a congruence at each prime of $T$, costing
a factor $1/r$ each; $\prod_{p\in S}(1+1/p)$ subsets survive out of $2^{|S|}$. Neither statement
mentions the cofactor $A_S$, so the criterion reaches the families whose $A_S$ is composite and, the
tail being arbitrary, the pair sector, both of which the arity--one method cannot. Every level--$60$
base surviving the certificate is decided over all $T$ with $|T|\le6$: about $9\times10^{11}$ splits,
no factorisation, and no two--cycle. The heuristic model and a breeder form for certificate search
are included. The range $|T|\ge7$ is not decided and its price is stated.
\end{abstract}"""

COMP_B_ABSTRACT = r"""\begin{abstract}
This note records what cannot be used on Erd\H{o}s Problem~\#307, in the form of theorems rather
than of failed attempts. Over $\mathbb{F}_q[t]$ the derivative admits no two--cycle, by a degree
argument with no integer counterpart, and no place of $\mathbb{Q}$ carries that argument: the
archimedean absolute value is expanding on the relevant range, and each $p$--adic valuation, while
lowered at the primes of $n$, is raised elsewhere. By Ostrowski these are all the places, so the
function--field mechanism is unavailable as a classification statement and not as a failure of
ingenuity. Twisted two--cycles do exist over $\mathbb{Z}[i]$, $\mathbb{Z}[\sqrt{-2}]$,
$\mathbb{Z}[\omega]$ and $\mathbb{Z}[\sqrt2]$, so the obstruction is the orderability of
$\mathbb{Q}$. Two closures on the existence route are proved: no certificate distinguishes the two
branches, and no potential of the form $\log n+G(\sigma(n))$ can decrease around a cycle, for any
$G$, since the $G$--terms telescope and only the mass identity survives.
\end{abstract}"""

COMP_C_ABSTRACT = r"""\begin{abstract}
This note records the analytic route to Erd\H{o}s Problem~\#307 and how far it reaches. The
deviation ladder gives a second derivation of the barrier from the frontier side rather than from
the cycle. The main positive result is that both Pythagorean layers have density zero on the
squarefree stratum, with a rate. The square sieve at the mass--two wall is developed and does not
attain that rate: the loss is located in the character expansion, where the required uniformity in
the modulus is shown to be unavailable, and not in the arithmetic. Statements whose proofs rest on
inputs absent from the formalisation, Siegel--Walfisz and Hal\'asz among them, are labelled as such
and carry no machine check.
\end{abstract}"""

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

    # Four documents. Each is defined by its section labels, a prefix used for the cross-document
    # references that xr resolves, a file name, a title and an abstract.
    DOCS = [
        dict(key="K", secs=CORE_SECS,   file="erdos307-core",
             name="the core note",
             title=None, abstract=CORE_ABSTRACT),
        dict(key="A", secs=COMP_A_SECS, file="erdos307-computational",
             name="the computational companion",
             title=("\\title{The level--$60$ computation for Erd\\H{o}s Problem~\\#307:\\\\ "
                    "a certificate, a split sieve, and the pair sector}"),
             abstract=COMP_A_ABSTRACT),
        dict(key="B", secs=COMP_B_SECS, file="erdos307-obstructions",
             name="the obstructions companion",
             title=("\\title{Obstructions for Erd\\H{o}s Problem~\\#307:\\\\ "
                    "places, potentials, and two closures on the existence route}"),
             abstract=COMP_B_ABSTRACT),
        dict(key="C", secs=COMP_C_SECS, file="erdos307-analytic",
             name="the analytic companion",
             title=("\\title{The Pythagorean layers of Erd\\H{o}s Problem~\\#307:\\\\ "
                    "a density theorem and the square sieve at the mass--two wall}"),
             abstract=COMP_C_ABSTRACT),
    ]

    by_key = {}
    for d in DOCS:
        d["blocks"] = [(l, b) for l, b in blocks if l in d["secs"]]
        labs = set()
        for _, b in d["blocks"]:
            labs |= set(re.findall(r"\\label\{([^}]*)\}", b))
        if d["key"] == "K":
            labs |= set(re.findall(r"\\label\{([^}]*)\}", lead))
        d["labels"] = labs
        by_key[d["key"]] = d

    unassigned = [l for l, _ in blocks if not any(l in d["secs"] for d in DOCS)]
    if unassigned:
        raise SystemExit("section assigned to no document: " + ", ".join(unassigned))

    def retarget(text, me):
        """Point a reference that leaves this document at the document that holds it."""
        def sub(m):
            lab = m.group(1)
            for d in DOCS:
                if d is not me and lab in d["labels"]:
                    return "\\ref{" + d["key"] + "-" + lab + "}"
            return m.group(0)
        return re.sub(r"\\ref\{([^}]*)\}", sub, text)

    def name_foreign(text, me):
        """A pointer into another document must read as one, not as a section of this paper."""
        for d in DOCS:
            if d is me: continue
            for word in ("Section", "Sections"):
                text = re.sub(word + r"~\\ref\{" + d["key"] + r"-([^}]*)\}",
                              word + r"~\\ref{" + d["key"] + r"-\1} of " + d["name"], text)
        return text

    xr = "\\usepackage{xr}\n"
    written = []
    for d in DOCS:
        body = ("".join(b for _, b in d["blocks"]))
        if d["key"] == "K":
            body = lead + body
        # the appendix lives with the analytic companion
        if d["key"] == "C" and "\\appendix" not in body:
            body = body.replace("\\section{The minus--layer density theorem",
                                "\\appendix\n\\section{The square sieve: the argument")
        body = name_foreign(retarget(body, d), d)
        pre = preamble.replace("\\usepackage[expansion=false]{microtype}",
                               "\\usepackage[expansion=false]{microtype}\n" + xr)
        if d["title"]:
            pre = re.sub(r"\\title\{.*?\}\n", lambda _m: d["title"] + "\n", pre, flags=re.S)
        ext = "".join("\\externaldocument[" + e["key"] + "-]{" + e["file"] + "}\n"
                      for e in DOCS if e is not d)
        doc = pre + ext + head + d["abstract"] + "\n" + body + "\n" + bib + "\n\\end{document}\n"
        Path(d["file"] + ".tex").write_text(doc)
        written.append((d["file"], len(d["blocks"]), body.count(chr(10))))

    for f, ns, nl in written:
        print(f"{f:26s}: {ns} sections, {nl} lines")

if __name__ == "__main__":
    main()
