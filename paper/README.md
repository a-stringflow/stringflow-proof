# Paper

Main document: `main.tex`

Build:

```text
latexmk -pdf main.tex
```

or, with a standard TeX distribution:

```text
pdflatex main.tex
bibtex main
pdflatex main.tex
pdflatex main.tex
```

Structure:

```text
main.tex
sections/intro.tex
sections/framework.tex
sections/core.tex
sections/bridge.tex
sections/lean.tex
sections/appendix.tex
supplement_manual.tex
supplement/ch1_framework.tex ... supplement/ch33_submission_checklist.tex
refs.bib
```

Supplementary manual build:

```text
pdflatex supplement_manual.tex
pdflatex supplement_manual.tex
pdflatex supplement_manual.tex
```

Current compiled lengths: main document 43 pages; supplementary manual
102 pages.

Status discipline: the paper never claims Lean closure for
`unified_core_final_no_hge` or for
`FinalStatement.five_x_plus_one_diverges_at_7`; the final authority is
the Lean repository.

AI assistance: this work was assisted by AI tools (DeepSeek V4 Flash
(0731), Codex, and OpenCode Go) during exploration, proof drafting, and
Lean formalisation.  The disclosure is also recorded in the Lean
repository README.
