# Wiley pack for the Journal of Graph Theory

The target journal is the Journal of Graph Theory. This directory is the Wiley pack Neil supplied, kept as a cleaned subset. It is not wired to the article. `paper/main.tex` remains an `amsart` file, and this directory is not read when that file is compiled.

The class is `USG.cls`, Wiley’s file of 2024/05/07 (v6.0). The author-guidelines PDF in this directory is the guide shipped with that pack. Journal of Graph Theory accepts a free-format submission, so the manuscript can go in as a PDF first. Convert to this class only when a production file is required.

## What is here

- `USG.cls`
- Wiley style and bibliography files the class loads when they sit beside it: `NJDnatbib.sty`, `NJDapacite.sty`, `lettersp.sty` (the pack names this `LETTERSP.STY`; both names are present), `mla.sty`, `wileyNJD-Chicago.bst`, `wileyNJD-Chicago-lastoo.bst`, `wileyNJD-Chicago.bib`
- `algorithm.sty`, `algorithmicx.sty`, `appendix.sty`, used by the sample
- `Optimal-Design-layout.tex`, the sample as supplied
- `Fonts/Stix/`, the OpenType files from the pack
- `images/`, the logos the class places on the title page, including `Wiley_logo.eps` and `allergy.eps`, which the class names with the `.eps` extension
- `Author-guidelines for LaTex Template_Wiley (2026).pdf`

The sample’s first line is `\documentclass[ASNA,twocolumn]{USG}`. In `USG.cls` the option `ASNA` selects the AMS reference style. The sample’s `\journal` line still reads AIChE Journal. That is the demonstration file from the pack, not a Journal of Graph Theory setting.

The class loads `stix2` from the TeX installation. The `fontspec` path that would use `Fonts/Stix/` is commented out in `USG.cls`.

## What was left out

Build products (`aux`, `log`, `bbl`, `blg`, `synctex`) and the compiled sample PDF are not included. Private copies of `amssymb.sty` and `natbib.sty` that came in the zip are omitted, so they do not override the copies in the TeX distribution. Large demonstration images that the class does not name (`box.eps`, `Research_badges.eps`, and the EPS originals of the social-network logos) are omitted. The logo PDFs are stored under the names `\includegraphics` looks up.

## No wrapper for the article

There is no `wiley-main.tex` that inputs `paper/main.tex`. That file is a complete document, with its own `\documentclass`. Feeding it to `USG` would nest the two classes. A Journal of Graph Theory copy has to be a separate file started from `Optimal-Design-layout.tex`.

The submission source is `paper/wiley-jgt.tex`, a complete `USG` document with the `ASNA` option, set in one column. It does not input `paper/main.tex`. The portable manuscript remains `paper/main.tex` in `amsart`.
