# Journal templates

The working manuscript stays `paper/main.tex`, in `amsart`. These notes record four publisher classes for a later submission copy. They do not change the article. The Journal of Graph Theory is the target. Neil’s Wiley pack is in `wiley-njd/`. The other three classes are not stored here: download the current bundle from the link below.

| Journal | Class | Bundle |
| --- | --- | --- |
| Discrete Mathematics (Elsevier) | `cas-sc` | [els-cas-templates](https://ctan.org/pkg/els-cas-templates) on CTAN |
| SIAM Journal on Discrete Mathematics | `siamart` | Standard macros on the [SIAM journal-authors page](https://epubs.siam.org/journal-authors) |
| Journal of Graph Theory (Wiley) | `USG` (Wiley NJD pack) | [`wiley-njd/`](wiley-njd/README.md) |
| Combinatorica (Springer Nature) | `sn-jnl` | [Springer Nature LaTeX author support](https://www.springernature.com/gp/authors/campaigns/latex-author-support) |

## Elsevier, Discrete Mathematics

The CTAN bundle `els-cas-templates` (class files `cas-sc.cls` and `cas-dc.cls`) is Elsevier’s updated CAS workflow. Use the single-column class:

```latex
\documentclass{cas-sc}
```

The sample file in the bundle is `cas-sc-template.tex`, with bibliography style `cas-model2-names.bst`. The same bundle contains the two-column class `cas-dc`. The [Discrete Mathematics guide for authors](https://www.sciencedirect.com/journal/discrete-mathematics/publish/guide-for-authors) asks for Elsevier’s LaTeX template and permits a double-column LaTeX submission; a Word file must stay single-column. Check that guide again before submission.

## SIAM, SIDMA

SIDMA uses the standard SIAM journal macros, not the online-only class `siamonline`. On the author page the standard class file is the dated file `siamart251216.cls`, the article skeleton is `ex_article.tex`, and the bibliography style is `siamplain.bst`. The class family is `siamart`; the date in the filename changes when SIAM ships a new macro set, so take the file named on that page rather than an older `siamart220329.cls`. A review copy uses the `review` option. The macros are optional at submission: SIAM will reformat a plain source after acceptance.

## Wiley, Journal of Graph Theory

The target journal is the Journal of Graph Theory. The class Neil supplied is `USG.cls` (Wiley, 2024/05/07, v6.0), kept with its sample and the author-guidelines PDF in [`wiley-njd/`](wiley-njd/README.md). That directory is the pack to use for a later JGT copy. The journal accepts a free-format submission, and a PDF can be sent first, so `paper/main.tex` stays in `amsart` until a production file is required.

## Springer Nature, Combinatorica

The Springer Nature journal template uses `sn-jnl.cls`. The December 2024 package is the zip linked from the author-support page, and the same template is the Springer Nature journal article on Overleaf. Springer Nature says the template may be used for a submission to any of its journals. It is a content-first class, not a substitute for the journal’s own limits.

Combinatorica’s instructions ask for a manuscript of at most 30 pages in 11-point LaTeX on US letter paper with 1-inch margins, submitted through EditFlow, and for a plain source of an accepted paper, without complicated macros or non-standard packages. Those instructions are on the [journal page](https://www.springer.com/journal/493). A submission prepared in `sn-jnl` still has to meet them.

## What this directory does not do

`paper/main.tex` is not converted to any of these classes. A submission copy should be a separate file, started from the publisher’s sample and filled from the present source, so that the portable article and its proofs stay in `amsart`.
