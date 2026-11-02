# GEN₃ certificate

Formal submission material for the one-triangle finite lemma and the two-triangle local lemma in `paper/main.tex`, `paper/wiley-jgt.tex`, and `paper/supplement.tex`.

`verify_gen3.py` will be added in this directory. It is a Python 3.10+ verifier that uses only the standard library and embeds the decision certificate. The command is:

```bash
python3 verify_gen3.py
```

The program checks the one-triangle search (169 labelled nodes, 52 leaves, largest order 17) and the two-triangle search (118 nodes across the four initial configurations). The mathematical statement, the reason a finite tree covers every order, and the audit protocol are in the article and in the supplement. This directory does not contain a reconstructed decision array.

Do not treat an absent `verify_gen3.py` as a printed certificate. When the program is deposited here, it is part of the submission.
