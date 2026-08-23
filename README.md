# Structural Reduction of Two Twin-Prime Conjectures and Conditional Resolution under Hypothesis H

**Dacomb Bierton**  
ORCID: [0009-0007-7507-1398](https://orcid.org/0009-0007-7507-1398)  
23 August 2026

[![License: CC BY 4.0](https://img.shields.io/badge/License-CC%20BY%204.0-lightgrey.svg)](https://creativecommons.org/licenses/by/4.0/)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22063097.svg)](https://doi.org/10.5281/zenodo.22063097)

---

## Overview

This repository contains formal reductions of two conjectures introduced in earlier notes:

- **Twin-Prime Propagation Conjecture** — infinitely many consecutive pairs of lower twin primes produce a new lower twin via \(C = p + q + 1\).
- **Twin-Gap Existence Conjecture** — every sufficiently large lower twin prime \(t\) admits a productive even gap \(d = o(t)\).

Neither statement is proved in ZFC alone. Each implies the classical twin-prime conjecture. What *is* proved is that both are formal consequences of standard arithmetic hypotheses (Schinzel’s Hypothesis H for linear forms, and a uniform Bateman–Horn asymptotic).

All local lemmas (covering of \(D\), residues of lower twins, admissibility of the 6-tuple, consecutiveness of gap 6) are unconditional.

---

## Main result (short form)

**File:** [`Proof_of_Bierton_Conjectures.tex`](Proof_of_Bierton_Conjectures.tex) · [PDF](Proof_of_Bierton_Conjectures.pdf)

| Statement | Hypothesis | Conclusion |
|-----------|------------|------------|
| **Theorem A (Propagation)** | Hypothesis H | Infinitely many consecutive pairs in \(\mathcal{T}\) propagate via \(C = p+q+1\) |
| **Theorem B (Gap existence)** | Uniform Bateman–Horn for linear 4-tuples | Every large \(t\in\mathcal{T}\) has a productive gap of size \(O(t^\theta)\) for any fixed \(\theta>0\) |

The propagation statement is exactly Hypothesis H for the single admissible 6-tuple

\[
n,\quad n+2,\quad n+6,\quad n+8,\quad 2n+7,\quad 2n+9.
\]

---

## Longer development + machine certificate

**Files:**

| File | Description |
|------|-------------|
| [`On_Bierton_Twin_Conjectures.tex`](On_Bierton_Twin_Conjectures.tex) · [PDF](On_Bierton_Twin_Conjectures.pdf) | Full structural reduction, status table, corrected Hardy–Littlewood heuristic, explicit witnesses |
| [`prove_section6.py`](prove_section6.py) | Machine-checks every modular lemma, admissibility argument, logical implication, and computational claim in the longer note |

```bash
# Rebuild PDFs
pdflatex Proof_of_Bierton_Conjectures.tex
pdflatex On_Bierton_Twin_Conjectures.tex

# Run the certificate (default limit 100 000)
python prove_section6.py
python prove_section6.py --limit 200000
```

The script reports:

```
ALL SEVEN SECTION-6 CLAIMS CERTIFIED.
```

---

## Relation to the original notes

- [A Twin-Prime Propagation Conjecture](https://doi.org/10.5281/zenodo.22017371) (19 Aug 2026)
- [A Twin-Gap Existence Conjecture](https://doi.org/10.5281/zenodo.22058355) (22 Aug 2026)

This package supplies:

1. The covering argument that eliminates the \(D_n\) branch for all pairs after \((3,5)\).
2. The precise admissible 6-tuple that realises the propagation process.
3. The identification of both conjectures with standard hypotheses (Hypothesis H / uniform Bateman–Horn).

---

## Citation

If you use this work, please cite the original notes together with this reduction:

```
Bierton, D. (2026). A twin-prime propagation conjecture.
  Zenodo. https://doi.org/10.5281/zenodo.22017371

Bierton, D. (2026). A twin-gap existence conjecture.
  Zenodo. https://doi.org/10.5281/zenodo.22058355

Bierton, D. (2026). Structural reduction of two twin-prime
  conjectures and conditional resolution under Hypothesis H.
  Zenodo. https://doi.org/10.5281/zenodo.22063097
```

---

## License

This work is licensed under a [Creative Commons Attribution 4.0 International License](https://creativecommons.org/licenses/by/4.0/).
