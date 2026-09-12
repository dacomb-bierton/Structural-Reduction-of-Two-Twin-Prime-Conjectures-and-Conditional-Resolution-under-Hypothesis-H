# Structural Reduction of Two Twin-Prime Conjectures and Conditional Resolution under Hypothesis H

**Dacomb Bierton**  
ORCID: [0009-0007-7507-1398](https://orcid.org/0009-0007-7507-1398)  
23 August 2026, revised 12 September 2026

[![License: CC BY 4.0](https://img.shields.io/badge/License-CC%20BY%204.0-lightgrey.svg)](https://creativecommons.org/licenses/by/4.0/)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22063097.svg)](https://doi.org/10.5281/zenodo.22063097)

---

## Overview

This repository contains the structural reduction of two conjectures introduced in earlier notes:

- **Twin-Prime Propagation Conjecture** (1.1) — infinitely many consecutive pairs of lower twin primes \(p_n < p_{n+1}\) produce a new lower twin via \(C_n = p_n + p_{n+1} + 1\).
- **Twin-Gap Existence Conjecture** (1.2) — every sufficiently large lower twin prime \(t\) admits a *productive* even gap \(d = o(t)\): \(t+d\) and \(2t+d+1\) are lower twins and \(d-1\) or \(d+1\) is prime.

Neither statement is proved in ZFC alone; each implies the classical twin-prime conjecture. What *is* proved is that both are formal consequences of standard arithmetic hypotheses (Schinzel's Hypothesis H for linear forms, and a uniform Bateman–Horn asymptotic), and every local lemma used along the way is unconditional.

---

## Results

**Files:** [`On_Bierton_Twin_Conjectures.tex`](On_Bierton_Twin_Conjectures.tex) · [PDF](On_Bierton_Twin_Conjectures.pdf)

| Statement | Hypothesis | Conclusion |
|-----------|------------|------------|
| **Theorem 4.4** | Hypothesis H | Infinitely many consecutive pairs in \(\mathcal{T}\) at gap 6 propagate via \(C = 2n+7\) |
| **Theorem 4.6** | Hypothesis H | *Every* gap \(g \equiv 0 \pmod 6\) occurs infinitely often as the gap of a propagating consecutive pair |
| **Proposition 4.9** | none | Gap-6 propagation never iterates: if \((n, n+6)\) propagates then \((C, C+6)\) does not; the gap after \(C\) is \(\equiv 0, 12, 18 \pmod{30}\) |
| **Theorem 5.5** | Uniform Bateman–Horn for linear 5-tuples | Every large \(t\in\mathcal{T}\) has \(\gg t^\theta/(\log t)^5\) productive gaps below \(t^\theta\), for any fixed \(0<\theta<1\) |

Supporting lemmas, all unconditional:

- \(D_n = p_n + p_{n+1} + 3\) is never a lower twin for \(n \ge 2\) (covering modulo 3), so Conjecture 1.1 reduces to \(C_n \in \mathcal{T}\).
- The 6-tuple \(n,\ n+2,\ n+6,\ n+8,\ 2n+7,\ 2n+9\) is admissible, with \(\nu(2),\nu(3),\nu(5),\nu(7) = 1,2,4,4\) and \(\nu(q)=6\) for \(q\ge 11\); every witness \(n>5\) satisfies \(n \equiv 11 \pmod{30}\).
- For every gap \(g \equiv 0 \pmod 6\) the analogous 6-tuple is admissible, and a Chinese-remainder class \(n \equiv r \pmod M\) forces every candidate lower twin strictly between \(n\) and \(n+g\) to be composite. This is what turns Hypothesis H into consecutiveness for arbitrary gaps.
- The 5-tuple \(d+t,\ d+t+2,\ d+2t+1,\ d+2t+3,\ d-1\) is admissible for **every** lower twin \(t>5\) (no exceptional set), and its singular series is bounded below by the Hardy–Littlewood quintuplet constant \(10.1318\ldots\).
- \(t=3\) has no productive gap; condition "\(d\pm1\) prime" is automatic for \(6 \le d \le 114\) and first fails at \(d=120\).

Quantitative statements:

- Bateman–Horn constant of the propagating 6-tuple: \(\mathfrak{S} = 51.8959\ldots = 3 \times\) (sextuplet constant). Predicted 51.7 witnesses below \(10^7\), 112.6 below \(4\cdot10^7\); observed 62 and 126.
- Heuristic constant for the number of propagating consecutive pairs: \(\kappa = 6\,(2C_2)^2 \prod_{\ell \ge 5}\bigl(1 + 8/(\ell-2)^3\bigr) = 14.7677\ldots\), derived from the residue distribution of consecutive lower twins. Predicted 2759.5 pairs with \(p_n \le 10^7\), observed 2827; predicted 7719.1 with \(p_n \le 4\cdot 10^7\), observed 7937.
- Conjecture 5.6: the least productive gap satisfies \(d_{\min}(t) \ll_\varepsilon (\log t)^{5+\varepsilon}\). Every lower twin \(5 \le t \le 10^6\) has one; the largest is \(d_{\min}(719351) = 63318\).

The revision also corrects three points of the first edition: Conjecture 1.2 is **not** known to be stronger than Conjecture 1.1 (neither implies the other; both follow from uniform Bateman–Horn and both imply the twin-prime conjecture); the Bateman–Horn formula carried a spurious factor \(\prod(\operatorname{lead} f_i)^{-1}\); and the admissibility lemma for Conjecture 1.2 needed no "thin exceptional set".

---

## Machine certificate

**File:** [`prove_section6.py`](prove_section6.py) — no dependencies beyond the Python 3 standard library.

```bash
# Rebuild the PDF
pdflatex On_Bierton_Twin_Conjectures.tex   # run three times for the table of contents and references

# Run the certificate (default: lower twins p_n <= 10^7, a few seconds)
python prove_section6.py
python prove_section6.py --limit 40000000
python prove_section6.py --quiet             # PASS/FAIL lines only
```

The script discharges the eight rows of the status table in Section 6 of the note. It

- exhausts every finite residue-class argument (Lemmas 2.1–2.3, 4.2, 4.3, 4.5, 4.7, 5.1–5.3, Proposition 4.9);
- decides admissibility of a \(k\)-tuple of primitive linear forms by checking primes \(q \le k\) exhaustively and using the pigeonhole principle for \(q > k\);
- executes the Chinese-remainder construction of Theorem 4.6 for gaps \(12 \le g \le 60\), verifies it, and exhibits witnesses in the class for \(g = 12\) (\(n = 29387, 108947, 7403117\));
- evaluates \(\mathfrak{S}\), \(\mathfrak{S}_{\min}\), \(2C_2\) and \(\kappa\) from their Euler products and compares the Bateman–Horn and \(\kappa\) predictions with the data (nothing is fitted);
- surveys least productive gaps for all lower twins up to \(10^6\) and builds explicit \(G\)-orbits.

The run ends with

```
ALL EIGHT SECTION-6 CLAIMS CERTIFIED.
```

---

## Relation to the original notes

- [A Twin-Prime Propagation Conjecture](https://doi.org/10.5281/zenodo.22017371) (19 Aug 2026)
- [A Twin-Gap Existence Conjecture](https://doi.org/10.5281/zenodo.22058355) (22 Aug 2026)

This package supplies:

1. The covering argument that eliminates the \(D_n\) branch for all pairs after \((3,5)\).
2. The admissible 6-tuple that realises the propagation process, and the family of 6-tuples (one per gap \(g \equiv 0 \pmod 6\)) with the forcing classes that make Hypothesis H produce consecutive pairs at every gap.
3. The identification of both conjectures with standard hypotheses (Hypothesis H / uniform Bateman–Horn), with explicit constants.

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
