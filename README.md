# Multiplicative rank in odd Collatz trajectories

From an odd positive integer, multiply by three, add one, and divide out all factors of two. These papers ask how many values along the resulting trajectory are multiplicatively independent.

* **Multiplicative rank of dense samples from odd Collatz segments.** Among $N$ distinct consecutive odd states, any fixed positive fraction contains at least $c(\log N)^{3/2}/\log\log N$ multiplicatively independent values, with $c$ depending only on that fraction. The starting value is unrestricted. If every step decreases, the full segment contains at least a constant times $\sqrt{N}$ independent values. [Paper](multiplicative-rank.pdf)
* **Twenty-one multiplicatively independent odd states in a nontrivial Collatz cycle.** Any nontrivial positive cycle would contain at least 21 multiplicatively independent odd values. To reproduce the numerical inequalities, run `python3 verification/cycle-certificate.py` from the repository root. [Paper](cycle-rank.pdf) · [Exact arithmetic checker](verification/cycle-certificate.py)

© 2026 maxilism. The papers and checker are licensed under [CC BY 4.0](LICENSE).
