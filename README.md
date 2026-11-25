# Multiplicative rank in odd Collatz trajectories

From an odd positive integer, multiply by three, add one, and divide out all factors of two. These papers ask how many values along the resulting trajectory are multiplicatively independent.

* **Multiplicative rank of dense samples from odd Collatz segments.** Among $N$ distinct consecutive odd states, any fixed positive fraction contains at least $c(\log N)^{3/2}/\log\log N$ multiplicatively independent values, with $c$ depending only on that fraction. The starting value is unrestricted. If every step decreases, the full segment contains at least a constant times $\sqrt{N}$ independent values. [Paper](multiplicative-rank.pdf)
* **Private prime factors in typical odd Collatz trajectories.** Choose an odd starting value uniformly in $[2^m,2^{m+1})$. For each fixed $0<c<1/\log_2(4/3)$, with probability tending to one as $m\to\infty$, every state through step $\lfloor cm\rfloor$ has a prime factor dividing no other state in the segment. All $\lfloor cm\rfloor+1$ states are therefore multiplicatively independent. [Paper](private-primes.pdf) · [Lean proof of the shared-divisor count](verification/SharedDivisorCount.lean)
* **Twenty-one multiplicatively independent odd states in a nontrivial Collatz cycle.** Any nontrivial positive cycle would contain at least 21 multiplicatively independent odd values. To reproduce the numerical inequalities, run `python3 verification/cycle-certificate.py` from the repository root. [Paper](cycle-rank.pdf) · [Exact arithmetic checker](verification/cycle-certificate.py)

To check the Lean proof, set `MATHLIB_PROJECT` to a built checkout of [mathlib at `1f414401f69059aa7eead47b53ee40bd38455eeb`](https://github.com/leanprover-community/mathlib4/tree/1f414401f69059aa7eead47b53ee40bd38455eeb), which uses Lean `4.35.0-rc4`. Run the following from this repository’s root.

```sh
proof="$PWD/verification/SharedDivisorCount.lean"
(cd "$MATHLIB_PROJECT" && lake env lean "$proof")
```

© 2026 maxilism. The papers and verification files are licensed under [CC BY 4.0](LICENSE).
