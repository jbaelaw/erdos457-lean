# Erdős Problem #457 in Lean 4: the sharp constant

Let `q(n, k)` be the least prime that does not divide `(n+1)(n+2)⋯(n+k)`
([Erdős problem #457](https://www.erdosproblems.com/457)). Tao showed in the problem's discussion
that `q(n, log n) > (1/2 − o(1)) log n · log log n / log log log n` for infinitely many `n`; the
probabilistic heuristic predicts the constant `1`. This repository proves and formalizes the
constant `1`:

```lean
theorem erdos_457_sharp (ε : ℝ) (hε : 0 < ε) :
    {n : ℕ | (1 - ε) * Real.log n * Real.log (Real.log n) /
        Real.log (Real.log (Real.log n)) ≤ q n (Real.log n)}.Infinite
```

together with the `limsup` form `limsup_ge_one` and the Formal Conjectures variant
`erdos_457_qnk`. The definition of `q` is copied verbatim from
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/ErdosProblems/457.lean`). All three targets depend only on `propext`,
`Classical.choice` and `Quot.sound`.

## Proof

See [paper/erdos457.pdf](paper/erdos457.pdf) (3 pages). With `L = lcm(1, …, M)`, the number
`n = tL − h − 1` is chosen with `t` an anchored difference of two indices `j` having equal
product-cell codes `(⌊[jL]_p / h⌋)_{M < p ≤ K}`, so that every prime `p ≤ K` divides a block of
`2h = o(log n)` consecutive integers after `n`. No prime number theorem is used: the code-entropy
bound needs `θ(K) ≤ (1 + δ) K` only at the scales actually used, and Chebyshev's elementary
`liminf θ(x)/x ≤ 1` (proved in `Erdos457/Chebyshev.lean` from Legendre's formula and
`θ(x) ≤ x log 4`) supplies infinitely many of them.

## Layout

| File | Content |
|---|---|
| `Challenge.lean` | the statements (with `sorry`), importing Mathlib only |
| `Solution.lean` | the same statements, proved |
| `Erdos457/Chebyshev.lean` | Mertens' upper bound and `θ(n) ≤ (1+δ) n` infinitely often |
| `Erdos457/ThetaK.lean` | transfer to the scales `K = ⌊A M⌋` |
| `Erdos457/Basic.lean` | `q`, the covering criterion and the fold |
| `Erdos457/Main.lean` | the construction and the main theorem |
| `Erdos457/Corollaries.lean` | the `limsup` form and `erdos_457_qnk` |
| `Erdos684Lean/` | the product-cell code, its entropy bound and the anchored pigeonhole |

## Build

Lean `v4.35.0-rc3`, Mathlib `b84a70d6a5ed793cc46184160f4d4188d8c825fb`.

```
lake exe cache get
lake build
```

`comparator.json` lists the targets for the Lean comparator.

## License

Apache-2.0.
