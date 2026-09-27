# Research notes

## R1 — finite Freiman 3k−4 reduction

Current proof strategy is an independent Lean port of the mathematics, using the 2026 Isabelle AFP formalization `Freiman_3k_4` as a checked blueprint. The prior JSP-000216 WIP is used only as prior-work context and is not copied.

Normalize a finite integer set `A` affinely so that `min A = 0`, `max A = n`, and `gcd A = 1`. Let `k = |A|`.

Define interval holes `H0 = [0,n] \ A`. Split holes into:

- lower holes `L`: `x ∈ A+A`;
- upper holes `U`: `n+x ∈ A+A`;
- stable holes `S = H0 \ (L ∪ U)`.

The easy branch is:

`S = ∅  =>  A` is already covered by a unit-step progression of length at most `|A+A|-|A|+1`.

The key counting identity is

`|A+A| = 2|A|-1 + |L| + |U|`.

Thus the remaining finite theorem reduces to proving that small doubling together with `gcd A = 1` forbids stable holes.

For the hard branch set

- `B = A mod n`, so `|B| = |A|-1`;
- `C = B+B` in `Z/nZ`;
- `H = stabilizer(C)`;
- `D = B+H`.

The checked formal blueprint splits into:

1. `B ⊆ H`: a nontrivial proper period forces a divisor `d>1` of every element of `A`, contradicting `gcd A = 1`.
2. `B ⊄ H`: prove the stabilizer-count inequality

   `|H| ≤ 1 + |L∩U| + 2(|D|-|B|)`,

   combine with Kneser

   `2|D| - |H| ≤ |C|`,

   and the exact identity

   `|A+A| = |C| + |A| + |L∩U|`

   to obtain `|A+A| ≥ 3|A|-3`, contradicting `|A+A| ≤ 3|A|-4`.

### Immediate implementation order

1. hole definitions and `stableHoles = ∅` reduction;
2. finite cardinality identities;
3. affine/GCD normalization;
4. modulo-`n` shadow and exact counting identity;
5. Kneser port/use;
6. stabilizer-count inequality;
7. finite `3k−4` theorem;
8. return to the zero-density transfer needed for JSP-000216.
