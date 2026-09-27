# Research notes

## R1 — finite Freiman 3k−4 theorem — COMPLETE

R1 is now kernel-checked end to end on the project branch.  The implementation is an independent Lean port of the mathematics, with the 2026 Isabelle AFP formalization and public additive-combinatorics formalizations used only as checked blueprints/API references.

For a normalized finite integer set `A ⊆ [0,p]` with `0,p ∈ A` and `gcd A = 1`, define interval holes and split them into lower, upper, and stable holes.  The easy branch shows that if the stable-hole set is empty then

`|[0,p]| ≤ |A+A| - |A| + 1`.

For the hard branch reduce modulo `p`, let `B = A mod p`, `C = B+B`, and `H = stabilizer(C)`.  The formal proof now contains the modular shadow/cardinality lemmas, trivial-stabilizer exclusion, gcd-one subgroup exclusion, saturation/coset bounds, refined integer lift, residue-fiber estimates, and the final contradiction

`stable hole  =>  |A+A| ≥ 3|A|-3`.

Hence under

`|A+A| ≤ 3|A|-4`

the stable-hole set is empty, giving the sharp normalized diameter bound

`p + 1 ≤ |A+A| - |A| + 1`.

Affine normalization was then formalized directly for `Finset ℤ`: translation by the least element and division by the gcd of all offsets preserves `|A|` and `|A+A|`, produces gcd one, and provides the normalized endpoints.  The resulting general finite theorem is:

`freiman_three_k_minus_fourF`:
for every finite integer set `A` with `3 ≤ |A|` and `|A+A| ≤ 3|A|-4`, there exist a start and positive common difference such that `A` is contained in an arithmetic progression with exactly

`|A+A| - |A| + 1`

displayed terms.

The theorem and all supporting modules are imported by `Jsp000216.lean`; CI #89 is green.

## R2 — zero-density transfer for Erdős #245 — ACTIVE

The remaining problem is the infinite transfer from a zero-density set `S ⊆ ℕ` to a finite prefix to which R1 applies.

Planned decomposition:

1. finite windows `window S N`, counts `countIn S N`, and increasing enumeration `enumerate S`;
2. exact enumeration/count identities and `window S N + window S N ⊆ window (S+S) (2N)`;
3. elementary density consequences, including arbitrarily large dyadic scales with `countIn S (2N) ≤ 4 countIn S N`;
4. prove a doubling-gap lemma: under an eventual sumset ratio `< 3`, arbitrarily far out there is an index `i` with `2*enumerate S i < enumerate S (i+1)`;
5. at such a gap, identify the finite prefix sumset exactly with the global sumset window, derive `|X+X| ≤ 3|X|-4`, invoke R1, and contradict zero density;
6. package the contradiction into the `limsup ≥ 3` statement of JSP-000216 / Erdős #245.

The main new structural obstacle is step 4.  A checked public blueprint obtains it from a bounded-doubling proper generalized-arithmetic-progression cover plus a finite-dimensional no-doubling-gap chain estimate.  We will first formalize the elementary window/density layers independently, then isolate the smallest GAP-cover package actually needed for this one implication.
