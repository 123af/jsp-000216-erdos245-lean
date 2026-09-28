# JSP-000216 / Erdős Problem 245 — Lean submission record

## Mathematical result

- Problem: JSP-000216 / Erdős Problem #245.
- Original statement: for every infinite zero-density set `A ⊆ ℕ`,
  `limsup |(A + A) ∩ [1,N]| / |A ∩ [1,N]| ≥ 3`.
- Historical solution: G. A. Freiman, *Foundations of a structural theory of set addition* (1973), as recorded by the Justin Sun Prize catalog and Erdős Problems #245.
- This repository claims no mathematical-solver credit.

## Lean formalization

- Repository owner / formalization submitter: `123af`.
- AI assistance: OpenAI ChatGPT / GPT-5.6 Sol was used extensively during development. The repository owner is responsible for the submitted proof and verification record.
- Branch: `formalization/r1-holes`.
- Final theorem file: `Jsp000216/Erdos245Final.lean`.
- Main theorem: `Jsp000216.erdos245_limsupF`.
- Formal Conjectures RHS compatibility theorem: `Jsp000216.erdos245_formalConjectures_rhsF`.
- Axiom audit file: `Jsp000216/Audit.lean`.

The compatibility theorem states the current right-hand side of `google-deepmind/formal-conjectures` Erdős Problem 245 directly, omitting only that repository's external meta-level `answer(True)` wrapper.

## Reproduction

Toolchain and dependencies are pinned in `lean-toolchain` and `lakefile.lean`:

- Lean: `leanprover/lean4:v4.35.0-rc3`
- mathlib: `v4.35.0-rc3`
- `MiscYD`: `cd12c538d66f15a358a6904e7c847cd67661096f`

From a fresh checkout of the selected commit:

```bash
lake update
lake exe cache get
lake build
```

The root build imports `Jsp000216.Audit`, so the axiom audit is run as part of the normal build. It prints:

```text
'Jsp000216.erdos245_limsupF' depends on axioms: [propext, Classical.choice, Quot.sound]
'Jsp000216.erdos245_formalConjectures_rhsF' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The submitted proof contains no proof `sorry`, `admit`, user-added `axiom`, `native_decide`, `unsafe`, or added `opaque` proof escape in the PR diff.

## Statement correspondence

`Jsp000216.erdos245_formalConjectures_rhsF` quantifies over every `A : Set ℕ`, assumes `A.Infinite`, assumes the same real-cutoff zero-density `Tendsto` condition used by Formal Conjectures, and proves the same `EReal` limsup lower bound `3` for the truncated sumset/counting-function ratio.

Thus the formal theorem is universal in `A`; it is not the weaker existential statement asserting merely that one particular zero-density set can have a very large sumset.

## Related prior formalization work

- The Justin Sun Prize PR #4538 (`ddddddfsd/sunprize-lean-jsp-000216`) is acknowledged as related prior public progress. That submission explicitly records an incomplete proof with the finite Freiman inverse step and the zero-density transfer step left as external assumptions.
- Other JSP-000216 submissions located during review include existential Cantor-set constructions and a submission mapped to Erdős Problem #216 rather than Erdős Problem #245; these do not state the universal limsup theorem proved here.
- The Google DeepMind Formal Conjectures statement for Erdős Problem 245 was used as a statement reference.

This repository was developed as an independent proof repository. Related public work was consulted for problem mapping and gap identification; source code from the incomplete JSP-000216 progress repository was not copied into this development.

## Submission intent

This record is intended to support an external Lean-formalization submission to `TheJustinSunPrize/awards`. Mathematical credit remains with the historical solver(s); the requested contribution type is Lean formalization.
